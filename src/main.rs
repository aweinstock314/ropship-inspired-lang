#![warn(missing_docs)]
//! ropship-inspired-language

#[macro_use] extern crate lazy_static;
#[macro_use] extern crate pest_derive;
use pest::Parser;

/// The concrete syntax is parsed by pest, returning a concrete syntax tree containing span information for each grammar production
#[allow(missing_docs)]
pub mod concrete_syntax {
    #[derive(Parser)]
    #[grammar = "syntax.pest"]
    pub struct RILParser;
}

/// The AST is produced by traversing pest's CST, and is in a form convenient for typechecking and lowering into a stack-machine IR
pub mod abstract_syntax {
    /// The rust type of object language types
    #[derive(Debug, Clone)]
    pub enum TypeId {
        /// Pointers to some other type
        Pointer(Box<TypeId>),
        /// Register-sized words
        Word64,
    }

    impl TypeId {
        /// How many bytes instances of this type occupy
        pub fn size_in_bytes(&self) -> usize {
            match self {
                TypeId::Word64 => 8,
                TypeId::Pointer(_) => 8,
            }
        }
        /// Multiplier for additions to values of this type (so that `p += 1` works if `p` is a ptr)
        pub fn stride_to_increment(&self) -> usize {
            match self {
                TypeId::Word64 => 1,
                TypeId::Pointer(t) => t.size_in_bytes(),
            }
        }
    }

    /// Modifiers for compound assignments
    #[derive(Debug)]
    pub enum AssignmentModifier {
        /// `=`
        Normal,
        /// `+=`
        Add,
    }

    /// Expressions of the object language
    #[derive(Debug)]
    pub enum Expr {
        /// Literal integers
        Literal(String),
        /// Dereferencing another expression
        Deref(Box<Expr>),
        /// Variable lookups
        Var(String),
    }

    /// Statements of the object language
    #[allow(missing_docs)]
    #[derive(Debug)]
    pub enum Statement {
        /// Variable declarations
        LocalDecl { ident: String, ty: TypeId, initializer: Expr },
        /// "dotimes" loops
        DoTimes { amount: Expr, body: Vec<Statement> },
        /// Compound assignment with a modifier
        Assignment { lhs: String, modifier: AssignmentModifier, rhs: Expr },
        /// Return from a function
        Return { val: Expr },
    }

    /// Function definitions
    #[derive(Debug)]
    pub struct FunctionDef {
        /// The name of the function
        pub name: String,
        /// The function's argument names and types
        pub args: Vec<(String, TypeId)>,
        /// The return type of the function
        pub return_type: TypeId,
        /// The statements in the function's body
        pub body: Vec<Statement>,
    }

    /// Translation units
    #[derive(Debug)]
    pub struct TranslationUnit {
        /// The functions in a translation unit
        pub functions: Vec<FunctionDef>,
    }
}

/// Since the CST has both too much information (spans) and too little information (some shape information is knowable from the grammar, but not statically reflected), we convert it into an AST.
/// The module is a set of functions with the same recursion structure as the production rules, that recurse over the CST to convert it into an AST.
pub mod concrete_to_abstract_syntax;

/// Constants for and functions for manipulating x86 literals
pub mod x86_instructions {
    // for reg in {eax,ecx,edx,ebx,esp,ebp,esi,edi}; do rasm2 "add esp, $reg" | sed 's/\(..\)/\\x\1/g; s/^.*$/\&*b"\0",/'; done
    /// "pop $reg"
    const POP_EXX: [&[u8]; 8] = [&*b"\x58", &*b"\x59", &*b"\x5a", &*b"\x5b", &*b"\x5c", &*b"\x5d", &*b"\x5e", &*b"\x5f"];
    /// "imul $reg"
    const IMUL_EXX: [&[u8]; 8] = [&*b"\xf7\xe8", &*b"\xf7\xe9", &*b"\xf7\xea", &*b"\xf7\xeb", &*b"\xf7\xec", &*b"\xf7\xed", &*b"\xf7\xee", &*b"\xf7\xef"];
    /// "mov $reg, dword [eax]"
    const LOAD_EXX_EAX: [&[u8]; 8] = [&*b"\x8b\x00", &*b"\x8b\x08", &*b"\x8b\x10", &*b"\x8b\x18", &*b"\x8b\x20", &*b"\x8b\x28", &*b"\x8b\x30", &*b"\x8b\x38"];
    /// "mov dword [eax], $reg"
    const STORE_EAX_EXX: [&[u8]; 8] = [&*b"\x89\x00", &*b"\x89\x08", &*b"\x89\x10", &*b"\x89\x18", &*b"\x89\x20", &*b"\x89\x28", &*b"\x89\x30", &*b"\x89\x38"];
    include!("arith_gadgets.generated.rs");
    include!("cmov_gadgets.generated.rs");

    /// Kinds of gadgets, without specifying the last register
    #[allow(missing_docs)]
    #[derive(Debug, Clone, Copy)]
    pub enum GadgetKind { Pop, Imul, LoadEax, StoreEax, Add(X86Reg), Sub(X86Reg), Xor(X86Reg), Mov(X86Reg), Xchg(X86Reg), CmovCcEax(X86ConditionCode) }

    impl GadgetKind {
        /// All the GadgetKinds
        pub fn all_values() -> Vec<GadgetKind> {
            use GadgetKind::*;
            let mut ret = vec![Pop, Imul, LoadEax, StoreEax];
            for reg in &X86Reg::all_values() { ret.push(Add(*reg)); }
            for reg in &X86Reg::all_values() { ret.push(Sub(*reg)); }
            for reg in &X86Reg::all_values() { ret.push(Xor(*reg)); }
            for reg in &X86Reg::all_values() { ret.push(Mov(*reg)); }
            for reg in &X86Reg::all_values() { ret.push(Xchg(*reg)); }
            for cc in &X86ConditionCode::all_values() {
                if *cc != X86ConditionCode::RCX {
                    ret.push(CmovCcEax(*cc));
                }
            }
            ret
        }
        /// For a particular GadgetKind, the instructions that correspond to it, for each register
        pub fn gadgets_by_register(&self) -> [&'static [u8]; 8] {
            use GadgetKind::*; use X86ConditionCode::*;
            match *self {
                Pop => POP_EXX,
                Imul => IMUL_EXX,
                LoadEax => LOAD_EXX_EAX,
                StoreEax => STORE_EAX_EXX,
                Add(X86Reg::EAX) => ADD_EAX_EXX, Add(X86Reg::ECX) => ADD_ECX_EXX, Add(X86Reg::EDX) => ADD_EDX_EXX, Add(X86Reg::EBX) => ADD_EBX_EXX,
                Add(X86Reg::ESP) => ADD_ESP_EXX, Add(X86Reg::EBP) => ADD_EBP_EXX, Add(X86Reg::ESI) => ADD_ESI_EXX, Add(X86Reg::EDI) => ADD_EDI_EXX,
                Sub(X86Reg::EAX) => SUB_EAX_EXX, Sub(X86Reg::ECX) => SUB_ECX_EXX, Sub(X86Reg::EDX) => SUB_EDX_EXX, Sub(X86Reg::EBX) => SUB_EBX_EXX,
                Sub(X86Reg::ESP) => SUB_ESP_EXX, Sub(X86Reg::EBP) => SUB_EBP_EXX, Sub(X86Reg::ESI) => SUB_ESI_EXX, Sub(X86Reg::EDI) => SUB_EDI_EXX,
                Xor(X86Reg::EAX) => XOR_EAX_EXX, Xor(X86Reg::ECX) => XOR_ECX_EXX, Xor(X86Reg::EDX) => XOR_EDX_EXX, Xor(X86Reg::EBX) => XOR_EBX_EXX,
                Xor(X86Reg::ESP) => XOR_ESP_EXX, Xor(X86Reg::EBP) => XOR_EBP_EXX, Xor(X86Reg::ESI) => XOR_ESI_EXX, Xor(X86Reg::EDI) => XOR_EDI_EXX,
                Mov(X86Reg::EAX) => MOV_EAX_EXX, Mov(X86Reg::ECX) => MOV_ECX_EXX, Mov(X86Reg::EDX) => MOV_EDX_EXX, Mov(X86Reg::EBX) => MOV_EBX_EXX,
                Mov(X86Reg::ESP) => MOV_ESP_EXX, Mov(X86Reg::EBP) => MOV_EBP_EXX, Mov(X86Reg::ESI) => MOV_ESI_EXX, Mov(X86Reg::EDI) => MOV_EDI_EXX,
                Xchg(X86Reg::EAX) => XCHG_EAX_EXX, Xchg(X86Reg::ECX) => XCHG_ECX_EXX, Xchg(X86Reg::EDX) => XCHG_EDX_EXX, Xchg(X86Reg::EBX) => XCHG_EBX_EXX,
                Xchg(X86Reg::ESP) => XCHG_ESP_EXX, Xchg(X86Reg::EBP) => XCHG_EBP_EXX, Xchg(X86Reg::ESI) => XCHG_ESI_EXX, Xchg(X86Reg::EDI) => XCHG_EDI_EXX,
                CmovCcEax(Above) => CMOVA_EAX_EXX,
                CmovCcEax(AboveEq) => CMOVAE_EAX_EXX,
                CmovCcEax(Below) => CMOVB_EAX_EXX,
                CmovCcEax(BelowEq) => CMOVBE_EAX_EXX,
                CmovCcEax(Carry) => CMOVC_EAX_EXX,
                CmovCcEax(RCX) => panic!("sadly, cmovrcx doesn't exist to parallel jrcx"),
                CmovCcEax(Eq) => CMOVE_EAX_EXX,
                CmovCcEax(Greater) => CMOVG_EAX_EXX,
                CmovCcEax(GreaterEq) => CMOVGE_EAX_EXX,
                CmovCcEax(Less) => CMOVL_EAX_EXX,
                CmovCcEax(LessEq) => CMOVLE_EAX_EXX,
                CmovCcEax(NotEq,) => CMOVNE_EAX_EXX,
                CmovCcEax(NotOverflow) => CMOVNO_EAX_EXX,
                CmovCcEax(NotParity) => CMOVNP_EAX_EXX,
                CmovCcEax(NotSign) => CMOVNS_EAX_EXX,
                CmovCcEax(Overflow) => CMOVO_EAX_EXX,
                CmovCcEax(Parity) => CMOVP_EAX_EXX,
                CmovCcEax(Sign) => CMOVS_EAX_EXX,
            }
        }
    }

    lazy_static! {
        /// All the byte patterns for gadgets we care about
        pub static ref ALL_GADGETS: Vec<&'static [u8]> = {
            let mut ret = Vec::new();
            for gadget_kind in &GadgetKind::all_values() {
                for gadget in &gadget_kind.gadgets_by_register() {
                    ret.push(*gadget);
                }
            }
            ret
        };
    }

    /// The 8 x86 registers we use, in the order they are in the table
    #[allow(missing_docs)]
    #[repr(C)]
    #[derive(Debug, Clone, Copy)]
    pub enum X86Reg {
        EAX, ECX, EDX, EBX, ESP, EBP, ESI, EDI
    }

    impl X86Reg {
        /// All the X86Reg's, in order
        pub fn all_values() -> [X86Reg; 8] {
            use X86Reg::*;
            [EAX, ECX, EDX, EBX, ESP, EBP, ESI, EDI]
        }
    }

    /// All the X86 condition codes (used by jmp and cmov)
    #[allow(missing_docs)]
    #[repr(C)]
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum X86ConditionCode {
        Above, AboveEq, Below, BelowEq, Carry, RCX, Eq, Greater, GreaterEq, Less, LessEq, NotEq,
        NotOverflow, NotParity, NotSign, Overflow, Parity, Sign,
    }

    impl X86ConditionCode {
        /// All the X86ConditionCode's
        pub fn all_values() -> [X86ConditionCode; 18] {
            use X86ConditionCode::*;
            [Above, AboveEq, Below, BelowEq, Carry, RCX, Eq, Greater, GreaterEq, Less, LessEq, NotEq,
            NotOverflow, NotParity, NotSign, Overflow, Parity, Sign]
        }
    }
}

/// Given the executable sections of a binary and their virtual addresses, build a BTreeMap that indexes addresses of the gadgets we care
pub mod gadget_search {
    use std::collections::BTreeMap;
    use std::fmt;
    /// Find the gadgets with a naive O(n*m) search (we can take a dependency on an O(n+m) string search library after codegen is implemented)
    pub fn find_gadgets<'gadgets>(gadgets: &mut BTreeMap<&'gadgets [u8], Vec<usize>>, section: &[u8], section_offset: usize, goals: &[&'gadgets [u8]]) {
        for goal in goals.iter() {
            let n = goal.len();
            for (i, bytes) in section.windows(n).enumerate() {
                // TODO: fancier suffix-nop detection if we end up being too limited for gadgets?
                let acceptable_suffixes: &[&[u8]] = &[&*b"\xc3", &*b"\x90\xc3", &*b"\x90\x90\xc3"];
                if bytes == *goal {
                    //println!("{:?}", &section[i..i+n+5]);
                    if acceptable_suffixes.iter().any(|s| { &section[i+n..i+n+s.len()] == *s }) {
                        gadgets.entry(*goal).or_insert_with(|| vec![]).push(section_offset+i);
                    }
                }
            }
        }
    }
    /// Newtype wrapper for displaying the resulting BTreeMap as an aligned table, with `X86Reg`s on the x-axis, and `GadgetKind`s on the y-axis, with {0,1} in a cell indicating the {ab,pre}sence of the gadget
    pub struct ViewGadgetsAsChart<'a, 'b>(pub &'a BTreeMap<&'b [u8], Vec<usize>>);
    impl<'a, 'b> fmt::Display for ViewGadgetsAsChart<'a, 'b> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            use fmt::Write;
            use super::x86_instructions::{GadgetKind, X86Reg};
            let max_kind_width = GadgetKind::all_values().iter().fold(0, |w, k| w.max(format!("{:?}", k).len()));
            write!(f, "\n{:>w$}", "", w=max_kind_width+1)?;
            for reg in &X86Reg::all_values() {
                let regstr = format!("{:?}", reg);
                write!(f, "{:>width$}", regstr, width=regstr.len()+1)?;
            }
            write!(f, "\n")?;
            for kind in &GadgetKind::all_values() {
                let mut buf = String::new();
                let mut emit_row = false;
                write!(buf, "{:>w$}", format!("{:?}", kind), w=max_kind_width+1)?;
                for reg in &X86Reg::all_values() {
                    let regstr = format!("{:?}", reg);
                    let has_gadget = self.0.contains_key(kind.gadgets_by_register()[*reg as usize]);
                    write!(buf, "{:>width$}", has_gadget as u8, width=regstr.len()+1)?;
                    emit_row |= has_gadget;
                }
                write!(buf, "\n")?;
                if emit_row {
                    write!(f, "{}", buf)?;
                }
            }
            Ok(())
        }
    }
}

/// High-level interpreter with separate memory spaces for variables and pointers, for experimenting with language features and checking that they match the compiled outputs
pub mod high_level_eval;

/// "stack-ish" IR, in which IR-level jumps are conditional stack pivots in x86, but IR registers are directly x86 registers
pub mod stackish_machine {
    use std::collections::{BTreeMap, BTreeSet};
    use std::fmt::{self, Debug, Display, Formatter};
    use std::iter::FromIterator;
    use std::ops;
    use super::abstract_syntax::*;
    use super::x86_instructions::X86ConditionCode;

    /// Newtype for basic block indices
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct BasicBlockIndex(usize);
    impl ops::Add<usize> for BasicBlockIndex {
        type Output = BasicBlockIndex;
        fn add(self, rhs: usize) -> BasicBlockIndex {
            BasicBlockIndex(self.0 + rhs)
        }
    }

    /// InstructionAddresses are (which basic block, index into basic block)
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct InstructionAddress(BasicBlockIndex, usize);

    /// IR-level register, not yet mapped to concrete x86 registers
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub enum RegisterNumber {
        /// RSP
        InstructionPointer,
        /// RAX
        Accumulator,
        /// To be allocated by graph coloring
        GeneralPurpose(usize),
        /// To be allocated by graph coloring, with preference to x86 calling conventions
        ArgumentNumber(usize),
    }

    /// IR-level LValues
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Location {
        /// IR-level register
        Reg(RegisterNumber),
        /// IR-IP-relative memory offset
        RelMem(isize),
    }

    /// Kind of arithmetic instruction, subset of x86_instructions::GadgetKind
    #[allow(missing_docs)]
    #[derive(Debug, Clone, Copy)]
    pub enum ArithKind {
        Add, Sub, Mul, Xor, Swap, CMovLe
    }

    /// StackishOp<!> has no extra variants, and should map closely to x86 instructions
    /// StackishOp<HigherLevelOps> has extra variants that can be desugared to the initial ops
    /// instruction addresses are basic block indices at this level
    #[derive(Debug, Clone)]
    pub enum StackishOp<A> {
        /// ret
        Nop,
        /// pop resolved_addr
        Jump(BasicBlockIndex),
        /// CMOVcc rsp, resolved_addr
        ConditionalBranch(X86ConditionCode, BasicBlockIndex),
        /// pop $reg
        LoadImmediate(RegisterNumber, u64),
        /// $instr eax, $reg
        ArithAccumReg(ArithKind, RegisterNumber),
        /// mov eax, $reg
        LoadAccum(RegisterNumber),
        /// mov $reg, eax
        StoreAccum(RegisterNumber),
        /// int $0x80
        Syscall,
        /// mov $reg0, $reg1
        MovRegReg(RegisterNumber, RegisterNumber),
        /// hook for additional instructions
        Extra(A),
    }

    /// HigherLevelOps are more abstract, but are convenient to codegen
    /// they can be lowered to plain StackishOp's later
    #[derive(Debug, Clone)]
    pub enum HigherLevelOps {
        /// IR-IP-relative store
        StoreStartRelative(isize, RegisterNumber),
        /// IR-IP-relative load
        LoadStartRelative(RegisterNumber, isize),
    }

    /// Offset for allocating IR-IP-relative memory
    const ZONE_BETWEEN_VARS_AND_PROG: isize = 0x100;

    /// State for translating an AST program to the stack machine
    #[derive(Debug)]
    pub struct StackishProgram<Ops> {
        /// The list of ops at each basic block
        basic_blocks: BTreeMap<BasicBlockIndex, Vec<StackishOp<Ops>>>,
        /// The basic block we're currently emitting code for
        current_bb: BasicBlockIndex,
        /// IR-IP relative variable offsets
        vars_from_start: BTreeMap<String, isize>, // stack before the ropchain is probably overwriteable, so allocate vars backwards from there
        /// The types of AST-level variables
        type_ctx: BTreeMap<String, TypeId>,
        /// The next IR-IP-relative offset
        next_var_offset: isize,
        /// The next register to allocate (will be condensed by graph coloring)
        next_temp_register: usize,
    }

    impl<Ops: Debug> Display for StackishProgram<Ops> {
        fn fmt(&self, fmt: &mut Formatter) -> fmt::Result {
            writeln!(fmt, "StackishProgram {{")?;
            writeln!(fmt, "variable offsets:")?;
            for (k, v) in self.vars_from_start.iter() {
                writeln!(fmt, "  {:?}: {}", k, v)?;
            }
            writeln!(fmt, "basic blocks:")?;
            for (k, v) in self.basic_blocks.iter() {
                writeln!(fmt, "bb{}:", k.0)?;
                for op in v.iter() {
                    writeln!(fmt, "  {:?}", op)?;
                }
            }
            writeln!(fmt, "}}")?;
            Ok(())
        }
    }

    impl<Ops: Clone + Debug> StackishProgram<Ops> {
        /// Create a blank StackishProgram context
        pub fn new() -> StackishProgram<Ops> {
            StackishProgram {
                basic_blocks: BTreeMap::from_iter(vec![(BasicBlockIndex(0), vec![])]),
                current_bb: BasicBlockIndex(0),
                vars_from_start: BTreeMap::new(),
                type_ctx: BTreeMap::new(),
                next_var_offset: -ZONE_BETWEEN_VARS_AND_PROG,
                next_temp_register: 0,
            }
        }
        /// Push one op to the current basic block
        pub fn push_to_current_bb(&mut self, op: StackishOp<Ops>) {
            self.basic_blocks.get_mut(&self.current_bb).unwrap().push(op);
        }
        /// Push many ops to the current basic block
        pub fn extend_current_bb(&mut self, ops: &[StackishOp<Ops>]) {
            self.basic_blocks.get_mut(&self.current_bb).unwrap().extend_from_slice(ops);
        }
        /// Close the previous basic block and start a new one, returning the index of the new one
        pub fn start_basic_block(&mut self) -> BasicBlockIndex {
            self.current_bb.0 += 1;
            self.basic_blocks.insert(self.current_bb, vec![]);
            self.current_bb
        }
        /// Allocate a general purpose register
        pub fn get_next_gpr(&mut self) -> RegisterNumber {
            self.next_temp_register += 1;
            RegisterNumber::GeneralPurpose(self.next_temp_register)
        }
        /// Iterate over all the instructions emitted so far
        pub fn for_each_instruction<F: FnMut(InstructionAddress, &StackishOp<Ops>)>(&self, mut f: F) {
            for (bb, block) in &self.basic_blocks {
                for (i, inst) in block.iter().enumerate() {
                    f(InstructionAddress(*bb, i), inst);
                }
            }
        }
        /// Calculate the successor addresses of the given instruction, counting fallthrough, jumps, and conditional jumps
        pub fn successors(&self, node: InstructionAddress) -> BTreeSet<InstructionAddress> {
            let bb = &self.basic_blocks[&node.0];
            if node.1 == bb.len() - 1 {
                let mut fallthrough = vec![];
                if self.basic_blocks.contains_key(&(node.0+1)) {
                    fallthrough.push(InstructionAddress(node.0+1, 0));
                }
                match bb[node.1] {
                    StackishOp::Jump(next_bb) => BTreeSet::from_iter(vec![InstructionAddress(next_bb, 0)]),
                    StackishOp::ConditionalBranch(_, next_bb) => { fallthrough.push(InstructionAddress(next_bb, 0)); BTreeSet::from_iter(fallthrough) }, 
                    _ => { BTreeSet::from_iter(fallthrough) },
                }
            } else {
                match bb[node.1] {
                    StackishOp::Jump(_) | StackishOp::ConditionalBranch(_, _) => panic!("Jump/ConditionalBranch in the middle of basic block: {:?} {:?}", node, bb),
                    _ => BTreeSet::from_iter(vec![InstructionAddress(node.0, node.1+1)]),
                }
            }
        }
    }

    impl StackishProgram<HigherLevelOps> {
        /// Allocate a typed variable
        pub fn declare_value(&mut self, name: &str, ty: &TypeId, value: RegisterNumber) {
            self.next_var_offset -= ty.size_in_bytes() as isize;
            let addr = self.next_var_offset;
            self.vars_from_start.insert(name.into(), addr);
            self.type_ctx.insert(name.into(), ty.clone());
            self.push_to_current_bb(StackishOp::Extra(HigherLevelOps::StoreStartRelative(addr, value)));
        }
    }
    /// Translate an expression
    // TODO: should this take a register number (hence requiring translate_stmt to schedule all the registers)?
    pub fn translate_expr(prog: &mut StackishProgram<HigherLevelOps>, expr: &Expr) -> RegisterNumber {
        println!("translate expr {:?}: {:?}", expr, prog);
        match expr {
            Expr::Literal(s) => {
                let out = prog.get_next_gpr();
                prog.push_to_current_bb(StackishOp::LoadImmediate(out, s.parse::<u64>().unwrap()));
                out
            },
            Expr::Var(s) => {
                let out = prog.get_next_gpr();
                let offset = prog.vars_from_start[s];
                prog.push_to_current_bb(StackishOp::Extra(HigherLevelOps::LoadStartRelative(out, offset)));
                out
            }
            Expr::Deref(e) => {
                let out = prog.get_next_gpr();
                let tmp = translate_expr(prog, e);
                prog.extend_current_bb(&[
                    // NOTE: clobbers accumulator
                    StackishOp::LoadAccum(tmp),
                    //StackishOp::ArithAccumReg(ArithKind::Swap, out),
                    StackishOp::MovRegReg(out, RegisterNumber::Accumulator),
                ]);
                out
            },
        }
    }
    /// Translate a statement
    pub fn translate_stmt(prog: &mut StackishProgram<HigherLevelOps>, stmt: &Statement) {
        println!("translate stmt {:?}", stmt);
        match stmt {
            Statement::LocalDecl { ident, ty, initializer } => {
                let tmp = translate_expr(prog, initializer);
                prog.declare_value(ident, ty, tmp);
            },
            Statement::DoTimes { amount, body } => {
                // dotimes n { stmts } => tmp <- n; label0: stmts; tmp -= 1; jneq label0; label1:
                let reg_amount = translate_expr(prog, amount);
                let label0 = prog.start_basic_block();
                for inner_stmt in body {
                    translate_stmt(prog, inner_stmt); // TODO: I don't think this will handle forwards gotos
                }
                let one = translate_expr(prog, &Expr::Literal("1".into())); // TODO: check if this is already in some register/have a global "1" value lying around/codegen decrement
                prog.extend_current_bb(&[
                    StackishOp::ArithAccumReg(ArithKind::Swap, reg_amount),
                    StackishOp::ArithAccumReg(ArithKind::Sub, one), // sets flags for the test
                    StackishOp::ArithAccumReg(ArithKind::Swap, reg_amount), // xchg preserves flags
                    StackishOp::ConditionalBranch(X86ConditionCode::NotEq, label0),
                ]);
                let _label1 = prog.start_basic_block(); // TODO: pass around the bb instead of always working on the latest one, so that a "break" can target this
            }
            Statement::Assignment { lhs, modifier, rhs } => {
                let lhs_loc = prog.vars_from_start[lhs];
                let rhs_reg = translate_expr(prog, rhs);
                let ops = match modifier {
                    AssignmentModifier::Normal => vec![StackishOp::Extra(HigherLevelOps::StoreStartRelative(lhs_loc, rhs_reg))],
                    AssignmentModifier::Add => vec![
                        // TODO: clobbers accumulator, should translation have that liberty in general?
                        StackishOp::Extra(HigherLevelOps::LoadStartRelative(RegisterNumber::Accumulator, lhs_loc)),
                        StackishOp::ArithAccumReg(ArithKind::Add, rhs_reg),
                        StackishOp::Extra(HigherLevelOps::StoreStartRelative(lhs_loc, RegisterNumber::Accumulator)),
                        ],
                    };
                prog.extend_current_bb(&ops);
            }
            Statement::Return { val } => {
                let ret = translate_expr(prog, val);
                prog.push_to_current_bb(StackishOp::ArithAccumReg(ArithKind::Swap, ret));
            }
        }
    }

    /// Translate a function
    pub fn translate_function(prog: &mut StackishProgram<HigherLevelOps>, func: &FunctionDef) {
        for (i, (name, ty)) in func.args.iter().enumerate() {
            prog.declare_value(name, ty, RegisterNumber::ArgumentNumber(i));
        }
        for stmt in func.body.iter() {
            translate_stmt(prog, stmt);
        }
    }

    /// Def-use info, used for a variety of standard dataflow analysis passes
    #[derive(Debug)]
    pub struct DefUseInfo {
        /// Which `Location`s are defined by which instructions?
        defs: BTreeMap<InstructionAddress, BTreeSet<Location>>,
        /// Which `Locations` are used at which instructions?
        uses: BTreeMap<InstructionAddress, BTreeSet<Location>>,
    }

    /// Insert a value into the set associated with a key, creating the set if it does not exist
    pub fn mapset_insert<K: Ord, V: Ord>(map: &mut BTreeMap<K, BTreeSet<V>>, key: K, val: V) {
        map.entry(key).or_insert_with(|| BTreeSet::new()).insert(val);
    }

    /// Compute the def-use info from a stackish program
    pub fn compute_def_use(prog: &StackishProgram<HigherLevelOps>) -> DefUseInfo {
        let mut defuse = DefUseInfo { defs: BTreeMap::new(), uses: BTreeMap::new() };
        prog.for_each_instruction(|inst_addr, inst| {
            use StackishOp::*; use HigherLevelOps::*;
            // many instructions have assignment-like behavior, so deduplicate that fact
            let assignment = |defuse: &mut DefUseInfo, dst, src| {
                mapset_insert(&mut defuse.defs, inst_addr, dst);
                mapset_insert(&mut defuse.uses, inst_addr, src);
            };
            match inst {
                Nop => {},
                Jump(_) => {},
                ConditionalBranch(_, _) => {}, // TODO: do we need a def-use pseudoregister for flags?
                LoadImmediate(reg, _) => { mapset_insert(&mut defuse.defs, inst_addr, Location::Reg(*reg)); },
                ArithAccumReg(kind, reg) => {
                    use ArithKind::*;
                    assignment(&mut defuse, Location::Reg(RegisterNumber::Accumulator), Location::Reg(*reg));
                    mapset_insert(&mut defuse.uses, inst_addr, Location::Reg(RegisterNumber::Accumulator));
                    match kind {
                        Add | Sub | Mul | Xor | CMovLe => {
                            // only the common ones from above
                        }
                        Swap => {
                            // swap also writes to the rhs
                            mapset_insert(&mut defuse.defs, inst_addr, Location::Reg(*reg));
                        }
                    }
                },
                // TODO: do load and store need to also model the def-use-ness of stack-allocated vars?
                // if so, need an overapproximation of points-to for {Load,Store}Accum rhs's
                LoadAccum(reg) => { assignment(&mut defuse, Location::Reg(RegisterNumber::Accumulator), Location::Reg(*reg)); },
                StoreAccum(reg) => { assignment(&mut defuse, Location::Reg(*reg), Location::Reg(RegisterNumber::Accumulator)); },
                Syscall => {},
                MovRegReg(dst, src) => { assignment(&mut defuse, Location::Reg(*dst), Location::Reg(*src)); },
                Extra(StoreStartRelative(offset, reg)) => { assignment(&mut defuse, Location::RelMem(*offset), Location::Reg(*reg)); },
                Extra(LoadStartRelative(reg, offset)) => { assignment(&mut defuse, Location::Reg(*reg), Location::RelMem(*offset)); },
            }
        });
        defuse
    }
    /// A join-semilattice for dataflow analysis, together with the transfer function for an analysis pass
    // (TODO: these should maybe be two separate traits?)
    pub trait DataflowLattice {
        /// Context for the transfer function
        type Context;
        /// The index (usually program points) that the facts are associated with
        type Index;
        /// The type of the dataflow facts themselves
        type Fact: Eq+Clone;
        /// Bottom of the join-semilattice
        fn bottom() -> Self::Fact;
        /// Inplace "join-assigment" for the join-semilattice (saves memory in the common case of sets)
        fn join(x: &mut Self::Fact, y: &Self::Fact);
        /// Transfer function for the analysis pass
        fn transfer(ctx: &Self::Context, idx: &Self::Index, x: Self::Fact) -> Self::Fact;
    }

    /// Liveness analysis, used to construct a graph for register allocation through graph coloring
    pub struct LivenessAnalysis;
    impl DataflowLattice for LivenessAnalysis {
        type Context = DefUseInfo;
        type Index = InstructionAddress;
        type Fact = BTreeSet<Location>;
        fn bottom() -> Self::Fact { BTreeSet::new() }
        fn join(x: &mut Self::Fact, y: &Self::Fact) {
            /*let mut ret = Self::bottom();
            for (k, v) in x.iter() { ret.entry(k.clone()).or_insert_with(|| BTreeSet::new()).extend(v.clone()); }
            for (k, v) in y.iter() { ret.entry(k.clone()).or_insert_with(|| BTreeSet::new()).extend(v.clone()); }
            ret*/
            x.extend(y.iter().cloned())
        }
        fn transfer(ctx: &DefUseInfo, idx: &InstructionAddress, out_n: Self::Fact) -> Self::Fact {
            /*let use_n: Self::Fact = ctx.uses.get(idx).unwrap_or(&BTreeSet::new()).iter().cloned().map(|loc| (*idx, loc)).collect();
            let def_n: Self::Fact = ctx.defs.get(idx).unwrap_or(&BTreeSet::new()).iter().cloned().map(|loc| (*idx, loc)).collect();*/
            let use_n = ctx.uses.get(idx).cloned().unwrap_or_else(|| BTreeSet::new());
            let def_n = ctx.defs.get(idx).cloned().unwrap_or_else(|| BTreeSet::new());
            let out_minus_def: Self::Fact = out_n.difference(&def_n).cloned().collect();
            use_n.union(&out_minus_def).cloned().collect()
        }
    }

    /// Compute forwards dataflow analysis over a stackish program
    pub fn compute_forwards_dataflow<D: DataflowLattice<Index=InstructionAddress>>(prog: &StackishProgram<HigherLevelOps>, ctx: &D::Context) -> (BTreeMap<D::Index, D::Fact>, BTreeMap<D::Index, D::Fact>) where D::Fact: std::fmt::Debug {
        let mut old_in = BTreeMap::new();
        let mut old_out = BTreeMap::new();
        loop {
            //println!("old_in: {:?}\nold_out: {:?}", old_in, old_out);
            let mut new_in = old_in.clone();
            let mut new_out = old_out.clone();
            prog.for_each_instruction(|inst_addr, _| {
                let in_n: &mut D::Fact = new_in.entry(inst_addr).or_insert_with(|| D::bottom());
                D::join(in_n, &D::transfer(ctx, &inst_addr, old_out.get(&inst_addr).cloned().unwrap_or_else(|| D::bottom())));
                for succ in prog.successors(inst_addr) {
                    //let in_s = new_in.iter().filter_map(|(k, v)| if k == succ { Some((inst_addr, v)) } else { None }).collect();
                    let in_s = new_in.get(&succ).cloned().unwrap_or_else(|| D::bottom());
                    let out_n: &mut D::Fact = new_out.entry(inst_addr).or_insert_with(|| D::bottom());
                    D::join(out_n, &in_s);
                }
            });
            if new_in == old_in && new_out == old_out {
                return (new_in, new_out);
            }
            old_in = new_in;
            old_out = new_out;
        }
    }
}

/// Graph algorithms for graph-coloring register allocation
pub mod graph_algos;

#[allow(missing_docs)]
pub mod codegen {
    use super::stackish_machine::*;
    use super::x86_instructions::*;
    use std::collections::BTreeMap;
    pub struct CodegenCtx<'gadgets> {
        gadget_locs: BTreeMap<&'gadgets [u8], Vec<usize>>,
        regalloc: BTreeMap<RegisterNumber, X86Reg>,
    }
    impl<'gadgets> CodegenCtx<'gadgets> {
        fn gadget_available(&self, gadget: GadgetKind) -> bool {
            unimplemented!()
        }
        fn physreg_for_absreg(&self, absreg: RegisterNumber) -> X86Reg {
            unimplemented!()
        }
        fn do_codegen(&mut self, prog: &StackishProgram<HigherLevelOps>) {
            unimplemented!()
        }
    }
}

fn main() {
    use std::fs::File;
    use std::io::{Read, Write};

    let input_bytes = include_bytes!("../sum_input.ril");
    let input_string = String::from_utf8_lossy(&*input_bytes);
    let res = concrete_syntax::RILParser::parse(concrete_syntax::Rule::function, &input_string);
    println!("{:?}\n", res);
    if let Ok(mut pairs) = res { 
        let f = concrete_to_abstract_syntax::functiondef(pairs.next().unwrap());
        println!("{:#?}", f);
        {
            use high_level_eval::*;
            let mut state = HighLevelState::new();
            let data: &[u64] = &[0,1,2,3,4,5,6,7,8,9];
            let data64: &[u8] = unsafe { ::std::slice::from_raw_parts(data.as_ptr() as _, data.len() * ::std::mem::size_of::<u64>() / ::std::mem::size_of::<u8>()) };
            let p = state.allocate_data(&data64);
            let ret = eval_function(&mut state, &f, &[p, data.len() as _]);
            println!("eval returned {:?}", ret);
        }
        {
            use stackish_machine::*;
            use petgraph::{Graph, dot::{Dot, Config}, visit::NodeIndexable};
            let mut prog = StackishProgram::new();
            translate_function(&mut prog, &f);
            println!("stackish program: {}", prog);
            /*println!("Successors:");
            prog.for_each_instruction(|inst_addr, inst| {
                println!("\t{:?} {:?} {:?}", inst_addr, inst, prog.successors(inst_addr));
            });*/
            let defuse = compute_def_use(&prog);
            //println!("defuse info: {:?}", defuse);
            let (live_in, live_out) = compute_forwards_dataflow::<LivenessAnalysis>(&prog, &defuse);
            println!("live_in:");
            for item in &live_in {
                println!("\t{:?}", item);
            }
            println!("live_out:");
            for item in &live_out {
                println!("\t{:?}", item);
            }

            let mut regalloc_graph = Graph::<_, ()>::new();
            let mut regalloc_keys = BTreeMap::new();
            for (_, v) in &live_in {
                for x in v {
                    if let Location::Reg(y) = x {
                        if !regalloc_keys.contains_key(y) {
                            let node = regalloc_graph.add_node(y);
                            regalloc_keys.insert(y, node);
                        }
                    }
                }
            }
            for (_, v) in &live_in {
                for x in v {
                    if let Location::Reg(x0) = x {
                        for y in v {
                            if let Location::Reg(y0) = y {
                                let node_x = regalloc_keys[x0];
                                let node_y = regalloc_keys[y0];
                                if node_x != node_y {
                                    regalloc_graph.update_edge(node_x, node_y, ());
                                }
                            }
                        }
                    }
                }
            }
            let mut graphviz = format!("{:?}", Dot::with_config(&regalloc_graph, &[Config::EdgeNoLabel]));
            let coloring = graph_algos::brute_force_colors(&regalloc_graph, 4);
            println!("coloring: {:?}", coloring);
            if let Some(coloring) = coloring {
                let mut replacement = "digraph {\n".to_string();
                for i in 0..regalloc_graph.node_bound() {
                    static COLORS: &[&str] = &["red", "green", "blue", "purple"];
                    replacement += &format!("    {} [ fillcolor = {}, style = filled ]\n", i, COLORS[coloring[i].0]);
                }
                graphviz = graphviz.replace("digraph {", &replacement);
            }
            let mut graphviz_file = File::create("reg_alloc.dot").unwrap();
            graphviz_file.write(graphviz.as_bytes()).unwrap();
            println!("Wrote reg_alloc.dot");
        }
    }

    use std::collections::BTreeMap;
    for path in &["/bin/ls", "/bin/bash", "/lib/x86_64-linux-gnu/libc.so.6"] {
        let mut file = File::open(path).unwrap();
        let mut bytes = Vec::new();
        file.read_to_end(&mut bytes).unwrap();
        let elf = goblin::elf::Elf::parse(&bytes).unwrap();
        let mut gadgets = BTreeMap::new();
        for phdr in &elf.program_headers {
            if phdr.is_executable() {
                let range = phdr.file_range();
                gadget_search::find_gadgets(&mut gadgets, &bytes[range.clone()], range.start, &x86_instructions::ALL_GADGETS);
            }
        }
        println!("ELF-aware gadgets for {}: {}", path, gadget_search::ViewGadgetsAsChart(&gadgets));
        #[cfg(feature="also_check_raw_gadgets")] {
            let mut raw_gadgets = BTreeMap::new();
            gadget_search::find_gadgets(&mut raw_gadgets, &bytes, 0, &x86_instructions::ALL_GADGETS);
            if raw_gadgets != gadgets {
                println!("ELF-unaware gadgets for {}: {}", path, gadget_search::ViewGadgetsAsChart(&raw_gadgets));
            }
        }
    }
}
