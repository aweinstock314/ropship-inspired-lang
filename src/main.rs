#[macro_use] extern crate lazy_static;
#[macro_use] extern crate pest_derive;
use pest::Parser;

pub mod concrete_syntax {
    #[derive(Parser)]
    #[grammar = "syntax.pest"]
    pub struct RILParser;
}

pub mod abstract_syntax {
    #[derive(Debug, Clone)]
    pub enum TypeId {
        Pointer(Box<TypeId>),
        Word64,
    }

    impl TypeId {
        pub fn size_in_bytes(&self) -> usize {
            match self {
                TypeId::Word64 => 8,
                TypeId::Pointer(_) => 8,
            }
        }
        pub fn stride_to_increment(&self) -> usize {
            match self {
                TypeId::Word64 => 1,
                TypeId::Pointer(t) => t.size_in_bytes(),
            }
        }
    }

    #[derive(Debug)]
    pub enum AssignmentModifier {
        Normal,
        Add,
    }

    #[derive(Debug)]
    pub enum Expr {
        Literal(String),
        Deref(Box<Expr>),
        Var(String),
    }

    #[derive(Debug)]
    pub enum Statement {
        LocalDecl { ident: String, ty: TypeId, initializer: Expr },
        DoTimes { amount: Expr, body: Vec<Statement> },
        Assignment { lhs: String, modifier: AssignmentModifier, rhs: Expr },
        Return { val: Expr },
    }

    #[derive(Debug)]
    pub struct FunctionDef {
        pub name: String,
        pub args: Vec<(String, TypeId)>,
        pub return_type: TypeId,
        pub body: Vec<Statement>,
    }

    #[derive(Debug)]
    pub struct TranslationUnit {
        pub functions: Vec<FunctionDef>,
    }
}

pub mod concrete_to_abstract_syntax;

pub mod x86_instructions {
    // for reg in {eax,ecx,edx,ebx,esp,ebp,esi,edi}; do rasm2 "add esp, $reg" | sed 's/\(..\)/\\x\1/g; s/^.*$/\&*b"\0",/'; done
    const ADD_ESP_EXX: [&[u8]; 8] = [&*b"\x01\xc4", &*b"\x01\xcc", &*b"\x01\xd4", &*b"\x01\xdc", &*b"\x01\xe4", &*b"\x01\xec", &*b"\x01\xf4", &*b"\x01\xfc"];
    const SUB_ESP_EXX: [&[u8]; 8] = [&*b"\x29\xc4", &*b"\x29\xcc", &*b"\x29\xd4", &*b"\x29\xdc", &*b"\x29\xe4", &*b"\x29\xec", &*b"\x29\xf4", &*b"\x29\xfc"];
    const POP_EXX: [&[u8]; 8] = [&*b"\x58", &*b"\x59", &*b"\x5a", &*b"\x5b", &*b"\x5c", &*b"\x5d", &*b"\x5e", &*b"\x5f"];
    const ADD_EAX_EXX: [&[u8]; 8] = [&*b"\x01\xc0", &*b"\x01\xc8", &*b"\x01\xd0", &*b"\x01\xd8", &*b"\x01\xe0", &*b"\x01\xe8", &*b"\x01\xf0", &*b"\x01\xf8"];
    const SUB_EAX_EXX: [&[u8]; 8] = [&*b"\x29\xc0", &*b"\x29\xc8", &*b"\x29\xd0", &*b"\x29\xd8", &*b"\x29\xe0", &*b"\x29\xe8", &*b"\x29\xf0", &*b"\x29\xf8"];
    const XOR_EAX_EXX: [&[u8]; 8] = [&*b"\x31\xc0", &*b"\x31\xc8", &*b"\x31\xd0", &*b"\x31\xd8", &*b"\x31\xe0", &*b"\x31\xe8", &*b"\x31\xf0", &*b"\x31\xf8"];
    const XCHG_EAX_EXX: [&[u8]; 8] = [&*b"\x90", &*b"\x91", &*b"\x92", &*b"\x93", &*b"\x94", &*b"\x95", &*b"\x96", &*b"\x97"];
    const CMOVLE_EAX_EXX: [&[u8]; 8] = [&*b"\x0f\x4e\xc0", &*b"\x0f\x4e\xc1", &*b"\x0f\x4e\xc2", &*b"\x0f\x4e\xc3", &*b"\x0f\x4e\xc4", &*b"\x0f\x4e\xc5", &*b"\x0f\x4e\xc6", &*b"\x0f\x4e\xc7"];
    const IMUL_EXX: [&[u8]; 8] = [&*b"\xf7\xe8", &*b"\xf7\xe9", &*b"\xf7\xea", &*b"\xf7\xeb", &*b"\xf7\xec", &*b"\xf7\xed", &*b"\xf7\xee", &*b"\xf7\xef"];
    const LOAD_EXX_EAX: [&[u8]; 8] = [&*b"\x8b\x00", &*b"\x8b\x08", &*b"\x8b\x10", &*b"\x8b\x18", &*b"\x8b\x20", &*b"\x8b\x28", &*b"\x8b\x30", &*b"\x8b\x38"]; // "mov $reg, dword [eax]"
    const STORE_EAX_EXX: [&[u8]; 8] = [&*b"\x89\x00", &*b"\x89\x08", &*b"\x89\x10", &*b"\x89\x18", &*b"\x89\x20", &*b"\x89\x28", &*b"\x89\x30", &*b"\x89\x38"]; // "mov dword [eax], $reg"

    #[repr(C)]
    #[derive(Debug, Clone, Copy)]
    pub enum GadgetKind { AddEsp, SubEsp, Pop, AddEax, SubEax, XorEax, XchgEax, CmovleEax, Imul, LoadEax, StoreEax }

    impl GadgetKind {
        pub fn all_values() -> [GadgetKind; 11] {
            use GadgetKind::*;
            [AddEsp, SubEsp, Pop, AddEax, SubEax, XorEax, XchgEax, CmovleEax, Imul, LoadEax, StoreEax]
        }
        pub fn gadgets_by_register(&self) -> [&'static [u8]; 8] {
            [ADD_ESP_EXX, SUB_ESP_EXX, POP_EXX, ADD_EAX_EXX, SUB_EAX_EXX, XOR_EAX_EXX, XCHG_EAX_EXX, CMOVLE_EAX_EXX, IMUL_EXX, LOAD_EXX_EAX, STORE_EAX_EXX][*self as usize]
        }
    }

    lazy_static! {
        pub static ref ALL_GADGETS: Vec<&'static [u8]> = {
            let mut ret = Vec::new();
            for gadget_set in &[ADD_ESP_EXX, SUB_ESP_EXX, POP_EXX, ADD_EAX_EXX, SUB_EAX_EXX, XOR_EAX_EXX, XCHG_EAX_EXX, CMOVLE_EAX_EXX, IMUL_EXX, LOAD_EXX_EAX, STORE_EAX_EXX] {
                for gadget in gadget_set {
                    ret.push(*gadget);
                }
            }
            ret
        };
    }

    #[repr(C)]
    #[derive(Debug, Clone, Copy)]
    pub enum X86Reg {
        EAX, ECX, EDX, EBX, ESP, EBP, ESI, EDI
    }

    impl X86Reg {
        pub fn all_values() -> [X86Reg; 8] {
            use X86Reg::*;
            [EAX, ECX, EDX, EBX, ESP, EBP, ESI, EDI]
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub enum X86ConditionCode {
        Above, AboveEq, Below, BelowEq, Carry, RCX, Eq, Greater, GreaterEq, Less, LessEq, NotEq,
        NotOverflow, NotParity, NotSign, Overflow, Parity, Sign,
    }
}
pub mod gadget_search {
    use std::collections::BTreeMap;
    use std::fmt;
    pub fn find_gadgets<'gadgets>(binary: &[u8], goals: &[&'gadgets [u8]]) -> BTreeMap<&'gadgets [u8], Vec<usize>> {
        let mut ret = BTreeMap::new();
        for goal in goals.iter() {
            for (i, bytes) in binary.windows(goal.len()).enumerate() {
                if bytes == *goal && binary[i+goal.len()] == 0xc3 {
                    ret.entry(*goal).or_insert_with(|| vec![]).push(i);
                }
            }
        }
        ret
    }
    pub struct ViewGadgetsAsChart<'a, 'b>(pub &'a BTreeMap<&'b [u8], Vec<usize>>);
    impl<'a, 'b> fmt::Display for ViewGadgetsAsChart<'a, 'b> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            use super::x86_instructions::{GadgetKind, X86Reg};
            let max_kind_width = GadgetKind::all_values().iter().fold(0, |w, k| w.max(format!("{:?}", k).len()));
            write!(f, "\n{:>w$}", "", w=max_kind_width+1)?;
            for reg in &X86Reg::all_values() {
                let regstr = format!("{:?}", reg);
                write!(f, "{:>width$}", regstr, width=regstr.len()+1)?;
            }
            write!(f, "\n")?;
            for kind in &GadgetKind::all_values() {
                write!(f, "{:>w$}", format!("{:?}", kind), w=max_kind_width+1)?;
                for reg in &X86Reg::all_values() {
                    let regstr = format!("{:?}", reg);
                    write!(f, "{:>width$}", self.0.contains_key(kind.gadgets_by_register()[*reg as usize]) as u8, width=regstr.len()+1)?;
                }
                write!(f, "\n")?;
            }
            Ok(())
        }
    }
}

pub mod high_level_eval;

pub mod stackish_machine {
    use std::collections::BTreeMap;
    use std::fmt::{self, Display, Formatter};
    use std::iter::FromIterator;
    use super::abstract_syntax::*;
    use super::x86_instructions::X86ConditionCode;

    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct InstructionAddress(usize);
    #[derive(Debug, Clone, Copy)]
    pub enum RegisterNumber {
        InstructionPointer,
        Accumulator,
        GeneralPurpose(usize),
        ArgumentNumber(usize), // codegen these to be compatible with x86 ABI?
    }

    #[derive(Debug, Clone, Copy)]
    pub enum ArithKind {
        Add, Sub, Mul, Xor, Swap, CMovLe
    }

    /// StackishOp<!> has no extra variants, and should map closely to x86 instructions
    /// StackishOp<HigherLevelOps> has extra variants that can be desugared to the initial ops
    /// instruction addresses are basic block indices at this level
    #[derive(Debug, Clone)]
    pub enum StackishOp<A> {
        Nop,
        Jump(InstructionAddress),
        ConditionalBranch(X86ConditionCode, InstructionAddress), // CMOVcc rsp, resolved_addr
        LoadImmediate(RegisterNumber, u64),
        ArithAccumReg(ArithKind, RegisterNumber),
        LoadAccum(RegisterNumber),
        StoreAccum(RegisterNumber),
        Syscall,
        Extra(A),
    }

    /// HigherLevelOps are more abstract, but are convenient to codegen
    /// they can be lowered to plain StackishOp's later
    #[derive(Debug, Clone)]
    pub enum HigherLevelOps {
        MovRegReg(RegisterNumber, RegisterNumber),
        StoreStartRelative(isize, RegisterNumber),
        LoadStartRelative(RegisterNumber, isize),
    }

    const ZONE_BETWEEN_VARS_AND_PROG: isize = 0x100;

    #[derive(Debug)]
    pub struct StackishProgram {
        basic_blocks: BTreeMap<InstructionAddress, Vec<StackishOp<HigherLevelOps>>>,
        current_bb: InstructionAddress,
        vars_from_start: BTreeMap<String, isize>, // stack before the ropchain is probably overwriteable, so allocate vars backwards from there
        type_ctx: BTreeMap<String, TypeId>,
        next_var_offset: isize,
        next_temp_register: usize,
    }

    impl Display for StackishProgram {
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

    impl StackishProgram {
        pub fn new() -> StackishProgram {
            StackishProgram {
                basic_blocks: BTreeMap::from_iter(vec![(InstructionAddress(0), vec![])]),
                current_bb: InstructionAddress(0),
                vars_from_start: BTreeMap::new(),
                type_ctx: BTreeMap::new(),
                next_var_offset: -ZONE_BETWEEN_VARS_AND_PROG,
                next_temp_register: 0,
            }
        }
        pub fn declare_value(&mut self, name: &str, ty: &TypeId, value: RegisterNumber) {
            self.next_var_offset -= ty.size_in_bytes() as isize;
            let addr = self.next_var_offset;
            self.vars_from_start.insert(name.into(), addr);
            self.type_ctx.insert(name.into(), ty.clone());
            self.push_to_current_bb(StackishOp::Extra(HigherLevelOps::StoreStartRelative(addr, value)));
        }
        pub fn push_to_current_bb(&mut self, op: StackishOp<HigherLevelOps>) {
            self.basic_blocks.get_mut(&self.current_bb).unwrap().push(op);
        }
        pub fn extend_current_bb(&mut self, ops: &[StackishOp<HigherLevelOps>]) {
            self.basic_blocks.get_mut(&self.current_bb).unwrap().extend_from_slice(ops);
        }
        pub fn start_basic_block(&mut self) -> InstructionAddress {
            self.current_bb.0 += 1;
            self.basic_blocks.insert(self.current_bb, vec![]);
            self.current_bb
        }
        pub fn get_next_gpr(&mut self) -> RegisterNumber {
            self.next_temp_register += 1;
            RegisterNumber::GeneralPurpose(self.next_temp_register)
        }
    }
    // TODO: should this take a register number (hence requiring translate_stmt to schedule all the registers?
    pub fn translate_expr(prog: &mut StackishProgram, expr: &Expr) -> RegisterNumber {
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
                    StackishOp::ArithAccumReg(ArithKind::Swap, out),
                ]);
                out
            },
        }
    }
    pub fn translate_stmt(prog: &mut StackishProgram, stmt: &Statement) {
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

    pub fn translate_function(prog: &mut StackishProgram, func: &FunctionDef) {
        for (i, (name, ty)) in func.args.iter().enumerate() {
            prog.declare_value(name, ty, RegisterNumber::ArgumentNumber(i));
        }
        for stmt in func.body.iter() {
            translate_stmt(prog, stmt);
        }
    }
}

fn main() {
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
            let mut prog = StackishProgram::new();
            translate_function(&mut prog, &f);
            println!("stackish program: {}", prog);
        }
    }
    let bin_ls_bytes = include_bytes!("/bin/ls");
    let gadgets_ls = gadget_search::find_gadgets(bin_ls_bytes, &x86_instructions::ALL_GADGETS);
    println!("gadgets in /bin/ls: {}", gadget_search::ViewGadgetsAsChart(&gadgets_ls));

    let bin_bash_bytes = include_bytes!("/bin/bash");
    let gadgets_bash = gadget_search::find_gadgets(bin_bash_bytes, &x86_instructions::ALL_GADGETS);
    println!("gadgets in /bin/bash: {}", gadget_search::ViewGadgetsAsChart(&gadgets_bash));

    let libc_bytes = include_bytes!("/lib/x86_64-linux-gnu/libc.so.6");
    let gadgets_libc = gadget_search::find_gadgets(libc_bytes, &x86_instructions::ALL_GADGETS);
    println!("gadgets in libc: {}", gadget_search::ViewGadgetsAsChart(&gadgets_libc));
}
