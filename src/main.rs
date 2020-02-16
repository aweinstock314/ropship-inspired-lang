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
    const XCHG_EAX_EXX: [&[u8]; 8] = [&*b"\x90", &*b"\x91", &*b"\x92", &*b"\x93", &*b"\x94", &*b"\x95", &*b"\x96", &*b"\x97"];
    const CMOVLE_EAX_EXX: [&[u8]; 8] = [&*b"\x0f\x4e\xc0", &*b"\x0f\x4e\xc1", &*b"\x0f\x4e\xc2", &*b"\x0f\x4e\xc3", &*b"\x0f\x4e\xc4", &*b"\x0f\x4e\xc5", &*b"\x0f\x4e\xc6", &*b"\x0f\x4e\xc7"];
    const IMUL_EXX: [&[u8]; 8] = [&*b"\xf7\xe8", &*b"\xf7\xe9", &*b"\xf7\xea", &*b"\xf7\xeb", &*b"\xf7\xec", &*b"\xf7\xed", &*b"\xf7\xee", &*b"\xf7\xef"];
    const LOAD_EXX_EAX: [&[u8]; 8] = [&*b"\x8b\x00", &*b"\x8b\x08", &*b"\x8b\x10", &*b"\x8b\x18", &*b"\x8b\x20", &*b"\x8b\x28", &*b"\x8b\x30", &*b"\x8b\x38"]; // "mov $reg, dword [eax]"
    const STORE_EAX_EXX: [&[u8]; 8] = [&*b"\x89\x00", &*b"\x89\x08", &*b"\x89\x10", &*b"\x89\x18", &*b"\x89\x20", &*b"\x89\x28", &*b"\x89\x30", &*b"\x89\x38"]; // "mov dword [eax], $reg"

    #[repr(C)]
    pub enum X86Reg {
        EAX, ECX, EDX, EBX, ESP, EBP, ESI, EDI
    }
}

pub mod high_level_eval {
    use std::collections::BTreeMap;
    use super::abstract_syntax::*;

    #[derive(Debug)]
    pub struct HighLevelState {
        pub concrete_mem: BTreeMap<u64, u8>,
        pub abstract_mem: BTreeMap<String, u64>,
        pub type_ctx: BTreeMap<String, TypeId>,
    }

    impl HighLevelState {
        pub fn new() -> HighLevelState {
            HighLevelState {
                concrete_mem: BTreeMap::new(),
                abstract_mem: BTreeMap::new(),
                type_ctx: BTreeMap::new(),
            }
        }
        pub fn allocate_data(&mut self, data: &[u8]) -> u64 {
            let highest_allocated: u64 = self.concrete_mem.range(..).next_back().map(|(x,_)| *x).unwrap_or(0);
            let start = highest_allocated + 1;
            for (i, x) in data.iter().enumerate() {
                self.concrete_mem.insert(start+(i as u64), *x);
            }
            start
        }
        pub fn read64(&self, addr: u64) -> u64 {
            let mut res = 0u64;
            for i in 0..8 {
                res |= (self.concrete_mem[&(addr+i)] as u64) << (8*i);
            }
            res
        }
        pub fn declare_value(&mut self, name: &str, ty: &TypeId, val: u64) {
            self.abstract_mem.insert(name.into(), val);
            self.type_ctx.insert(name.into(), ty.clone());
        }
    }

    pub fn eval_expr(state: &HighLevelState, expr: &Expr) -> u64 {
        println!("eval expr: {:?}", expr);
        match expr {
            Expr::Literal(s) => s.parse::<u64>().unwrap(),
            Expr::Deref(e) => { state.read64(eval_expr(state, e)) },
            Expr::Var(s) => state.abstract_mem[s],
        }
    }

    #[derive(Debug)]
    pub enum ControlFlow {
        Next,
        Return(u64),
    }

    pub fn eval_stmt(state: &mut HighLevelState, stmt: &Statement) -> ControlFlow {
        println!("eval stmt: {:?}", stmt);
        match stmt {
            Statement::LocalDecl { ident, ty, initializer } => {
                state.declare_value(ident, ty, eval_expr(state, initializer));
            },
            Statement::DoTimes { amount, body } => {
                let amount = eval_expr(state, amount);
                for _ in 0..amount {
                    for stmt in body {
                        match eval_stmt(state, stmt) {
                            ControlFlow::Next => (),
                            x @ ControlFlow::Return(_) => { return x },
                        }
                    }
                }
            }
            Statement::Assignment { lhs, modifier, rhs } => {
                let rhs_val = eval_expr(state, rhs); 
                match modifier {
                    AssignmentModifier::Normal => state.abstract_mem.insert(lhs.clone(), rhs_val),
                    AssignmentModifier::Add => {
                        let to_add = match state.type_ctx[lhs] {
                            TypeId::Pointer(_) => rhs_val.wrapping_mul(8),
                            _ => rhs_val,
                        };
                        state.abstract_mem.insert(lhs.clone(), state.abstract_mem[lhs].wrapping_add(to_add))
                    },
                };
            },
            Statement::Return { val } => return ControlFlow::Return(eval_expr(state, val)),
        }
        ControlFlow::Next
    }

    pub fn eval_function(state: &mut HighLevelState, func: &FunctionDef, args: &[u64]) -> Option<u64> {
        for ((name, ty), val) in func.args.iter().zip(args) {
            state.declare_value(name, ty, *val);
        }
        for stmt in func.body.iter() {
            println!("state: {:?}", state);
            match eval_stmt(state, stmt) {
                ControlFlow::Next => (),
                ControlFlow::Return(n) => return Some(n),
            }
        }
        None
    }
}

fn main() {
    let input_bytes = include_bytes!("../sum_input.ril");
    let input_string = String::from_utf8_lossy(&*input_bytes);
    let res = concrete_syntax::RILParser::parse(concrete_syntax::Rule::function, &input_string);
    println!("{:?}\n", res);
    if let Ok(mut pairs) = res { 
        let f = concrete_to_abstract_syntax::functiondef(pairs.next().unwrap());
        println!("{:?}", f);
        {
            use high_level_eval::*;
            let mut state = HighLevelState::new();
            let data: &[u64] = &[0,1,2,3,4,5,6,7,8,9];
            let data64: &[u8] = unsafe { ::std::slice::from_raw_parts(data.as_ptr() as _, data.len() * ::std::mem::size_of::<u64>() / ::std::mem::size_of::<u8>()) };
            let p = state.allocate_data(&data64);
            let ret = eval_function(&mut state, &f, &[p, data.len() as _]);
            println!("eval returned {:?}", ret);
        }
    }
}
