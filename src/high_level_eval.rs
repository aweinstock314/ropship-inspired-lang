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
                    let to_add = rhs_val.wrapping_mul(state.type_ctx[lhs].stride_to_increment() as u64);
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
