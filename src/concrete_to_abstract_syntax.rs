use super::concrete_syntax::Rule;
use super::abstract_syntax::*;
use pest::iterators::Pair;
pub fn ident(pair: Pair<Rule>) -> String {
    if let Rule::ident = pair.as_rule() {
        pair.as_span().as_str().into()
    } else {
        panic!("expected ident, got {:?}", pair.as_rule());
    }
}
pub fn numeric_literal(pair: Pair<Rule>) -> String {
    if let Rule::numeric_literal = pair.as_rule() {
        pair.as_span().as_str().into()
    } else {
        panic!("expected numeric_literal, got {:?}", pair.as_rule());
    }
}
pub fn typeid(pair: Pair<Rule>) -> TypeId {
    if let Rule::type_id = pair.as_rule() {
        let mut pairs = pair.into_inner();
        println!("{:?}", pairs);
        let typair = pairs.next().unwrap();
        let ty = match typair.as_rule() {
            Rule::pointertype => TypeId::Pointer(Box::new(typeid(typair.into_inner().next().unwrap()))),
            Rule::primword64 => TypeId::Word64,
            other => panic!("invalid type_id {:?}", other),
        };
        println!("{:?}", ty);
        assert!(pairs.next().is_none());
        ty
    } else {
        panic!("expected type_id, got {:?}", pair.as_rule());
    }
}
pub fn vardecl(pair: Pair<Rule>) -> (String, TypeId) {
    if let Rule::vardecl = pair.as_rule() {
        let mut pairs = pair.into_inner();
        let ident = ident(pairs.next().unwrap());
        let typeid = typeid(pairs.next().unwrap());
        assert!(pairs.next().is_none());
        (ident, typeid)
    } else {
        panic!("expected vardecl, got {:?}", pair.as_rule());
    }
}
pub fn expr(pair: Pair<Rule>) -> Expr {
    if let Rule::expr = pair.as_rule() {
        let exp = pair.into_inner().next().unwrap();
        let rule = exp.as_rule();
        let mut exp = exp.into_inner();
        match rule {
            Rule::literal_expr => Expr::Literal(numeric_literal(exp.next().unwrap())),
            Rule::var_expr => Expr::Var(ident(exp.next().unwrap())),
            Rule::deref_expr => Expr::Deref(Box::new(expr(exp.next().unwrap()))),
            other => panic!("invalid expr {:?}", other),
        }
    } else {
        panic!("expected expr, got {:?}", pair.as_rule());
    }
}
pub fn assignment_modifier(pair: Pair<Rule>) -> AssignmentModifier {
    match pair.as_span().as_str() {
        "=" => AssignmentModifier::Normal,
        "+=" => AssignmentModifier::Add,
        other => panic!("invalid assignment modifier {:?}", other),
    }
}
pub fn statement(pair: Pair<Rule>) -> Statement {
    if let Rule::statement = pair.as_rule() {
        let stmt = pair.into_inner().next().unwrap();
        let rule = stmt.as_rule();
        let mut stmt = stmt.into_inner();
        let ret = match rule {
            Rule::localdef => {
                let (ident, ty) = vardecl(stmt.next().unwrap());
                let initializer = expr(stmt.next().unwrap());
                Statement::LocalDecl { ident, ty, initializer }
            },
            Rule::dotimes => {
                let amount = expr(stmt.next().unwrap());
                let body = stmt.map(statement).collect();
                Statement::DoTimes { amount, body }
            }
            Rule::assignment => {
                let lhs = ident(stmt.next().unwrap());
                let modifier = assignment_modifier(stmt.next().unwrap());
                let rhs = expr(stmt.next().unwrap());
                Statement::Assigment { lhs, modifier, rhs }
            }
            Rule::returnstmt => {
                let val = expr(stmt.next().unwrap());
                Statement::Return { val }
            }
            other => panic!("invalid statement {:?}", other),
        };
        ret
    } else {
        panic!("expected statement, got {:?}", pair.as_rule());
    }
}
pub fn functiondef(pair: Pair<Rule>) -> FunctionDef {
    if let Rule::function = pair.as_rule() {
        let mut pairs = pair.into_inner();
        let name = ident(pairs.next().unwrap());
        println!("name: {:?}", name);
        let args: Vec<(String, TypeId)> = pairs.next().unwrap().into_inner().map(|x| vardecl(x)).collect();
        println!("args: {:?}", args);
        let return_type = typeid(pairs.next().unwrap());
        println!("return_type: {:?}", return_type);
        println!("rest of pairs: {:?}", pairs);
        let body: Vec<Statement> = pairs.map(statement).collect();
        FunctionDef { name, args, return_type, body }
    } else {
        panic!("expected function, got {:?}", pair.as_rule());
    }
}
