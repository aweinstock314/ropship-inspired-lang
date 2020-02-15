#[macro_use] extern crate pest_derive;
use pest::Parser;

pub mod concrete_syntax {
    #[derive(Parser)]
    #[grammar = "syntax.pest"]
    pub struct RILParser;
}

pub mod abstract_syntax {
    pub enum Type {
        Pointer(Box<Type>),
        Word64,
    }

    pub enum AssignmentModifier {
        Normal,
        Add,
    }

    pub enum Expr {
        Literal(String),
        Deref(Box<Expr>),
        Var(String),
    }

    pub enum Statement {
        LocalDecl { ident: String, ty: Type, initializer: Expr },
        DoTimes { amount: Expr, body: Box<Statement> },
        Assigment { lhs: String, modifier: AssignmentModifier, rhs: Expr },
        Return { val: Expr },
    }

    pub struct FunctionDef {
        name: String,
        args: Vec<(String, Type)>,
        return_type: Type,
        body: Vec<Statement>,
    }

    pub struct TranslationUnit {
        functions: Vec<FunctionDef>,
    }
}


fn main() {
    let input_bytes = include_bytes!("../sum_input.ril");
    let input_string = String::from_utf8_lossy(&*input_bytes);
    let res = concrete_syntax::RILParser::parse(concrete_syntax::Rule::function, &input_string);
    println!("{:#?}", res);
}
