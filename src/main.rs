#[macro_use] extern crate pest_derive;
use pest::Parser;

pub mod concrete_syntax {
    #[derive(Parser)]
    #[grammar = "syntax.pest"]
    pub struct RILParser;
}

pub mod abstract_syntax {
    #[derive(Debug)]
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
        Assigment { lhs: String, modifier: AssignmentModifier, rhs: Expr },
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


fn main() {
    let input_bytes = include_bytes!("../sum_input.ril");
    let input_string = String::from_utf8_lossy(&*input_bytes);
    let res = concrete_syntax::RILParser::parse(concrete_syntax::Rule::function, &input_string);
    println!("{:?}\n", res);
    if let Ok(mut pairs) = res { 
        println!("{:#?}", concrete_to_abstract_syntax::functiondef(pairs.next().unwrap()));
    }
}
