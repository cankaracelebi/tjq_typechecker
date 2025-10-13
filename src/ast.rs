use std::cmp::Ordering;
use ordered_float::OrderedFloat;
pub type Of64 = OrderedFloat<f64>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(String),
    App(Box<Expr>, Box<Expr>),
    Abs(String, Box<Expr>),
    Let(String, Box<Expr>, Box<Expr>),
    Lit(Lit),
    Tuple(Vec<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit {
    Int(i64),
    Bool(bool),
    Str(String),
    Null,
    Num(Of64),
}


#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Var(String),
    Arrow(Box<Type>, Box<Type>),
    Int,
    Bool,
    Tuple(Vec<Type>),

    // Top,
    // Bot,
    Union(Vec<Type>),
    Inter(Vec<Type>),
    Neg(Box<Type>),
    Json(Box<JType>),
    Mu(String, Box<JType>), // recursive JSON type (?)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum JType {
    Null,
    Bool(Option<bool>),   
    Num(Option<Of64>),      
    Str(Option<String>),    

    Arr { elem: Box<JType>, len: Option<usize> }, 
    Obj { fields: Vec<JField>, extra: Option<Box<JType>> },

    // Top,
    // Bot,
    Union(Vec<JType>),
    Inter(Vec<JType>),
    Neg(Box<JType>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct JField {
    pub name: String,
    pub ty: JType,
    pub optional: bool, 
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme {
    pub vars: Vec<String>,
    pub ty: Type,
}


impl std::fmt::Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expr::Var(n) => write!(f, "{n}"),
            Expr::Lit(Lit::Int(n)) => write!(f, "{n}"),
            Expr::Lit(Lit::Bool(b)) => write!(f, "{b}"),
            Expr::Lit(Lit::Str(s)) => write!(f, "{s:?}"),
            Expr::Lit(Lit::Null) => write!(f, "null"),
            Expr::Lit(Lit::Num(x)) => write!(f, "{x}"),
            Expr::Abs(p, b) => write!(f, "λ{p}.{}", b),
            Expr::App(fu, ar) => match (fu.as_ref(), ar.as_ref()) {
                (Expr::Abs(_, _), _) => write!(f, "({fu}) {ar}"),
                (_, Expr::App(_, _) | Expr::Abs(_, _)) => write!(f, "{fu} ({ar})"),
                _ => write!(f, "{fu} {ar}"),
            },
            Expr::Let(v, val, body) => write!(f, "let {v} = {val} in {body}"),
            Expr::Tuple(es) => {
                write!(f, "(")?;
                for (i, e) in es.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{e}")?;
                }
                write!(f, ")")
            }
        }
    }
}

impl std::fmt::Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use Type::*;
        match self {
            Var(n) => write!(f, "{n}"),
            Int => write!(f, "Int"),
            Bool => write!(f, "Bool"),
            Tuple(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{t}")?;
                }
                write!(f, ")")
            }
            Arrow(a, b) => {
                let paren = matches!(a.as_ref(), Arrow(_, _) | Union(_) | Inter(_) | Neg(_));
                if paren { write!(f, "({a}) → {b}") } else { write!(f, "{a} → {b}") }
            }
            // Top => write!(f, "⊤"),
            // Bot => write!(f, "⊥"),
            Union(ts) => write_infix(f, " ∪ ", ts),
            Inter(ts) => write_infix(f, " ∩ ", ts),
            Neg(t) => {
                let paren = matches!(t.as_ref(), Arrow(_, _) | Union(_) | Inter(_) | Neg(_));
                if paren { write!(f, "¬({t})") } else { write!(f, "¬{t}") }
            }
            Json(jt) => write!(f, "Json<{jt}>"),
            Mu(v, jt) => write!(f, "μ{v}.{jt}"),    
        }
    }
}

impl std::fmt::Display for JType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use JType::*;
        match self {
            Null => write!(f, "Null"),
            Bool(None) => write!(f, "Bool"),
            Bool(Some(b)) => write!(f, "Bool({b})"),
            Num(None) => write!(f, "Number"),
            Num(Some(x)) => write!(f, "Number({x})"),
            Str(None) => write!(f, "String"),
            Str(Some(s)) => write!(f, "String({s:?})"),
            Arr { elem, len } => match len {
                Some(n) => write!(f, "[{}; {}]", elem, n),
                None => write!(f, "[{}]", elem),
            },
            Obj { fields, extra } => {
                write!(f, "{{")?;
                for (i, fld) in fields.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    if fld.optional { write!(f, "{}?: {}", fld.name, fld.ty)?; }
                    else { write!(f, "{}: {}", fld.name, fld.ty)?; }
                }
                if let Some(rest) = extra {
                    if !fields.is_empty() { write!(f, ", ")?; }
                    write!(f, "..: {}", rest)?;
                }
                write!(f, "}}")
            }
            // Top => write!(f, "⊤J"),
            // Bot => write!(f, "⊥J"),
            Union(ts) => write_infix(f, " ∪ ", ts),
            Inter(ts) => write_infix(f, " ∩ ", ts),
            Neg(t) => {
                let paren = matches!(t.as_ref(), Union(_) | Inter(_) | Neg(_));
                if paren { write!(f, "¬({t})") } else { write!(f, "¬{t}") }
            }
        }
    }
}

impl std::fmt::Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.vars.is_empty() { write!(f, "{}", self.ty) }
        else { write!(f, "forall {}. {}", self.vars.join(" "), self.ty) }
    }
}
fn write_infix<T: std::fmt::Display>(
    f: &mut std::fmt::Formatter<'_>,
    sep: &str,
    xs: &[T],
) -> std::fmt::Result {
    let mut it = xs.iter();
    if let Some(first) = it.next() { write!(f, "{first}")?; }
    for x in it { write!(f, "{sep}{x}")?; }
    Ok(())
}