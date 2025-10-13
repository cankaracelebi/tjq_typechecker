use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

use crate::ast::{Expr, Lit, Scheme, Type, JType, JField};

pub type TyVar = String;
pub type TmVar = String;
pub type Env = BTreeMap<TmVar, Scheme>; 
pub type Subst = HashMap<TyVar, Type>;

#[derive(Debug)]
pub struct InferenceTree {
    pub rule: String,
    pub input: String,
    pub output: String,
    pub children: Vec<InferenceTree>,
}


pub struct TypeInference {
    counter: usize,
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInference{
    pub fn new()-> Self {
        Self { counter: 0 }
    }
    fn fresh_tyvar(&mut self) -> TyVar{
        let var = format!("t{}", self.counter);
        self.counter += 1;
        var
    }
    fn pretty_env(&self, env: &Env) -> String {
        if env.is_empty() {
            "{}".to_string()
        } else {
            let entries: Vec<String> = env.iter().map(|(k, v)| format!("{}: {}", k, v)).collect();
            format!("{{{}}}", entries.join(", "))
        }
    }
    fn pretty_subst(&self, subst: &Subst) -> String {
        if subst.is_empty() {
            "{}".to_string()
        } else {
            let entries: Vec<String> = subst.iter().map(|(k, v)| format!("{}/{}", v, k)).collect();
            format!("{{{}}}", entries.join(", "))
        }
    }
    fn apply_subst(&self, subst: &Subst, ty: &Type) -> Type {
        match ty {
            Type::Var(name) => subst.get(name).cloned().unwrap_or_else(|| ty.clone()),
            Type::Arrow(t1, t2) => Type::Arrow(
                Box::new(self.apply_subst(subst, t1)),
                Box::new(self.apply_subst(subst, t2)),
            ),
            Type::Tuple(types) => {
                Type::Tuple(types.iter().map(|t| self.apply_subst(subst, t)).collect())
            }
            Type::Int | Type::Bool => ty.clone(),
            Type::Inter(types) => {
                Type::Inter(types.iter().map(|t| self.apply_subst(subst, t)).collect())
            }
            Type::Neg(t) => Type::Neg(Box::new(self.apply_subst(subst, t))),
            Type::Union(types) => {
                Type::Union(types.iter().map(|t| self.apply_subst(subst, t)).collect())
            }
            Type::Json(jt) => Type::Json(Box::new(self.apply_subst_jtype(subst, jt))),
            Type::Mu(v, jt) => Type::Mu(v.clone(), Box::new(self.apply_subst_jtype(subst, jt))),
        }
    }
    fn apply_subst_jtype(&self, subst: &Subst, ty: &JType) -> JType{
        //check !
        match ty {
            JType::Arr { elem, len } => JType::Arr { 
                elem: Box::new(self.apply_subst_jtype(subst, elem)), 
                len: *len 
            },
            JType::Obj { fields, extra } => JType::Obj { 
                fields: fields.iter().map(|f| JField { 
                    name: f.name.clone(), 
                    ty: self.apply_subst_jtype(subst, &f.ty), 
                    optional: f.optional 
                }).collect(),
                extra: extra.as_ref().map(|e| Box::new(self.apply_subst_jtype(subst, e)))
            },
            JType::Null | JType::Bool(None) | JType::Num(None) | JType::Str(None) => ty.clone(),
            JType::Bool(Some(b)) => JType::Bool(Some(*b)),
            JType::Num(Some(n)) => JType::Num(Some(*n)),
            JType::Str(Some(s)) => JType::Str(Some(s.clone())),
            JType::Inter(types) => {
                JType::Inter(types.iter().map(|t| self.apply_subst_jtype(subst, t)).collect())
            }
            JType::Neg(t) => JType::Neg(Box::new(self.apply_subst_jtype(subst, t))),
            JType::Union(types) => {
                JType::Union(types.iter().map(|t| self.apply_subst_jtype(subst, t)).collect())
            }

        }
    }
     fn apply_subst_scheme(&self, subst: &Subst, scheme: &Scheme) -> Scheme {
        // Remove bindings for quantified variables to avoid capture
        let mut filtered_subst = subst.clone();
        for var in &scheme.vars {
            filtered_subst.remove(var);
        }
        Scheme {
            vars: scheme.vars.clone(),
            ty: self.apply_subst(&filtered_subst, &scheme.ty),
        }
    }



}