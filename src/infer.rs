use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

use crate::ast::{Expr, JField, JType, Lit, Scheme, Type};

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

impl InferenceTree {
    fn new(rule: &str, input: &str, output: &str, children: Vec<InferenceTree>) -> Self {
        Self {
            rule: rule.to_string(),
            input: input.to_string(),
            output: output.to_string(),
            children,
        }
    }
}

pub struct TypeInference {
    counter: usize,
}

impl Default for TypeInference {
    fn default() -> Self {
        Self::new()
    }
}

impl TypeInference {
    pub fn new() -> Self {
        Self { counter: 0 }
    }
    fn fresh_tyvar(&mut self) -> TyVar {
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
        }
    }
    fn apply_subst_jtype(&self, subst: &Subst, ty: &JType) -> JType {
        //check !
        match ty {
            JType::Arr { elem, len } => JType::Arr {
                elem: Box::new(self.apply_subst_jtype(subst, elem)),
                len: *len,
            },
            JType::Obj { fields, extra } => JType::Obj {
                fields: fields
                    .iter()
                    .map(|f| JField {
                        name: f.name.clone(),
                        ty: self.apply_subst_jtype(subst, &f.ty),
                        optional: f.optional,
                    })
                    .collect(),
                extra: extra
                    .as_ref()
                    .map(|e| Box::new(self.apply_subst_jtype(subst, e))),
            },
            JType::Null | JType::Bool(None) | JType::Num(None) | JType::Str(None) => ty.clone(),
            JType::Bool(Some(b)) => JType::Bool(Some(*b)),
            JType::Num(Some(n)) => JType::Num(Some(*n)),
            JType::Str(Some(s)) => JType::Str(Some(s.clone())),
            JType::Inter(types) => JType::Inter(
                types
                    .iter()
                    .map(|t| self.apply_subst_jtype(subst, t))
                    .collect(),
            ),
            JType::Neg(t) => JType::Neg(Box::new(self.apply_subst_jtype(subst, t))),
            JType::Union(types) => JType::Union(
                types
                    .iter()
                    .map(|t| self.apply_subst_jtype(subst, t))
                    .collect(),
            ),
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
    fn apply_subst_env(&self, subst: &Subst, env: &Env) -> Env {
        env.iter()
            .map(|(k, v)| (k.clone(), self.apply_subst_scheme(subst, v)))
            .collect()
    }
    fn compose_subst(&self, s1: &Subst, s2: &Subst) -> Subst {
        let mut result = s1.clone();
        for (k, v) in s2 {
            result.insert(k.clone(), self.apply_subst(s1, v));
        }
        result
    }
    fn free_type_vars(&self, ty: &Type) -> HashSet<TyVar> {
        match ty {
            Type::Var(name) => {
                let mut set = HashSet::new();
                set.insert(name.clone());
                set
            }
            Type::Arrow(t1, t2) => {
                let mut set = self.free_type_vars(t1);
                set.extend(self.free_type_vars(t2));
                set
            }
            Type::Tuple(types) => {
                let mut set = HashSet::new();
                for t in types {
                    set.extend(self.free_type_vars(t));
                }
                set
            }
            Type::Int | Type::Bool => HashSet::new(),
            Type::Inter(types) | Type::Union(types) => {
                let mut set = HashSet::new();
                for t in types {
                    set.extend(self.free_type_vars(t));
                }
                set
            }
            Type::Neg(t) => self.free_type_vars(t),
        }
    }
    fn free_type_vars_jtype(&self, ty: &JType) -> HashSet<TyVar> {
        match ty {
            JType::Arr { elem, .. } => self.free_type_vars_jtype(elem),
            JType::Obj { fields, extra } => {
                let mut set = HashSet::new();
                for f in fields {
                    set.extend(self.free_type_vars_jtype(&f.ty));
                }
                if let Some(e) = extra {
                    set.extend(self.free_type_vars_jtype(e));
                }
                set
            }
            JType::Null | JType::Bool(None) | JType::Num(None) | JType::Str(None) => HashSet::new(),
            JType::Bool(Some(_)) | JType::Num(Some(_)) | JType::Str(Some(_)) => HashSet::new(),
            JType::Inter(types) | JType::Union(types) => {
                let mut set = HashSet::new();
                for t in types {
                    set.extend(self.free_type_vars_jtype(t));
                }
                set
            }
            JType::Neg(t) => self.free_type_vars_jtype(t),
        }
    }
    fn occurs_check(&self, var: &TyVar, ty: &Type) -> bool {
        self.free_type_vars(ty).contains(var)
    }
    fn unify(&self, t1: &Type, t2: &Type) -> Result<(Subst, InferenceTree), String> {
        let input = format!("{} ~ {}", t1, t2);
        
        match (t1, t2) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) => {
                let tree = InferenceTree::new("Unify-Base", &input, "{}", vec![]);
                Ok((HashMap::new(), tree))
            }
            (Type::Var(v), ty) | (ty, Type::Var(v)) => {
                if ty == &Type::Var(v.clone()) {
                    let tree = InferenceTree::new("Unify-Var-Same", &input, "{}", vec![]);
                    Ok((HashMap::new(), tree))
                } else if self.occurs_check(v, ty) {
                    Err(format!("Occurs check failed: {} occurs in {}", v, ty))
                } else {
                    let mut subst = HashMap::new();
                    subst.insert(v.clone(), ty.clone());
                    let output = format!("{{{}/{}}}", ty, v);
                    let tree = InferenceTree::new("Unify-Var", &input, &output, vec![]);
                    Ok((subst, tree))
                }
            }
            (Type::Arrow(a1, a2), Type::Arrow(b1, b2)) => {
                let (s1, tree1) = self.unify(a1, b1)?;
                let a2_subst = self.apply_subst(&s1, a2);
                let b2_subst = self.apply_subst(&s1, b2);
                let (s2, tree2) = self.unify(&a2_subst, &b2_subst)?;
                let final_subst = self.compose_subst(&s2, &s1);
                let output = self.pretty_subst(&final_subst);
                let tree = InferenceTree::new("Unify-Arrow", &input, &output, vec![tree1, tree2]);
                Ok((final_subst, tree))
            }
            (Type::Tuple(ts1), Type::Tuple(ts2)) => {
                if ts1.len() != ts2.len() {
                    return Err(format!(
                        "Tuple length mismatch: {} vs {}",
                        ts1.len(),
                        ts2.len()
                    ));
                }

                let mut subst = HashMap::new();
                let mut trees = Vec::new();

                for (t1, t2) in ts1.iter().zip(ts2.iter()) {
                    let t1_subst = self.apply_subst(&subst, t1);
                    let t2_subst = self.apply_subst(&subst, t2);
                    let (s, tree) = self.unify(&t1_subst, &t2_subst)?;
                    subst = self.compose_subst(&s, &subst);
                    trees.push(tree);
                }

                let output = self.pretty_subst(&subst);
                let tree = InferenceTree::new("Unify-Tuple", &input, &output, trees);
                Ok((subst, tree))
            }
            // FIXED: Return proper error string
            _ => Err(format!(
                "Unification failure: cannot unify {} with {}",
                t1, t2
            )),
        }
    }
    pub fn infer(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        match expr {
            Expr::Lit(Lit::Int(_)) => self.infer_lit_int(env, expr),
            Expr::Lit(Lit::Bool(_)) => self.infer_lit_bool(env, expr),
            Expr::Lit(Lit::Str(_)) => self.infer_lit_string(env, expr),
            Expr::Lit(Lit::Null) => self.infer_lit_null(env, expr),
            Expr::Lit(Lit::Num(_)) => self.infer_lit_num(env, expr),
            Expr::Var(name) => self.infer_var(env, expr, name),
            // Expr::Abs(param, body) => self.infer_abs(env, expr, param, body),
            // Expr::App(func, arg) => self.infer_app(env, expr, func, arg),
            // Expr::Let(var, value, body) => self.infer_let(env, expr, var, value, body),
            // Expr::Tuple(exprs) => self.infer_tuple(env, expr, exprs),
            _ => todo!(),
        }
    }
    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        // Create fresh type variables for each quantified variable
        let mut subst = HashMap::new();
        for var in &scheme.vars {
            let fresh = self.fresh_tyvar();
            subst.insert(var.clone(), Type::Var(fresh));
        }

        self.apply_subst(&subst, &scheme.ty)
    }

    /// T-Var: x : σ ∈ Γ    τ = inst(σ)
    ///        ─────────────────────────
    ///               Γ ⊢ x : τ
    fn infer_var(
        &mut self,
        env: &Env,
        expr: &Expr,
        name: &str,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        let input = format!("{} ⊢ {} ⇒", self.pretty_env(env), expr);

        match env.get(name) {
            Some(scheme) => {
                let instantiated = self.instantiate(scheme);
                let output = format!("{}", instantiated);
                let tree = InferenceTree::new("T-Var", &input, &output, vec![]);
                Ok((HashMap::new(), instantiated, tree))
            }
            None => Err(format!("asd")),
        }
    }
    /// T-LitInt: ─────────────────
    ///           Γ ⊢ n : Int
    fn infer_lit_int(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        let input = format!("{} ⊢ {} ⇒", self.pretty_env(env), expr);
        let tree = InferenceTree::new("T-Int", &input, "Int", vec![]);
        Ok((HashMap::new(), Type::Int, tree))
    }
    /// T-LitBool: ─────────────────
    ///            Γ ⊢ b : Bool
    fn infer_lit_bool(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        let input = format!("{} ⊢ {} ⇒", self.pretty_env(env), expr);
        let tree = InferenceTree::new("T-Bool", &input, "Bool", vec![]);
        Ok((HashMap::new(), Type::Bool, tree))
    }
    /// T-LitString: ─────────────────
    ///            Γ ⊢ s : String
    fn infer_lit_string(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        let input = format!("{} ⊢ {} : ?", self.pretty_env(env), expr);
        let tree = InferenceTree::new("T-LitString", &input, "String", vec![]);

        todo!()
    }
    /// T-LitNull: ─────────────────
    ///            Γ ⊢ n : Null
    fn infer_lit_null(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        let input = format!("{} ⊢ {} : ?", self.pretty_env(env), expr);
        let tree = InferenceTree::new("T-LitNull", &input, "Null", vec![]);

        todo!()
    }
    /// T-LitString: ─────────────────
    ///            Γ ⊢ n: num
    fn infer_lit_num(
        &mut self,
        env: &Env,
        expr: &Expr,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        let input = format!("{} ⊢ {} : ?", self.pretty_env(env), expr);
        let tree = InferenceTree::new("T-LitNum", &input, "Num", vec![]);

        todo!()
    }
    /// T-Lam: Γ, x : α ⊢ e : τ    α fresh
    ///        ─────────────────────────────
    ///           Γ ⊢ λx. e : α → τ
    fn infer_abs(
        &mut self,
        env: &Env,
        expr: &Expr,
        name: &str,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        todo!()
    }
    /// T-App: Γ ⊢ e₁ : τ₁    Γ ⊢ e₂ : τ₂    α fresh    S = unify(τ₁, τ₂ → α)
    ///        ──────────────────────────────────────────────────────────────
    ///                            Γ ⊢ e₁ e₂ : S(α)
    fn infer_app(
        &mut self,
        env: &Env,
        expr: &Expr,
        name: &str,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        todo!()
    }
    /// T-Let: Γ ⊢ e₁ : τ₁    σ = gen(Γ, τ₁)    Γ, x : σ ⊢ e₂ : τ₂
    ///        ──────────────────────────────────────────────────────
    ///                     Γ ⊢ let x = e₁ in e₂ : τ₂
    fn infer_let(
        &mut self,
        env: &Env,
        expr: &Expr,
        name: &str,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        todo!()
    }
    fn infer_tuple(
        &mut self,
        env: &Env,
        expr: &Expr,
        name: &str,
    ) -> Result<(Subst, Type, InferenceTree), String> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_infer_lit_int() {
        let mut ti = TypeInference::new();
        let env = Env::new();
        let expr = Expr::Lit(Lit::Int(42));
        let (subst, ty, tree) = ti.infer(&env, &expr).unwrap();
        assert!(subst.is_empty());
        assert_eq!(ty, Type::Int);
        assert_eq!(tree.rule, "T-LitInt");
    }
}
