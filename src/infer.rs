use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;

use crate::ast::{Expr, Lit, Scheme, Type, JType};

pub type TyVar = String;
pub type TmVar = String;
pub type Env = BTreeMap<TmVar, Scheme>; 

#[derive(Debug)]
pub struct InferenceTree {
    pub rule: String,
    pub input: String,
    pub output: String,
    pub children: Vec<InferenceTree>,
}


