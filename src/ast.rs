use symbolic_expressions::{Sexp, SexpError};
use std::{str::FromStr, fmt::Display, collections::HashMap};
use egg::{*};

#[derive(Debug, Clone)]
pub struct Type { 
  repr: Sexp
}

impl Type {
  fn new(repr: Sexp) -> Self {
    Self { repr }
  }

  pub fn datatype(&self) -> Result<&String, SexpError> {
    self.repr.string()
  }

  pub fn args(&self) -> Vec<Type> {
    match &self.repr {
      Sexp::String(_) => vec![],  // This type is a D
      Sexp::List(xs) => {         // This type is a (-> (D1 ... Dn) D)
        let mut args = vec![];
        for x in xs[1].list().unwrap() {
          args.push(Type::new(x.clone()));
        }
        args        
      }
      _ => panic!("arity: type is empty"),
    }
  }
}

impl FromStr for Type {
  type Err = SexpError;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    Ok(Type::new(symbolic_expressions::parser::parse_str(s)?))
  }
}

impl Display for Type {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "{}", self.repr)
  }
}

// Expressions
pub type Expr = RecExpr<SymbolLang>;

pub fn var_depth(var_name: &str) -> usize {
  var_name.matches("-").count()
}

pub fn is_descendant(var_name: &String, ancestor_name: &String) -> bool {
  var_name.starts_with(ancestor_name) && var_name.len() > ancestor_name.len()
}

// Environment: for now just a map from datatype names to constructor names
pub type Env = HashMap<Symbol, Vec<Symbol>>;

// Type context
pub type Context = HashMap<Symbol, Type>;

pub fn mk_context(descr: &[(&str, &str)]) -> Context {
  let mut ctx = Context::new();
  for (name, ty) in descr {
    ctx.insert(Symbol::from(name), ty.parse().unwrap());
  }
  ctx
}

pub fn mk_env(descr: &[(&str, &str)]) -> Env {
  let mut env = Env::new();
  for (name, cons) in descr {
    env.insert(Symbol::from(name), cons.split_whitespace().map(|s| Symbol::from(s)).collect());
  }
  env
}
