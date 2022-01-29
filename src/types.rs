use symbolic_expressions::{Sexp, SexpError};
use std::{str::FromStr, fmt::Display};

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
