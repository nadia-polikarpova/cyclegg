use symbolic_expressions::{Sexp, SexpError};
use std::{str::FromStr, fmt::Display, collections::HashMap};
use egg::{*};

#[derive(Debug, Clone, PartialEq)]
pub struct Type { 
  repr: Sexp
}

impl Type {
  pub fn new(repr: Sexp) -> Self {
    Self { repr }
  }

  /// If this type is a datatype, returns its name and otherwise return error.
  pub fn datatype(&self) -> Result<&String, SexpError> {
    match &self.repr {
      Sexp::String(s) => Ok(s),   // This type is a D
      Sexp::List(xs) => {         // This type is a type constructor application
        match xs[0].string()?.as_str() {
          "->" => Err(SexpError::Other("expected datatype and got arrow".to_string())),
          _    => xs[0].string()
        }
      }
      _ => panic!("arity: type is empty"),
    }
  }

  /// Split a type into arguments and return value
  /// (arguments are empty if the type is not an arrow)
  pub fn args_ret(&self) -> (Vec<Type>, Type) {
    match &self.repr {
      Sexp::String(_) => (vec![], self.clone()),  // This type is a D
      Sexp::List(xs) => {         // This type is a (-> (D1 ... Dn) D)
        match xs[0].string().unwrap().as_str() {
          "->" => {
            let args = xs[1].list().unwrap().iter().map(|x| Type::new(x.clone())).collect(); 
            (args, Type::new(xs[2].clone()))
          }          
          _    => (vec![], self.clone())
        }
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
pub type Pat = Pattern<SymbolLang>;

pub const BOOL_TYPE: &str = "Bool";
pub const ITE: &str = "ite";
pub const TRUE: &str = "True";
pub const FALSE: &str = "False";
pub const APPLY: &str = "$";
pub const GUARD_PREFIX: &str = "g-";

pub fn var_depth(var_name: &str) -> usize {
  var_name.matches("-").count()
}

pub fn is_descendant(var_name: &String, ancestor_name: &String) -> bool {
  var_name.starts_with(ancestor_name) && var_name.len() > ancestor_name.len()
}

pub fn is_constructor(var_name: &String) -> bool {
  var_name.chars().next().unwrap().is_uppercase()
} 

// Convert a symbol into a wildcard by prepending a '?' to it
pub fn to_wildcard(s: &Symbol) -> Var {
  format!("?{}", s).parse().unwrap()
}

pub fn has_guard_wildcards(p: &Pat) -> bool {
  p.vars().iter().any(|v| v.to_string().starts_with(format!("?{}", GUARD_PREFIX).as_str()))
}

// Convert e into a pattern by replacing all symbols where is_var holds with wildcards
pub fn to_pattern<'a, P>(e: &'a Expr, is_var: P) -> Pat
where P: Fn(&'a Symbol) -> bool
{
  let mut pattern_ast = PatternAst::default();
  for n in e.as_ref() {
    if is_var(&n.op) {     
      pattern_ast.add(ENodeOrVar::Var(to_wildcard(&n.op)));
    } else {
      pattern_ast.add(ENodeOrVar::ENode(n.clone()));
    }
  }
  Pattern::from(pattern_ast)
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