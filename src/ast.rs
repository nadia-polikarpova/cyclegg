use symbolic_expressions::{Sexp, SexpError};
use std::{str::FromStr, fmt::Display, collections::HashMap};
use egg::{*};

#[derive(Debug, Clone)]
pub struct Type { 
  repr: Sexp
}

impl Type {
  pub fn new(repr: Sexp) -> Self {
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
pub type Pat = Pattern<SymbolLang>;

pub fn var_depth(var_name: &str) -> usize {
  var_name.matches("-").count()
}

pub fn is_descendant(var_name: &String, ancestor_name: &String) -> bool {
  var_name.starts_with(ancestor_name) && var_name.len() > ancestor_name.len()
}

// Convert a symbol into a wildcard by prepending a '?' to it
pub fn to_wildcard(s: &Symbol) -> Var {
  format!("?{}", s).parse().unwrap()
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
