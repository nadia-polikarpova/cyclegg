use egg::*;
use lazy_static::lazy_static;

use std::{collections::HashMap, fmt::Display, str::FromStr};
use symbolic_expressions::{Sexp, SexpError};

use crate::config::CONFIG;

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
  pub repr: Sexp,
}

impl Type {
  pub fn new(repr: Sexp) -> Self {
    Self { repr }
  }

  /// If this type is a datatype, returns its name and otherwise return error.
  pub fn datatype(&self) -> Result<&String, SexpError> {
    match &self.repr {
      Sexp::String(s) => Ok(s), // This type is a D
      Sexp::List(xs) => {
        // This type is a type constructor application
        match xs[0].string()?.as_str() {
          ARROW => Err(SexpError::Other(
            "expected datatype and got arrow".to_string(),
          )),
          _ => xs[0].string(),
        }
      }
      _ => panic!("arity: type is empty"),
    }
  }

  /// Split a type into arguments and return value
  /// (arguments are empty if the type is not an arrow)
  pub fn args_ret(&self) -> (Vec<Type>, Type) {
    match &self.repr {
      Sexp::String(_) => (vec![], self.clone()), // This type is a D
      Sexp::List(xs) => {
        // This is a type constructor application
        match xs[0].string().unwrap().as_str() {
          ARROW => {
            let args = xs[1]
              .list()
              .unwrap()
              .iter()
              .map(|x| Type::new(x.clone()))
              .collect();
            (args, Type::new(xs[2].clone()))
          }
          _ => (vec![], self.clone()),
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

pub fn mangle_name(name: &str) -> String {
  // We never mangle symbols. The cases we have are:
  //   $  (function application)
  //   -> (type arrows)
  //   ?x (variable names)
  if name
    .chars()
    .next()
    .map(|c| !c.is_alphabetic())
    .unwrap_or(true)
  {
    return name.to_string();
  }
  if CONFIG.mangle_names {
    if name.chars().next().unwrap().is_ascii_uppercase() {
      format!("Cyclegg_{}", name)
    } else {
      format!("cyclegg_{}", name)
    }
  } else {
    name.to_string()
  }
}

pub fn mangle_sexp(sexp: &Sexp) -> Sexp {
  map_sexp(|elem| Sexp::String(mangle_name(elem)), sexp)
}

// Constants
lazy_static! {
  pub static ref BOOL_TYPE: String = mangle_name("Bool");
  pub static ref ITE: String = mangle_name("ite");
  pub static ref TRUE: String = mangle_name("True");
  pub static ref FALSE: String = mangle_name("False");
}
pub const ARROW: &str = "->";
pub const APPLY: &str = "$";
pub const GUARD_PREFIX: &str = "g_";

pub fn var_depth(var_name: &str) -> usize {
  var_name.matches('_').count()
}

pub fn is_descendant(var_name: &str, ancestor_name: &str) -> bool {
  var_name.starts_with(ancestor_name) && var_name.len() > ancestor_name.len()
}

#[derive(PartialEq, PartialOrd, Ord, Eq, Debug)]
pub enum StructuralComparison {
  /// Strictly less than
  LT,
  /// Not greater than
  LE,
  /// Don't know - we reject these
  Incomparable,
}

pub fn map_sexp<F>(f: F, sexp: &Sexp) -> Sexp
where
  F: Copy + Fn(&str) -> Sexp,
{
  match sexp {
    Sexp::Empty => Sexp::Empty,
    Sexp::String(str) => f(str),
    Sexp::List(list) => Sexp::List(list.iter().map(|s| map_sexp(f, s)).collect()),
  }
}

pub fn contains_function(sexp: &Sexp) -> bool {
  match sexp {
    Sexp::List(list) => {
      if !list.is_empty() {
        if let Sexp::String(str) = &list[0] {
          if !is_constructor(str) {
            return true;
          }
        }
      }
      list.iter().any(contains_function)
    }
    _ => false,
  }
}

fn starts_uppercase(string: &str) -> bool {
  string
    .chars()
    .next()
    .map(|c| c.is_ascii_uppercase())
    .unwrap_or(false)
}

fn find_instantiations_helper(
  proto: &Sexp,
  actual: &Sexp,
  instantiations_map: &mut HashMap<String, Sexp>,
) {
  match (proto, actual) {
    (Sexp::Empty, _) | (_, Sexp::Empty) => unreachable!(),
    (Sexp::String(proto_str), actual_sexp) => {
      if starts_uppercase(proto_str) {
        // It's a constant in the proto, which means it should be a constant
        // (i.e. a string with the same value) in the actual
        assert!(actual_sexp.is_string());
        assert_eq!(proto_str, actual_sexp.string().unwrap());
      } else {
        // Otherwise, it's a type variable so we can instantiate it
        let instantiation = actual_sexp.clone();
        if let Some(existing_instantiation) = instantiations_map.get(proto_str) {
          // Past instantiations must agree
          assert_eq!(&instantiation, existing_instantiation);
        } else {
          instantiations_map.insert(proto_str.clone(), instantiation);
        }
      }
    }
    (Sexp::List(proto_list), actual_sexp) => {
      // The actual must match the proto
      assert!(actual_sexp.is_list());
      let actual_list = actual_sexp.list().unwrap();
      // Including lengths.
      assert_eq!(proto_list.len(), actual_list.len());
      proto_list
        .iter()
        .zip(actual_list.iter())
        .for_each(|(sub_proto, sub_actual)| {
          find_instantiations_helper(sub_proto, sub_actual, instantiations_map)
        });
    }
  }
}

/// Find the instantiations of proto needed to obtain actual
///
/// ex: proto  = (Pair a (Pair b b))
///     actual = (Pair (List x) (Pair Nat Nat))
///
///     instantiations = {a: (List x), b: Nat}
///
/// actual is assumed to be a valid instantiation of proto.
pub fn find_instantiations(proto: &Type, actual: &Type) -> HashMap<String, Sexp> {
  let mut instantiations = HashMap::new();
  find_instantiations_helper(&proto.repr, &actual.repr, &mut instantiations);
  instantiations
}

/// Resolves a Sexp using instantiations, but does not recursively resolve it.
///
/// Ex: sexp:           (List a)
///     instantiations: {a: (List b), b: Nat}
///
///     returns:        (List b)
pub fn resolve_sexp(sexp: &Sexp, instantiations: &HashMap<String, Sexp>) -> Sexp {
  map_sexp(
    |v| {
      instantiations
        .get(v)
        .cloned()
        .unwrap_or_else(|| Sexp::String(v.to_string()))
    },
    sexp,
  )
}

/// Recursively resolves a Sexp using instantiations.
///
/// Ex: sexp:           (List a)
///     instantiations: {a: (List b), b: Nat}
///
///     returns:        (List Nat)
pub fn recursively_resolve_sexp(sexp: &Sexp, instantiations: &HashMap<String, Sexp>) -> Sexp {
  map_sexp(|v| recursively_resolve_variable(v, instantiations), sexp)
}

/// Requires that there are no cycles in instantiations.
pub fn recursively_resolve_variable(var: &str, instantiations: &HashMap<String, Sexp>) -> Sexp {
  instantiations
    .get(var)
    .map(|sexp| map_sexp(|v| recursively_resolve_variable(v, instantiations), sexp))
    .unwrap_or_else(|| Sexp::String(var.to_string()))
}

// FIXME: we should track down where these singletons are coming from and
// prevent them instead of fixing them
pub fn fix_singletons(sexp: Sexp) -> Sexp {
  match sexp {
    Sexp::List(list) => {
      if list.len() == 1 {
        fix_singletons(list[0].to_owned())
      } else {
        Sexp::List(list.into_iter().map(fix_singletons).collect())
      }
    }
    _ => sexp,
  }
}

fn structural_comparison_list(child: &Sexp, ancestors: &[Sexp]) -> StructuralComparison {
  let mut ancestor_comparison_results = ancestors
    .iter()
    .map(|ancestor_elem| structural_comparision(child, ancestor_elem));
  // Ignore the constructor
  ancestor_comparison_results.next();
  for ancestor_comparison_result in ancestor_comparison_results {
    // If any part is LE/LT, then it is LT because there is additional
    // structure on the RHS (the constructor).
    if ancestor_comparison_result == StructuralComparison::LE
      || ancestor_comparison_result == StructuralComparison::LT
    {
      return StructuralComparison::LT;
    }
  }
  StructuralComparison::Incomparable
}

pub fn structural_comparision(child: &Sexp, ancestor: &Sexp) -> StructuralComparison {
  match (child, ancestor) {
    (Sexp::String(child_name), Sexp::String(ancestor_name)) => {
      // If they are both constructors, they must match
      if is_constructor(child_name) && is_constructor(ancestor_name) {
        if child_name == ancestor_name {
          StructuralComparison::LE
        } else {
          StructuralComparison::Incomparable
        }
      }
      // If just the child is a constructor, then it is smaller
      // If they are both variables and the child is a descendent, it is smaller
      else if is_constructor(child_name) || is_descendant(child_name, ancestor_name) {
        StructuralComparison::LT
      } else if !is_constructor(ancestor_name) && child_name == ancestor_name {
        StructuralComparison::LE
      }
      // Otherwise, we don't know how to compare them
      else {
        StructuralComparison::Incomparable
      }
    }
    (Sexp::List(child_list), Sexp::List(ancestor_list)) => {
      // Try to compare the two as if they matched
      let mut result = StructuralComparison::LE;
      let elem_comparison_results = child_list
        .iter()
        .zip(ancestor_list.iter())
        .map(|(child_elem, ancestor_elem)| structural_comparision(child_elem, ancestor_elem));
      for elem_comparison_result in elem_comparison_results {
        // If any part is incomparable, the entire thing is.
        if elem_comparison_result == StructuralComparison::Incomparable {
          result = StructuralComparison::Incomparable;
          break;
        }
        result = std::cmp::min(result, elem_comparison_result);
      }
      // If that fails, try to compare the two as if the child is in any
      // substructure.
      if result != StructuralComparison::LT {
        result = std::cmp::min(result, structural_comparison_list(child, ancestor_list))
      }
      result
    }
    (Sexp::Empty, Sexp::Empty) => StructuralComparison::LE,
    (Sexp::String(_), Sexp::List(ancestor_list)) => {
      structural_comparison_list(child, ancestor_list)
    }
    // Consider the (List, String) case?
    // Does (Empty, _) need to return LE/LT?
    _ => StructuralComparison::Incomparable,
  }
}

pub fn is_constructor(var_name: &str) -> bool {
  var_name.chars().next().unwrap().is_uppercase()
}

// Convert a symbol into a wildcard by prepending a '?' to it
pub fn to_wildcard(s: &Symbol) -> Var {
  format!("?{}", s).parse().unwrap()
}

// Does this pattern contain a wildcard derived from a guard variable?
// If so, we don't want to use it in a lemma because it cannot possibly be applied in a useful way.
pub fn has_guard_wildcards(p: &Pat) -> bool {
  p.vars().iter().any(|v| {
    v.to_string()
      .starts_with(format!("?{}", GUARD_PREFIX).as_str())
  })
}

// Convert e into a pattern by replacing all symbols where is_var holds with wildcards
pub fn to_pattern<'a, P>(e: &'a Expr, is_var: P) -> Pat
where
  P: Fn(&'a Symbol) -> bool,
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
pub type Env = HashMap<Symbol, (Vec<String>, Vec<Symbol>)>;

// Type context
pub type Context = HashMap<Symbol, Type>;

// Function definitions
pub type Defns = HashMap<String, Vec<(Sexp, Sexp)>>;

pub fn mk_context(descr: &[(&str, &str)]) -> Context {
  let mut ctx = Context::new();
  for (name, ty) in descr {
    ctx.insert(Symbol::from(*name), ty.parse().unwrap());
  }
  ctx
}

// CK: Function is unused and I didn't feel like extending it to account for the change from
//     Env = HashMap<Symbol, Vec<Symbol>>
// to
//     Env = HashMap<Symbol, (Vec<String>, Vec<Symbol>)>
//
// pub fn mk_env(descr: &[(&str, &str)]) -> Env {
//   let mut env = Env::new();
//   for (name, cons) in descr {
//     env.insert(Symbol::from(*name), cons.split_whitespace().map(|s| Symbol::from(s)).collect());
//   }
//   env
// }
