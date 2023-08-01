use egg::*;
use indexmap::IndexMap;
use itertools::{EitherOrBoth, Itertools};
use std::collections::HashMap;
use std::str::FromStr;
use symbolic_expressions::Sexp;

use crate::ast::{Context, Defns, Env, Expr, Type};
use crate::config::CONFIG;
use crate::goal::{ProofState, ProofTerm};

/// Constants from (Liquid)Haskell
const EQUALS: &str = "=";
const LH_EQUALS: &str = "==.";
const USING_LEMMA: &str = "?";
const AND_THEN: &str = "***";
const QED: &str = "QED";
const TAB_WIDTH: usize = 2;
const PROOF: &str = "Proof";
const DATA: &str = "data";
const WHERE: &str = "where";
const MODULE: &str = "module";

const PRAGMA_GADT_SYNTAX: &str = "{-# LANGUAGE GADTSyntax #-}";
const PRAGMA_LH_REFLECTION: &str = "{-@ LIQUID \"--reflection\" @-}";
const PRAGMA_LH_PLE: &str = "{-@ LIQUID \"--ple\" @-}";
const IMPORT_LH_EQUATIONAL: &str = "import Language.Haskell.Liquid.Equational";

const LH_ANNOT_BEGIN: &str = "{-@";
const LH_ANNOT_END: &str = "@-}";
const LH_REFLECT: &str = "reflect";
const COMMENT: &str = "--";
// const HAS_TYPE: &str = "::";
// For adding nice spacing.
const JOINING_HAS_TYPE: &str = " :: ";
const JOINING_ARROW: &str = " -> ";

/// Constants from cyclegg
const APPLY: &str = "$";
const ARROW: &str = "->";
const FORWARD_ARROW: &str = "=>";
const BACKWARD_ARROW: &str = "<=";
const IH_EQUALITY_PREFIX: &str = "ih-equality-";
const LEMMA_PREFIX: &str = "lemma-";

/// A rewrite can be forward or backward, this specifies which direction it
/// goes.
enum RwDirection {
  Forward,
  Backward,
}

pub fn explain_top(
  goal: String,
  state: &mut ProofState,
  lhs: Expr,
  rhs: Expr,
  params: Vec<String>,
  top_level_vars: HashMap<Symbol, Type>,
  defns: Defns,
  env: Env,
  global_context: Context,
) -> String {
  let mut str_explanation = String::new();

  // Haskell pragmas
  str_explanation.push_str(PRAGMA_GADT_SYNTAX);
  str_explanation.push('\n');
  str_explanation.push_str(PRAGMA_LH_REFLECTION);
  str_explanation.push('\n');
  str_explanation.push_str(PRAGMA_LH_PLE);
  str_explanation.push('\n');
  str_explanation.push('\n');

  // Haskell module declaration + imports
  str_explanation.push_str(MODULE);
  str_explanation.push(' ');
  // Some hacky junk to capitalize the first character of the goal.
  let mut goal_chars = goal.chars();
  let goal_first_char = goal_chars.next().unwrap();
  str_explanation.push(goal_first_char.to_ascii_uppercase());
  goal_chars.for_each(|c| str_explanation.push(c));
  str_explanation.push(' ');
  str_explanation.push_str(WHERE);
  str_explanation.push('\n');
  str_explanation.push_str(IMPORT_LH_EQUATIONAL);
  str_explanation.push('\n');
  str_explanation.push('\n');

  // Haskell data declarations
  str_explanation.push_str(&add_data_definitions(&env, &global_context));

  // Haskell definitions
  str_explanation.push_str(&add_definitions(&defns, &global_context));

  // (arg name, arg type), to be used in creating the type.
  let args: Vec<(String, String)> = params
    .into_iter()
    .map(|param| {
      (
        param.clone(),
        convert_ty(&top_level_vars[&Symbol::from(&param)].repr),
      )
    })
    .collect();
  // println!("{:?}", args);

  // LH type
  str_explanation.push_str(LH_ANNOT_BEGIN);
  str_explanation.push(' ');
  str_explanation.push_str(&goal);
  str_explanation.push_str(JOINING_HAS_TYPE);
  // Join with arrows each of the arguments
  let args_str = args
    .iter()
    .map(|(arg_name, arg_ty)| format!("{}: {}", arg_name, arg_ty))
    .collect::<Vec<String>>()
    .join(JOINING_ARROW);
  str_explanation.push_str(&args_str);
  // Refined type of the proof
  let proof_str = format!("{{ {} = {} }}", lhs, rhs);
  str_explanation.push_str(JOINING_ARROW);
  str_explanation.push_str(&proof_str);
  str_explanation.push(' ');
  str_explanation.push_str(LH_ANNOT_END);
  str_explanation.push('\n');

  // Haskell type
  str_explanation.push_str(&goal);
  str_explanation.push_str(JOINING_HAS_TYPE);
  // Same deal as with the LH type but now we just include the types
  let arg_tys_str = args
    .iter()
    .map(|(_, arg_ty)| arg_ty.to_string())
    .collect::<Vec<String>>()
    .join(JOINING_ARROW);
  str_explanation.push_str(&arg_tys_str);
  if !args.is_empty() {
    str_explanation.push_str(JOINING_ARROW);
  }
  // This time we just use the Proof type
  str_explanation.push_str(&PROOF);
  str_explanation.push('\n');

  // Haskell function definition
  str_explanation.push_str(&goal);
  str_explanation.push(' ');
  // Now we include just the arguments and separate by spaces
  let arg_names_str = args
    .iter()
    .map(|(arg_name, _)| arg_name.to_string())
    .collect::<Vec<String>>()
    .join(" ");
  str_explanation.push_str(&arg_names_str);
  if !args.is_empty() {
    str_explanation.push(' ');
  }
  str_explanation.push_str(&EQUALS);
  str_explanation.push('\n');

  // Finally, we can do the proof explanation
  let proof_exp = explain_proof(1, goal.clone(), state, &goal);
  str_explanation.push_str(&proof_exp);
  str_explanation
}

fn add_data_definitions(env: &Env, global_context: &Context) -> String {
  let mut data_defns_str = String::new();

  // The definition will look like
  //
  // data List a where
  //   Nil :: List a
  //   Cons :: a -> List a -> List a
  //
  // We will use GADTSyntax for convenience
  for (datatype, (type_vars, constrs)) in env.iter() {
    // data DATATYPE where
    data_defns_str.push_str(DATA);
    data_defns_str.push(' ');
    data_defns_str.push_str(&datatype.to_string());
    data_defns_str.push(' ');
    if !type_vars.is_empty() {
      data_defns_str.push_str(&type_vars.join(" "));
      data_defns_str.push(' ');
    }
    data_defns_str.push_str(WHERE);
    data_defns_str.push('\n');

    // CONSTRUCTOR :: CONSTRUCTOR_TYPE
    for constr in constrs {
      add_indentation(&mut data_defns_str, 1);
      data_defns_str.push_str(&constr.to_string());
      data_defns_str.push_str(JOINING_HAS_TYPE);
      data_defns_str.push_str(&convert_ty(&global_context[&constr].repr));
      data_defns_str.push('\n');
    }
    data_defns_str.push('\n');
  }

  data_defns_str
}

fn add_definitions(defns: &Defns, global_context: &Context) -> String {
  let mut defns_str = String::new();

  // The definition will look like
  //
  // {-@ reflect listLen @-}
  // listLen :: List a -> Natural
  // listLen Nil = Z
  // listLen (Cons x xs) = S (listLen xs)
  for (name, cases) in defns.iter() {
    // {-@ reflect DEFN_NAME @-}
    defns_str.push_str(LH_ANNOT_BEGIN);
    defns_str.push(' ');
    defns_str.push_str(LH_REFLECT);
    defns_str.push(' ');
    defns_str.push_str(name);
    defns_str.push(' ');
    defns_str.push_str(LH_ANNOT_END);
    defns_str.push('\n');

    // DEFN_NAME :: DEFN_TYPE
    defns_str.push_str(name);
    defns_str.push_str(JOINING_HAS_TYPE);
    // Hacky conversion to symbol to extract from the global context
    defns_str.push_str(&convert_ty(
      &global_context[&Symbol::from_str(name).unwrap()].repr,
    ));
    defns_str.push('\n');

    for (args, value) in cases.iter() {
      defns_str.push_str(name);
      defns_str.push(' ');
      // This match is necessary to strip the parens
      match fix_vars(args) {
        Sexp::Empty => {}
        Sexp::String(arg) => {
          defns_str.push_str(&arg);
          defns_str.push(' ');
        }
        Sexp::List(args) => {
          defns_str.push_str(&args.iter().map(|arg| arg.to_string()).join(" "));
          defns_str.push(' ');
        }
      };
      defns_str.push_str(EQUALS);
      defns_str.push(' ');
      defns_str.push_str(&fix_vars(value).to_string());
      defns_str.push('\n');
    }
    defns_str.push('\n');
  }

  defns_str
}

fn explain_proof(
  depth: usize,
  goal: String,
  state: &mut ProofState,
  top_goal_name: &String,
) -> String {
  // If it's not in the proof tree, it must be a leaf.
  if !state.proof.contains_key(&goal) {
    // The explanation should be in solved_goal_explanations. If it isn't,
    // we must be trying to explain an incomplete proof which is an error.
    return explain_goal(
      depth,
      state.solved_goal_explanations.get_mut(&goal).unwrap(),
      top_goal_name,
    );
  }
  // Need to clone to avoid borrowing... unfortunately this is all because we need
  // a mutable reference to the explanations for some annoying reason
  let proof_term = state.proof.get(&goal).unwrap().clone();
  let mut str_explanation = String::new();
  let mut proof_depth = depth;
  let mut case_depth = depth + 1;
  if let ProofTerm::ITESplit(var, condition, _) = &proof_term {
    add_indentation(&mut str_explanation, proof_depth);
    str_explanation.push_str(&format!("let {} = {} in", var, condition));
    str_explanation.push('\n');
    case_depth += 1;
    proof_depth += 1;
  };
  match &proof_term {
    ProofTerm::CaseSplit(var, cases) | ProofTerm::ITESplit(var, _, cases) => {
      add_indentation(&mut str_explanation, proof_depth);
      str_explanation.push_str(&format!("case {} of", var));
      str_explanation.push('\n');
      for (case_constr, case_goal) in cases {
        add_indentation(&mut str_explanation, case_depth);
        str_explanation.push_str(&format!("{} ->", case_constr));
        str_explanation.push('\n');
        // Recursively explain the proof
        str_explanation.push_str(&explain_proof(
          case_depth + 1,
          case_goal.clone(),
          state,
          &top_goal_name,
        ));
      }
      str_explanation
    }
  }
}

fn explain_goal(
  depth: usize,
  explanation: &mut Explanation<SymbolLang>,
  top_goal_name: &String,
) -> String {
  // TODO: Add lemma justification with USING_LEMMA
  let mut str_explanation: String = String::new();
  let flat_terms = explanation.make_flat_explanation();
  let next_flat_term_iter = flat_terms.iter().skip(1);
  let flat_term_and_next = flat_terms.into_iter().zip_longest(next_flat_term_iter);
  // Render each of the terms in the explanation
  let flat_strings: Vec<String> = flat_term_and_next
    .map(|flat_term_and_next| {
      let (flat_term, next_term_opt) = match flat_term_and_next {
        EitherOrBoth::Both(flat_term, next_term) => (flat_term, Some(next_term)),
        EitherOrBoth::Left(flat_term) => (flat_term, None),
        EitherOrBoth::Right(_) => {
          unreachable!("next_flat_term_iter somehow is longer than flat_term_iter")
        }
      };
      let mut str = String::new();
      if CONFIG.verbose_proofs {
        if let Some((rule_name, rw_dir)) = &extract_rule_name(flat_term) {
          add_indentation(&mut str, depth);
          str.push_str(COMMENT);
          str.push(' ');
          if let RwDirection::Backward = rw_dir {
            str.push_str(BACKWARD_ARROW);
            str.push(' ');
          }
          str.push_str(&rule_name);
          if let RwDirection::Forward = rw_dir {
            str.push(' ');
            str.push_str(FORWARD_ARROW);
          }
          str.push('\n')
        }
      }
      add_indentation(&mut str, depth);
      str.push_str(&flat_term_to_sexp(flat_term).to_string());
      if let Some(next_term) = next_term_opt {
        // We don't care about the direction of the rewrite because lemmas
        // and the IH prove equalities which are bidirectional.
        if let Some((rule_name, rw_dir)) = &extract_rule_name(next_term) {
          if rule_name.starts_with(IH_EQUALITY_PREFIX) {
            str.push('\n');
            let args = extract_ih_arguments(rule_name);
            add_indentation(&mut str, depth);
            str.push_str(USING_LEMMA);
            str.push(' ');
            str.push_str(top_goal_name);
            str.push(' ');
            str.push_str(&args.join(" "));
          } else if rule_name.starts_with(LEMMA_PREFIX) {
            // println!("extracting lemma from {} {} {}", rule_name, flat_term, next_term);
            str.push_str(&extract_lemma_invocation(
              rule_name, rw_dir, flat_term, next_term, depth,
            ));
          }
        }
      }
      str
    })
    .collect();
  // Construct a joiner that intersperses newlines and properly spaced
  // LH_EQUALS operators.
  let mut joiner = "\n".to_string();
  add_indentation(&mut joiner, depth);
  joiner.push_str(LH_EQUALS);
  joiner.push('\n');

  // The bulk of our proof is the individual terms joined by LH_EQUALS.
  str_explanation.push_str(&flat_strings.join(&joiner));
  str_explanation.push('\n');
  add_indentation(&mut str_explanation, depth);
  // This is just required by LH to finish it.
  str_explanation.push_str(AND_THEN);
  str_explanation.push('\n');
  add_indentation(&mut str_explanation, depth);
  str_explanation.push_str(QED);
  str_explanation.push('\n');
  str_explanation
}

fn extract_lemma_invocation(
  rule_str: &String,
  rw_dir: &RwDirection,
  curr_term: &FlatTerm<SymbolLang>,
  next_term: &FlatTerm<SymbolLang>,
  depth: usize,
) -> String {
  let mut lemma_str = String::new();
  let mut rewrite_pos: Vec<i32> = vec![];
  let trace = find_rewritten_term(&mut rewrite_pos, next_term).unwrap();
  let rewritten_to = get_flat_term_from_trace(&trace, &next_term);
  let rewritten_from = get_flat_term_from_trace(&trace, &curr_term);
  let lemma: Vec<&str> = rule_str.split(LEMMA_PREFIX).collect::<Vec<&str>>()[1]
    .split(EQUALS)
    .collect();

  let mut lhsmap = map_variables(lemma[0], &flat_term_to_sexp(&rewritten_from).to_string());
  let rhsmap = map_variables(lemma[1], &flat_term_to_sexp(&rewritten_to).to_string());

  match rw_dir {
    RwDirection::Backward => {
      assert!(lhsmap
        .iter()
        .all(|(key, value)| rhsmap.get(key) == Some(value)))
    }
    RwDirection::Forward => {
      assert!(rhsmap
        .iter()
        .all(|(key, value)| lhsmap.get(key) == Some(value)))
    }
  }

  // take the union of both maps
  lhsmap.extend(rhsmap);

  lemma_str.push('\n');
  add_indentation(&mut lemma_str, depth);
  lemma_str.push_str(USING_LEMMA);
  lemma_str.push(' ');
  lemma_str.push_str(&rule_str);

  // add the lemma arguments
  for (_, value) in lhsmap {
    lemma_str.push_str(&format!(" {}", value));
  }

  lemma_str
}

fn add_indentation(s: &mut String, depth: usize) {
  s.push_str(&" ".repeat(depth * TAB_WIDTH));
}

fn flat_term_to_sexp(flat_term: &FlatTerm<SymbolLang>) -> Sexp {
  // This is a leaf
  if flat_term.node.children.is_empty() {
    convert_op(flat_term.node.op)
  // This is an interior node
  } else {
    let mut child_sexps: Vec<Sexp> = vec![convert_op(flat_term.node.op)];
    for child in &flat_term.children {
      child_sexps.push(flat_term_to_sexp(child));
    }
    Sexp::List(child_sexps)
  }
}

fn extract_rule_name(flat_term: &FlatTerm<SymbolLang>) -> Option<(String, RwDirection)> {
  let forward = flat_term
    .forward_rule
    .map(|rule| (rule.to_string(), RwDirection::Forward));
  let backward = flat_term
    .backward_rule
    .map(|rule| (rule.to_string(), RwDirection::Backward));
  // Find the first Some
  let rule_from_child = flat_term
    .children
    .iter()
    .map(extract_rule_name)
    .find(Option::is_some)
    .flatten();
  forward.or(backward).or(rule_from_child)
}

fn fix_vars(sexp: &Sexp) -> Sexp {
  match sexp {
    Sexp::Empty => Sexp::Empty,
    Sexp::String(s) => {
      let mut new_s = String::new();
      let mut s_chars = s.chars();
      if let Some(c) = s_chars.next() {
        match c {
          // Skip a question mark prefix on a var
          '?' => {}
          _ => new_s.push(c),
        };
      }
      // Add the rest
      new_s.push_str(s_chars.as_str());
      Sexp::String(new_s)
    }
    Sexp::List(children) => Sexp::List(children.iter().map(fix_vars).collect()),
  }
}

fn convert_op(op: Symbol) -> Sexp {
  let op_str = op.to_string();
  // Special case for converting `$`, which is used internally in cyclegg for
  // partial application, to the corresponding prefix operator `($)` in
  // Haskell.
  if op_str == APPLY {
    // This is a really ugly hack to wrap `$` in parens.
    Sexp::List(vec![Sexp::String(op_str)])
  } else {
    Sexp::String(op_str)
  }
}

/// Basically the same as ty.repr.to_string() but we make arrows infix
fn convert_ty(ty: &Sexp) -> String {
  match ty {
    Sexp::String(str) => str.clone(),
    Sexp::List(children) => {
      // Handle the arrow case, making it infix
      if children.len() == 3 {
        if let Sexp::String(op) = &children[0] {
          if *op == ARROW {
            if let Sexp::List(args) = children[1].clone() {
              let mut arg_tys: Vec<String> = args.iter().map(convert_ty).collect();
              let return_ty = convert_ty(&children[2]);
              arg_tys.push(return_ty);
              return format!("({})", arg_tys.join(JOINING_ARROW));
            } else {
              return format!(
                "({} {} {})",
                convert_ty(&children[1]),
                ARROW,
                convert_ty(&children[2])
              );
            }
          }
        }
      }
      let converted: String = children
        .into_iter()
        .map(convert_ty)
        .collect::<Vec<String>>()
        .join(" ");
      format!("({})", converted)
    }
    Sexp::Empty => String::new(),
  }
}

fn extract_ih_arguments(rule_name: &String) -> Vec<String> {
  rule_name
    .strip_prefix(IH_EQUALITY_PREFIX)
    .unwrap()
    .split(',')
    .into_iter()
    .map(|pair| {
      // println!("{}", pair);
      let args: Vec<&str> = pair.split('=').into_iter().collect();
      // This should just be x=(Constructor c1 c2 c3)
      assert_eq!(args.len(), 2);
      args[1].to_string()
    })
    .collect()
}
/// Given a FlatTerm, locates the subterm that was rewritten by looking for a backward / forward rule
/// and returns a trace of indices to that term.
fn find_rewritten_term(trace: &mut Vec<i32>, flat_term: &FlatTerm<SymbolLang>) -> Option<Vec<i32>> {
  if flat_term.backward_rule.is_some() || flat_term.forward_rule.is_some() {
    Some(trace.to_vec())
  } else {
    for (i, child) in flat_term.children.iter().enumerate() {
      if child.has_rewrite_backward() || child.has_rewrite_forward() {
        trace.push(i as i32);
        return find_rewritten_term(trace, child);
      }
    }
    None
  }
}

fn get_flat_term_from_trace(
  trace: &Vec<i32>,
  flat_term: &FlatTerm<SymbolLang>,
) -> FlatTerm<SymbolLang> {
  let mut current_flat_term = flat_term;
  for i in trace {
    current_flat_term = &current_flat_term.children[*i as usize];
  }
  current_flat_term.clone()
}

/// Given two strings, s1 and s2, where s1 is a pattern and s2 is a string
/// returns a map from the variables in s1 to the corresponding substrings in s2.
fn map_variables(s1: &str, s2: &str) -> IndexMap<String, String> {
  let mut result_map = IndexMap::new();
  // let mut stack = Vec::new();
  let mut s1_iter = s1.chars().peekable();
  let mut s2_iter = s2.chars().peekable();

  while let Some(&c1) = s1_iter.peek() {
    let c2 = s2_iter.peek().unwrap();
    match c1 {
      '?' => {
        let mut temp_str = String::new();
        let mut nested_paren_count = 0;

        while let Some(&next_char) = s2_iter.peek() {
          match next_char {
            '(' if nested_paren_count > 0 => {
              temp_str.push(next_char);
              nested_paren_count += 1;
            }
            '(' => nested_paren_count += 1,
            ')' if nested_paren_count > 1 => {
              temp_str.push(next_char);
              nested_paren_count -= 1;
            }
            ')' => break,
            ' ' if nested_paren_count == 0 => break,
            _ => temp_str.push(next_char),
          }
          s2_iter.next();
        }

        if !temp_str.is_empty() {
          let mut extracted_str = String::new();
          s1_iter.next();
          while let Some(&next_char) = s1_iter.peek() {
            if next_char.is_whitespace() || next_char == ')' {
              break;
            }
            extracted_str.push(next_char);
            s1_iter.next();
          }

          s1_iter.next();

          result_map.insert(extracted_str, temp_str);
        }
      }
      _ if c1 == *c2 => {
        s1_iter.next();
      }
      _ => {
        break;
      }
    }
    s2_iter.next();
  }

  result_map
}

// TODO: Lemma generation.
// How to do lemmas:
// 1.
// 2. Anti-unficiation between terms to figure out:
//   1. What lemma was used?
//   2. What were its arguments? Specifically, for each variable
//      used in the lemma x, what term t is x mapped to in this invocation?
// 3. (If the lemma is the base induction hypothesis, simply call
//    it. -- this is probably unnecessary and is generalized by the following method).
//    Otherwise, look up the explanation for how its LHS relates to the goal
//    LHS and its RHS relates to the goal RHS. Use the argument map to instantiate
//    the explanations with concrete arguments. Inline the lemma as follows:
//    (LHS ==. proof of LHS -> goal LHS ? inductionHypothesis ==. proof of goal RHS -> RHS ==. RHS)
//    it might require some thinking to determine the relationship between the lemma's arguments
//    and the arguments to the induction hypothesis.
