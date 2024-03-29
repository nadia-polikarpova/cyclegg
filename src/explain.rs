use egg::*;
use indexmap::IndexMap;
use itertools::{EitherOrBoth, Itertools};
use std::collections::HashMap;
use std::str::FromStr;
use symbolic_expressions::Sexp;

use crate::ast::{map_sexp, to_pattern, Context, Defns, Env, Type};
use crate::config::CONFIG;
use crate::goal::{Equation, ProofState, ProofTerm, IH_EQUALITY_PREFIX, LEMMA_PREFIX};

/// Constants from (Liquid)Haskell
const EQUALS: &str = "=";
const UNIT: &str = "()";
const LH_EQUALS: &str = "==.";
const LH_USING_LEMMA: &str = "?";
const LH_FINISH_PROOF: &str = "***";
const LH_QED: &str = "QED";
const LH_PROOF: &str = "Proof";
const DATA: &str = "data";
const WHERE: &str = "where";
const MODULE: &str = "module";
const UNDEFINED: &str = "undefined";
const TAB_WIDTH: usize = 2;

const PRAGMA_GADT_SYNTAX: &str = "{-# LANGUAGE GADTSyntax #-}";
const PRAGMA_LH_REFLECTION: &str = "{-@ LIQUID \"--reflection\" @-}";
const PRAGMA_LH_PLE: &str = "{-@ LIQUID \"--ple\" @-}";
const IMPORT_LH_EQUATIONAL: &str = "import Language.Haskell.Liquid.Equational";

const LH_ANNOT_BEGIN: &str = "{-@";
const LH_ANNOT_END: &str = "@-}";
const LH_AUTOSIZE: &str = "autosize";
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

/// A rewrite can be forward or backward, this specifies which direction it
/// goes.
enum RwDirection {
  Forward,
  Backward,
}

#[derive(Debug)]
struct LemmaInfo {
  name: String,
  // (param_name, param_type)
  params: Vec<(String, String)>,
  lhs: Sexp,
  rhs: Sexp,
}

/// Capitalizes each part of the goal name and removes underscores.
///
/// prop_50_no_cyclic -> Prop50NoCyclic
pub fn goal_name_to_filename(goal_name: &str) -> String {
  goal_name
    .split('_')
    .into_iter()
    .map(|chunk| {
      let mut chars_iter = chunk.chars();
      let mut new_string = String::new();
      if let Some(first_char) = chars_iter.next() {
        new_string.push(first_char.to_ascii_uppercase());
      }
      new_string.extend(chars_iter);
      new_string
    })
    .collect()
}

pub fn explain_top(
  filename: &str,
  goal: &str,
  state: &mut ProofState,
  eq: &Equation,
  params: &[Symbol],
  top_level_vars: &HashMap<Symbol, Type>,
  defns: &Defns,
  env: &Env,
  global_context: &Context,
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

  // Comment explaining the file
  str_explanation.push_str(COMMENT);
  str_explanation.push(' ');
  str_explanation.push_str(goal);
  str_explanation.push_str(": ");
  str_explanation.push_str(&eq.lhs.sexp.to_string());
  str_explanation.push_str(" = ");
  str_explanation.push_str(&eq.rhs.sexp.to_string());
  str_explanation.push('\n');

  // Haskell module declaration + imports
  str_explanation.push_str(MODULE);
  str_explanation.push(' ');
  str_explanation.push_str(filename);
  str_explanation.push(' ');
  str_explanation.push_str(WHERE);
  str_explanation.push('\n');
  str_explanation.push_str(IMPORT_LH_EQUATIONAL);
  str_explanation.push('\n');
  str_explanation.push('\n');

  // Haskell data declarations
  str_explanation.push_str(&add_data_definitions(env, global_context));

  // Haskell definitions
  str_explanation.push_str(&add_definitions(defns, global_context));

  // (arg name, arg type), to be used in creating the type.
  let args: Vec<(String, String)> = params
    .iter()
    .map(|param| (param.to_string(), convert_ty(&top_level_vars[param].repr)))
    .collect();
  // println!("{:?}", args);

  // Add the types and function definition stub
  str_explanation.push_str(&add_proof_types_and_stub(
    goal,
    &eq.lhs.sexp,
    &eq.rhs.sexp,
    &args,
  ));
  str_explanation.push('\n');

  // Finally, we can do the proof explanation

  // Maps the rewrite rule string corresponding to a lemma to
  // (fresh_lemma_name, lemma_vars, lemma LHS, lemma RHS).
  // In the beginning add only the top-level inductive hypothesis.
  // TODO: still need to handle the inverted IH? (RHS => LHS)
  let mut lemma_map = HashMap::new();
  let pat_lhs: Pattern<SymbolLang> = to_pattern(&eq.lhs.expr, |v| top_level_vars.contains_key(v));
  let pat_rhs: Pattern<SymbolLang> = to_pattern(&eq.rhs.expr, |v| top_level_vars.contains_key(v));
  let lemma_info = LemmaInfo {
    name: goal.to_string(),
    params: params
      .iter()
      .map(|param| {
        let param_type = top_level_vars.get(param).unwrap();
        (param.to_string(), param_type.to_string())
      })
      .collect(),
    lhs: symbolic_expressions::parser::parse_str(&pat_lhs.to_string()).unwrap(),
    rhs: symbolic_expressions::parser::parse_str(&pat_rhs.to_string()).unwrap(),
  };
  let ih_name = format!("lemma-{}={}", pat_lhs, pat_rhs);
  lemma_map.insert(ih_name, lemma_info);

  let proof_exp = explain_proof(1, goal, state, goal, &mut lemma_map);
  str_explanation.push_str(&proof_exp);
  str_explanation.push('\n');

  for (_rule_name, lemma_info) in lemma_map.iter() {
    if lemma_info.name == goal {
      // This is the top-level IH, we don't need to add it.
      continue;
    }
    str_explanation.push_str(&add_proof_types_and_stub(
      &lemma_info.name,
      &lemma_info.lhs,
      &lemma_info.rhs,
      &lemma_info.params,
    ));
    str_explanation.push(' ');
    // TODO: add proofs
    str_explanation.push_str(UNDEFINED);
    str_explanation.push('\n');
    str_explanation.push('\n');
  }

  str_explanation
}

fn add_proof_types_and_stub(
  goal: &str,
  lhs: &Sexp,
  rhs: &Sexp,
  args: &Vec<(String, String)>,
) -> String {
  let mut str_explanation = String::new();

  // Technically we only need to fix uses of $ in the LHS/RHS, but
  // converting vars is fine too.
  let fixed_lhs = fix_value(lhs);
  let fixed_rhs = fix_value(rhs);

  // LH type
  str_explanation.push_str(LH_ANNOT_BEGIN);
  str_explanation.push(' ');
  str_explanation.push_str(goal);
  str_explanation.push_str(JOINING_HAS_TYPE);
  // Join with arrows each of the arguments
  let args_str = args
    .iter()
    .map(|(arg_name, arg_ty)| format!("{}: {}", arg_name, arg_ty))
    .collect::<Vec<String>>()
    .join(JOINING_ARROW);
  str_explanation.push_str(&args_str);
  // Refined type of the proof
  let proof_str = format!("{{ {} = {} }}", fixed_lhs, fixed_rhs);
  if !args.is_empty() {
    str_explanation.push_str(JOINING_ARROW);
  }
  str_explanation.push_str(&proof_str);
  str_explanation.push(' ');
  str_explanation.push_str(LH_ANNOT_END);
  str_explanation.push('\n');

  // Haskell type
  str_explanation.push_str(goal);
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
  str_explanation.push_str(LH_PROOF);
  str_explanation.push('\n');

  // Haskell function definition
  str_explanation.push_str(goal);
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
  str_explanation.push_str(EQUALS);

  str_explanation
}

fn add_data_definitions(env: &Env, global_context: &Context) -> String {
  let mut data_defns_str = String::new();

  // The definition will look like
  //
  // {-@ autosize List @-}
  // data List a where
  //   Nil :: List a
  //   Cons :: a -> List a -> List a
  //
  // We will use GADTSyntax for convenience
  for (datatype, (type_vars, constrs)) in env.iter() {
    // {-@ autosize DATATYPE @-}
    data_defns_str.push_str(LH_ANNOT_BEGIN);
    data_defns_str.push(' ');
    data_defns_str.push_str(LH_AUTOSIZE);
    data_defns_str.push(' ');
    data_defns_str.push_str(&datatype.to_string());
    data_defns_str.push(' ');
    data_defns_str.push_str(LH_ANNOT_END);
    data_defns_str.push('\n');
    // data DATATYPE TYPE_VARS where
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
      data_defns_str.push_str(&convert_ty(&global_context[constr].repr));
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
      defns_str.push_str(&fix_value(value).to_string());
      defns_str.push('\n');
    }
    defns_str.push('\n');
  }

  defns_str
}

fn explain_proof(
  depth: usize,
  goal: &str,
  state: &mut ProofState,
  top_goal_name: &str,
  lemma_map: &mut HashMap<String, LemmaInfo>,
) -> String {
  // If it's not in the proof tree, it must be a leaf.
  if !state.proof.contains_key(goal) {
    // The explanation should be in solved_goal_explanations. If it isn't,
    // we must be trying to explain an incomplete proof which is an error.
    return explain_goal(
      depth,
      state
        .solved_goal_explanation_and_context
        .get_mut(goal)
        .unwrap(),
      top_goal_name,
      lemma_map,
    );
  }
  // Need to clone to avoid borrowing... unfortunately this is all because we need
  // a mutable reference to the explanations for some annoying reason
  let proof_term = state.proof.get(goal).unwrap().clone();
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
          case_goal,
          state,
          top_goal_name,
          lemma_map,
        ));
      }
      str_explanation
    }
  }
}

fn explain_goal(
  depth: usize,
  (explanation, local_context): &mut (Explanation<SymbolLang>, Context),
  top_goal_name: &str,
  lemma_map: &mut HashMap<String, LemmaInfo>,
) -> String {
  let mut str_explanation: String = String::new();
  let flat_terms = explanation.make_flat_explanation();
  let next_flat_term_iter = flat_terms.iter().skip(1);
  let flat_term_and_next = flat_terms.iter().zip_longest(next_flat_term_iter);
  // Render each of the terms in the explanation.
  // The first term is the equality of the previous term and itself (rendered for CONFIG.verbose_proofs).
  // The second term is the lemma, if used (rendered always).
  // The third time is the comment string explaining the equality (rendered for CONFIG.verbose_proofs).
  let explanation_lines: Vec<(String, Option<String>, Option<String>)> = flat_term_and_next
    .map(|flat_term_and_next| {
      let (flat_term, next_term_opt) = match flat_term_and_next {
        EitherOrBoth::Both(flat_term, next_term) => (flat_term, Some(next_term)),
        EitherOrBoth::Left(flat_term) => (flat_term, None),
        EitherOrBoth::Right(_) => {
          unreachable!("next_flat_term_iter somehow is longer than flat_term_iter")
        }
      };
      let mut item = String::new();
      let comment = extract_rule_name(flat_term).map(|(rule_name, rw_dir)| {
        let mut comment_str = String::new();
        comment_str.push_str(COMMENT);
        comment_str.push(' ');
        if let RwDirection::Backward = rw_dir {
          comment_str.push_str(BACKWARD_ARROW);
          comment_str.push(' ');
        }
        comment_str.push_str(&rule_name);
        if let RwDirection::Forward = rw_dir {
          comment_str.push(' ');
          comment_str.push_str(FORWARD_ARROW);
        }
        comment_str
      });
      // These aren't necessary with PLE and generate spurious constraints so we omit them.
      if CONFIG.verbose_proofs {
        // First we convert to a sexp, then fix its operators. fix_value also
        // fixes variables which is unnecessary but won't cause harm.
        item.push_str(&fix_value(&flat_term_to_sexp(flat_term)).to_string());
      }
      let lemma = next_term_opt.and_then(|next_term| {
        // We don't care about the direction of the rewrite because lemmas
        // and the IH prove equalities which are bidirectional.
        extract_rule_name(next_term).and_then(|(rule_name, rw_dir)| {
          if rule_name.starts_with(IH_EQUALITY_PREFIX) {
            let args = extract_ih_arguments(&rule_name);
            Some(add_lemma_invocation(top_goal_name, args.iter()))
          } else if rule_name.starts_with(LEMMA_PREFIX) {
            // println!("extracting lemma from {} {} {}", rule_name, flat_term, next_term);
            Some(extract_lemma_invocation(
              &rule_name,
              &rw_dir,
              flat_term,
              next_term,
              top_goal_name,
              lemma_map,
              local_context,
            ))
          } else {
            None
          }
        })
      });
      (item, lemma, comment)
    })
    .collect();
  // if CONFIG.verbose_proofs {
  //   // Construct a joiner that intersperses newlines and properly spaced
  //   // LH_EQUALS operators.
  //   let mut joiner = "\n".to_string();
  //   add_indentation(&mut joiner, depth);
  //   joiner.push_str(LH_EQUALS);
  //   joiner.push('\n');

  //   // Individual terms joined by LH_EQUALS.
  //   str_explanation.push_str(&explanation_lines.join(&joiner));
  //   str_explanation.push('\n');
  //   add_indentation(&mut str_explanation, depth);
  //   // This is just required by LH to finish it.
  //   str_explanation.push_str(AND_THEN);
  //   str_explanation.push('\n');
  //   add_indentation(&mut str_explanation, depth);
  //   str_explanation.push_str(QED);
  //   str_explanation.push('\n');
  // } else {

  // It is a bit redundant to have two ways of emitting lines, but
  // the logic is simpler to debug.
  if CONFIG.verbose_proofs {
    for (line, (item, lemma, comment)) in explanation_lines.iter().enumerate() {
      add_comment(&mut str_explanation, comment.as_ref(), depth);
      add_indentation(&mut str_explanation, depth);
      if line > 0 {
        str_explanation.push_str(LH_EQUALS);
        str_explanation.push(' ');
      }
      str_explanation.push_str(item);
      str_explanation.push('\n');
      if let Some(lemma_str) = lemma {
        add_indentation(&mut str_explanation, depth);
        str_explanation.push_str(LH_USING_LEMMA);
        str_explanation.push(' ');
        str_explanation.push_str(lemma_str);
        str_explanation.push('\n');
      }
    }
    // There will always be at least one line of explanation, so we don't need
    // to handle the empty case.
    add_indentation(&mut str_explanation, depth);
    str_explanation.push_str(LH_FINISH_PROOF);
    str_explanation.push('\n');
    add_indentation(&mut str_explanation, depth);
    str_explanation.push_str(LH_QED);
    str_explanation.push('\n');
  } else {
    let mut is_first_lemma = true;
    for (_, lemma, comment) in explanation_lines.iter() {
      add_comment(&mut str_explanation, comment.as_ref(), depth);
      if let Some(lemma_str) = lemma {
        add_indentation(&mut str_explanation, depth);
        if !is_first_lemma {
          str_explanation.push_str(LH_USING_LEMMA);
          str_explanation.push(' ');
        } else {
          is_first_lemma = false;
        }
        str_explanation.push_str(lemma_str);
        str_explanation.push('\n');
      }
    }
    // It might be that there are no lines in this proof
    if is_first_lemma {
      add_indentation(&mut str_explanation, depth);
      str_explanation.push_str(UNIT);
      str_explanation.push('\n');
    }
  }

  str_explanation
}

fn add_comment(str_explanation: &mut String, comment: Option<&String>, depth: usize) {
  if CONFIG.proof_comments {
    if let Some(comment_str) = comment {
      add_indentation(str_explanation, depth);
      str_explanation.push_str(comment_str);
      str_explanation.push('\n');
    }
  }
}

fn add_lemma_invocation<'a, L>(lemma_name: &str, lemma_arguments: L) -> String
where
  L: Iterator<Item = &'a String>,
{
  let mut lemma_str = String::new();
  lemma_str.push_str(lemma_name);
  for arg in lemma_arguments {
    lemma_str.push_str(" (");
    lemma_str.push_str(arg);
    lemma_str.push(')');
  }
  lemma_str
}

fn extract_lemma_invocation(
  rule_str: &str,
  rw_dir: &RwDirection,
  curr_term: &FlatTerm<SymbolLang>,
  next_term: &FlatTerm<SymbolLang>,
  top_goal_name: &str,
  lemma_map: &mut HashMap<String, LemmaInfo>,
  local_context: &Context,
) -> String {
  let mut rewrite_pos: Vec<i32> = vec![];
  let trace = find_rewritten_term(&mut rewrite_pos, next_term).unwrap();
  let (rewritten_to, rewritten_from) = match rw_dir {
    RwDirection::Forward => (
      get_flat_term_from_trace(&trace, next_term),
      get_flat_term_from_trace(&trace, curr_term),
    ),
    RwDirection::Backward => (
      get_flat_term_from_trace(&trace, curr_term),
      get_flat_term_from_trace(&trace, next_term),
    ),
  };
  let lemma: Vec<&str> = rule_str.split(LEMMA_PREFIX).collect::<Vec<&str>>()[1]
    .split(EQUALS)
    .collect();

  let mut lhsmap = map_variables(lemma[0], &flat_term_to_sexp(&rewritten_from).to_string());
  let rhsmap = map_variables(lemma[1], &flat_term_to_sexp(&rewritten_to).to_string());

  // println!("lhs: {}, rhs: {}", lemma[0], lemma[1]);
  // println!("lhs_term: {}, rhs_term: {}", &flat_term_to_sexp(&rewritten_from).to_string(), &flat_term_to_sexp(&rewritten_to).to_string());
  // println!("lhs_map: {:?}, rhs_map: {:?}", lhsmap, rhsmap);

  assert!(rhsmap
    .iter()
    .all(|(key, value)| lhsmap.get(key) == Some(value)));

  // take the union of both maps
  lhsmap.extend(rhsmap);

  match lemma_map.get(rule_str) {
    Some(lemma_info) => {
      // Map lhsmap over the lemma's params.
      // We need to do this because the lemma could be the top level IH,
      // whose parameters are not in the same order as they are stored in lhsmap.
      add_lemma_invocation(
        &lemma_info.name,
        lemma_info
          .params
          .iter()
          .map(|(param, _)| lhsmap.get(param).unwrap()),
      )
    }
    None => {
      let lemma_name = format!("{}_lemma_{}", top_goal_name, lemma_map.len());
      let lemma_info = LemmaInfo {
        name: lemma_name.clone(),
        params: lhsmap
          .keys()
          .map(|param| {
            // println!("{:?} - {}", local_context, param);
            let param_type = local_context
              .get(&Symbol::from_str(param).unwrap())
              .unwrap();
            (param.clone(), param_type.to_string())
          })
          .collect(),
        // Convert to an Sexp so we can fix up its variables and any other stuff
        // we need to convert
        lhs: symbolic_expressions::parser::parse_str(lemma[0]).unwrap(),
        rhs: symbolic_expressions::parser::parse_str(lemma[1]).unwrap(),
      };
      lemma_map.insert(rule_str.to_string(), lemma_info);
      // Create the lemma invocation
      add_lemma_invocation(&lemma_name, lhsmap.values())
    }
  }
}

fn add_indentation(s: &mut String, depth: usize) {
  s.push_str(&" ".repeat(depth * TAB_WIDTH));
}

fn flat_term_to_sexp(flat_term: &FlatTerm<SymbolLang>) -> Sexp {
  let op_sexp = Sexp::String(flat_term.node.op.to_string());
  // This is a leaf
  if flat_term.node.children.is_empty() {
    op_sexp
  // This is an interior node
  } else {
    let mut child_sexps: Vec<Sexp> = vec![op_sexp];
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

fn convert_op(op_str: &str) -> Sexp {
  // Special case for converting `$`, which is used internally in cyclegg for
  // partial application, to the corresponding prefix operator `($)` in
  // Haskell.
  if op_str == APPLY {
    // This is a really ugly hack to wrap `$` in parens.
    Sexp::List(vec![Sexp::String(op_str.to_string())])
  } else {
    Sexp::String(op_str.to_string())
  }
}

/// Basically the same as ty.repr.to_string() but we make arrows infix
fn convert_ty(ty: &Sexp) -> String {
  // println!("ty: {:?}, fixed: {:?}", ty, fix_arrows(&fix_vars(ty)));
  fix_arrows(&fix_vars(ty))
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

fn fix_value(value: &Sexp) -> Sexp {
  map_sexp(convert_op, &fix_vars(value))
}

fn fix_arrows(ty: &Sexp) -> String {
  match ty {
    Sexp::String(str) => str.clone(),
    Sexp::List(children) => {
      // Handle the arrow case, making it infix
      if children.len() == 3 {
        if let Sexp::String(op) = &children[0] {
          if *op == ARROW {
            if let Sexp::List(args) = children[1].clone() {
              let mut arg_tys: Vec<String> = args.iter().map(fix_arrows).collect();
              let return_ty = fix_arrows(&children[2]);
              arg_tys.push(return_ty);
              return format!("({})", arg_tys.join(JOINING_ARROW));
            } else {
              return format!(
                "({} {} {})",
                fix_arrows(&children[1]),
                ARROW,
                fix_arrows(&children[2])
              );
            }
          }
        }
      }
      let converted: String = children
        .iter()
        .map(fix_arrows)
        .collect::<Vec<String>>()
        .join(" ");
      format!("({})", converted)
    }
    Sexp::Empty => String::new(),
  }
}

fn extract_ih_arguments(rule_name: &str) -> Vec<String> {
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
