use egg::*;
use symbolic_expressions::Sexp;
use std::collections::HashMap;

use crate::ast::{Type, Expr};
use crate::goal::{ProofState, ProofTerm};

/// Constants from (Liquid)Haskell
const EQUALS: &str = "=";
const LH_EQUALS: &str = "==.";
const USING_LEMMA: &str = "?";
const AND_THEN: &str = "***";
const QED: &str = "QED";
const TAB_WIDTH: usize = 2;
const PROOF: &str = "Proof";

const LH_TYPE_BEGIN: &str = "{-@";
const LH_TYPE_END: &str = "@-}";
const HAS_TYPE: &str = "::";

/// Constants from cyclegg
const APPLY: &str = "$";
const ARROW: &str = "->";

/// A rewrite can be forward or backward, this specifies which direction it
/// goes.
enum RwDirection {
    Forward,
    Backward
}

// TODO: Add functions and data declarations
pub fn explain_top(goal: String, state: &mut ProofState, lhs: Expr, rhs: Expr, top_level_vars: HashMap<Symbol, Type>) -> String {
    let mut str_explanation = String::new();
    // (arg name, arg type)
    let args: Vec<(String, String)> =
        top_level_vars.into_iter().map(|(symbol, ty)| (symbol.to_string(), convert_ty(ty.repr))).collect();

    // LH type
    str_explanation.push_str(LH_TYPE_BEGIN);
    str_explanation.push_str(&goal);
    str_explanation.push_str(HAS_TYPE);
    // Join with arrows each of the arguments
    let args_str = args.iter()
                       .map(|(arg_name, arg_ty)| format!("{}: {}", arg_name, arg_ty))
                       .collect::<Vec<String>>().join(ARROW);
    str_explanation.push_str(&args_str);
    // Refined type of the proof
    let proof_str = format!("{{ {} = {} }}", lhs, rhs);
    str_explanation.push_str(ARROW);
    str_explanation.push_str(&proof_str);
    str_explanation.push_str(LH_TYPE_END);
    str_explanation.push('\n');

    // Haskell type
    str_explanation.push_str(&goal);
    str_explanation.push_str(HAS_TYPE);
    // Same deal as with the LH type but now we just include the types
    let arg_tys_str = args.iter()
                       .map(|(_, arg_ty)| arg_ty.to_string())
                       .collect::<Vec<String>>().join(ARROW);
    str_explanation.push_str(&arg_tys_str);
    str_explanation.push_str(ARROW);
    // This time we just use the Proof type
    str_explanation.push_str(&PROOF);
    str_explanation.push('\n');

    // Haskell function definition
    str_explanation.push_str(&goal);
    str_explanation.push(' ');
    // Now we include just the arguments and separate by spaces
    let arg_names_str = args.iter()
                       .map(|(arg_name, _)| arg_name.to_string())
                       .collect::<Vec<String>>().join(" ");
    str_explanation.push_str(&arg_names_str);
    str_explanation.push_str(&EQUALS);
    str_explanation.push('\n');

    // Finally, we can do the proof explanation
    let proof_exp = explain_proof(1, goal, state);
    str_explanation.push_str(&proof_exp);
    str_explanation
}

fn explain_proof(depth: usize, goal: String, state: &mut ProofState) -> String {
    // If it's not in the proof tree, it must be a leaf.
    if !state.proof.contains_key(&goal) {
        // The explanation should be in solved_goal_explanations. If it isn't,
        // we must be trying to explain an incomplete proof which is an error.
        return explain_goal(depth, state.solved_goal_explanations.get_mut(&goal).unwrap());
    }
    // Need to clone to avoid borrowing... unfortunately this is all because we need
    // a mutable reference to the explanations for some annoying reason
    match state.proof.get(&goal).unwrap().clone() {
        ProofTerm::CaseSplit(var, cases) => {
            let mut str_explanation = String::new();
            add_indentation(&mut str_explanation, depth);
            str_explanation.push_str(&format!("case {} of", var));
            str_explanation.push('\n');
            let case_depth = depth + 1;
            for (case_constr, case_goal) in cases {
                add_indentation(&mut str_explanation, case_depth);
                str_explanation.push_str(&format!("{} ->", case_constr));
                str_explanation.push('\n');
                // Recursively explain the proof
                str_explanation.push_str(&explain_proof(case_depth + 1, case_goal.to_string(), state));
            }
            str_explanation
        }
    }
}

fn explain_goal(depth: usize, explanation: &mut Explanation<SymbolLang>) -> String {
    // TODO: Add lemma justification with USING_LEMMA
    let mut str_explanation: String = String::new();
    let flat_terms = explanation.make_flat_explanation();
    // Render each of the terms in the explanation
    let flat_strings: Vec<String> = flat_terms.into_iter().map(|flat_term| {
        let mut str = String::new();
        add_indentation(&mut str, depth);
        str.push_str(&flat_term_to_sexp(flat_term).to_string());
        str
    }).collect();
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

fn add_indentation(s: &mut String, depth: usize) {
    s.push_str(&" ".repeat(depth * TAB_WIDTH));
}

fn flat_term_to_sexp(flat_term: &FlatTerm<SymbolLang>) -> Sexp {
    // This is a leaf
    if flat_term.node.children.is_empty() {
        convert_op(flat_term.node.op)
    // This is an interior node
    } else {
        let mut child_sexps: Vec<Sexp> = vec!(convert_op(flat_term.node.op));
        for child in &flat_term.children {
            child_sexps.push(flat_term_to_sexp(child));
        }
        Sexp::List(child_sexps)
    }
}

fn convert_op(op: Symbol) -> Sexp {
    let op_str = op.to_string();
    // Special case for converting `$`, which is used internally in cyclegg for
    // partial application, to the corresponding prefix operator `($)` in
    // Haskell.
    if op_str == APPLY {
        // This is a really ugly hack to wrap `$` in parens.
        Sexp::List(vec!(Sexp::String(op_str)))
    } else {
        Sexp::String(op_str)
    }
}

/// Basically the same as ty.repr.to_string() but we make arrows infix
fn convert_ty(ty: Sexp) -> String {
    match ty {
        Sexp::String(str) => str,
        Sexp::List(children) => {
            // Handle the arrow case, making it infix
            if children.len() == 3 {
                if let Sexp::String(op) = &children[0] {
                    if op == &ARROW {
                        // FIXME: remove clones
                        if let Sexp::List(args) = children[1].clone() {
                            let mut arg_tys: Vec<String> = args.into_iter().map(convert_ty).collect();
                            let return_ty = convert_ty(children[2].clone());
                            arg_tys.push(return_ty);
                            return format!("({})", arg_tys.join(ARROW));
                        }
                    }
                }
            }
            let converted: String = children.into_iter().map(convert_ty).collect::<Vec<String>>().join(" ");
            format!("({})", converted)
        },
        Sexp::Empty => String::new(),
    }
}
