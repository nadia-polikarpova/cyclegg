use colored::Colorize;
use std::fs::*;
use std::io::Write;
use std::time::Instant;

pub mod ast;
pub mod config;
pub mod egraph;
pub mod explain;
pub mod goal;
pub mod parser;

use config::{ARGS, CONFIG};
use explain::explain_top;
use parser::*;

use crate::{explain::goal_name_to_filename, goal::Goal};

fn main() -> std::io::Result<()> {
  simple_logger::init_with_level(CONFIG.log_level).unwrap();

  let parser_state = parse_file(&ARGS.filename).unwrap();

  let mut result_file = if CONFIG.save_results {
    Some(File::create(CONFIG.output_directory.join("results.csv"))?)
  } else {
    None
  };
  let mut num_goals_attempted = 0;
  let mut num_differing_goals = 0;
  let mut cyclic_num_valid = 0;
  let mut non_cyclic_num_valid = 0;
  for raw_goal in parser_state.raw_goals.iter() {
    let (reductions, defns) = parser_state.get_reductions_and_definitions(
      &raw_goal.equation.lhs,
      &raw_goal.equation.rhs,
      raw_goal.local_rules.clone(),
    );
    let mut goal = Goal::top(
      &raw_goal.name,
      raw_goal.equation.lhs.clone(),
      raw_goal.equation.rhs.clone(),
      raw_goal.params.clone(),
      &parser_state.env,
      &parser_state.context,
      &reductions,
      &defns,
    );
    if let Some(prop_name) = &CONFIG.prop {
      if &goal.name != prop_name {
        continue;
      }
    }
    num_goals_attempted += 1;
    println!(
      "{} {}: {} = {}",
      "Proving begin".blue(),
      raw_goal.name.blue(),
      goal.eq.lhs.sexp,
      goal.eq.rhs.sexp
    );
    let start_cyclic = Instant::now();
    let (result, mut proof_state) = goal::prove(goal.copy(), true);
    let duration_cyclic = start_cyclic.elapsed();
    let goal_name_without_cyclic = format!("{}_no_cyclic", goal.name);
    goal.name = goal_name_without_cyclic;
    let start_non_cyclic = Instant::now();
    let (result_without_cyclic, mut proof_state_without_cyclic) = goal::prove(goal.copy(), false);
    let duration_non_cyclic = start_non_cyclic.elapsed();
    if CONFIG.verbose {
      println!(
        "{} {}: {} = {}",
        "Proving end".blue(),
        raw_goal.name.blue(),
        goal.eq.lhs.sexp,
        goal.eq.rhs.sexp
      );
    }
    if result != result_without_cyclic {
      num_differing_goals += 1;
      println!(
        "{}: with cyclic {}, without cyclic {} ",
        "Differing results".red(),
        result,
        result_without_cyclic
      );
    }
    println!(
      "{} = {} (cyclic: {:.2} ms, non cyclic: {:.2} ms)",
      raw_goal.name.blue(),
      result,
      duration_cyclic.as_millis(),
      duration_non_cyclic.as_millis()
    );
    if let goal::Outcome::Valid = result {
      cyclic_num_valid += 1;
    }
    if let goal::Outcome::Valid = result_without_cyclic {
      non_cyclic_num_valid += 1;
    }
    if CONFIG.emit_proofs {
      if let goal::Outcome::Valid = result {
        if CONFIG.cyclic_proofs {
          let filename = goal_name_to_filename(&raw_goal.name);
          let explanation = explain_top(
            &filename,
            &raw_goal.name,
            &mut proof_state,
            &goal.eq,
            &goal.params,
            &goal.local_context,
            goal.defns,
            goal.env,
            goal.global_context,
          );
          let mut file = File::create(CONFIG.proofs_directory.join(format!("{}.hs", filename)))?;
          file.write_all(explanation.as_bytes())?;
        }
      }
      if let goal::Outcome::Valid = result_without_cyclic {
        let filename = goal_name_to_filename(&goal.name);
        let explanation = explain_top(
          &filename,
          &goal.name,
          &mut proof_state_without_cyclic,
          &goal.eq,
          &goal.params,
          &goal.local_context,
          goal.defns,
          goal.env,
          goal.global_context,
        );
        let mut file = File::create(CONFIG.proofs_directory.join(format!("{}.hs", filename)))?;
        file.write_all(explanation.as_bytes())?;
      }
    }
    if let Some(ref mut file) = result_file {
      let line = format!(
        "{},{:?},{:?},{},{}\n",
        raw_goal.name,
        result,
        result_without_cyclic,
        // Convert to ms
        1000. * duration_cyclic.as_secs_f32(),
        1000. * duration_non_cyclic.as_secs_f32(),
      );
      file.write_all(line.as_bytes())?;
    }
  }
  println!("Attempted {} goals:", num_goals_attempted);
  println!("  {} differing results", num_differing_goals);
  println!("  {} solved (cyclic)", cyclic_num_valid);
  println!("  {} solved (no cyclic)", non_cyclic_num_valid);
  Ok(())
}
