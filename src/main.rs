use colored::Colorize;
use std::fs::*;
use std::io::{Result, Write};
use std::time::{Duration, Instant};

pub mod ast;
pub mod config;
pub mod egraph;
pub mod explain;
pub mod goal;
pub mod parser;

use config::{ARGS, CONFIG};
use explain::explain_top;
use goal::*;
use parser::*;

use crate::{explain::goal_name_to_filename, goal::Goal};

fn main() -> Result<()> {
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
    let (reductions, defns) =
      parser_state.get_reductions_and_definitions(raw_goal, raw_goal.local_rules.clone());
    let mut goal = Goal::top(
      &raw_goal.name,
      &raw_goal.equation,
      &raw_goal.premise,
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
      "{} {}: {}",
      "Proving begin".blue(),
      raw_goal.name.blue(),
      goal
    );

    let (result, duration) = if ARGS.do_uncyclic() {
      prove_goal(&goal, false)?
    } else {
      (Outcome::Unknown, Duration::from_secs(0))
    };
    let (result_cyclic, duration_cyclic) = if ARGS.do_cyclic() {
      goal.name = format!("{}_cyclic", goal.name);
      prove_goal(&goal, true)?
    } else {
      (Outcome::Unknown, Duration::from_secs(0))
    };

    if CONFIG.verbose {
      println!(
        "{} {}: {}",
        "Proving end".blue(),
        raw_goal.name.blue(),
        goal
      );
    }

    if ARGS.do_cyclic() && ARGS.do_uncyclic() {
      println!(
        "{} uncyclic: {} ({:.2} ms) cyclic: {} ({:.2} ms)",
        raw_goal.name.blue(),
        result,
        duration.as_millis(),
        result_cyclic,
        duration_cyclic.as_millis()
      );
      if result_cyclic != result {
        num_differing_goals += 1;
        println!("{}", "Differing results".red());
      }
    } else if ARGS.do_cyclic() {
      println!(
        "{} cyclic: {} ({:.2} ms)",
        raw_goal.name.blue(),
        result_cyclic,
        duration_cyclic.as_millis()
      );
    } else if ARGS.do_uncyclic() {
      println!(
        "{} uncyclic: {} ({:.2} ms)",
        raw_goal.name.blue(),
        result,
        duration.as_millis()
      );
    }
    if let Outcome::Valid = result_cyclic {
      cyclic_num_valid += 1;
    }
    if let Outcome::Valid = result {
      non_cyclic_num_valid += 1;
    }
    if let Some(ref mut file) = result_file {
      let line = format!(
        "{},{:?},{:?},{},{}\n",
        raw_goal.name,
        result_cyclic,
        result,
        // Convert to ms
        1000. * duration_cyclic.as_secs_f32(),
        1000. * duration.as_secs_f32(),
      );
      file.write_all(line.as_bytes())?;
    }
  }
  println!("Attempted {} goals:", num_goals_attempted);
  if ARGS.do_cyclic() && ARGS.do_uncyclic() {
    println!("  {} differing results", num_differing_goals);
  }
  if ARGS.do_uncyclic() {
    println!("  {} solved (no cyclic)", non_cyclic_num_valid);
  }
  if ARGS.do_cyclic() {
    println!("  {} solved (cyclic)", cyclic_num_valid);
  }
  Ok(())
}

/// Prove a goal using either cyclic or uncyclic mode;
/// record the duration and emit the proof.
fn prove_goal(goal: &Goal, cyclic: bool) -> Result<(Outcome, Duration)> {
  CONFIG.set_cyclic(cyclic);
  let start_time = Instant::now();
  let (result, mut proof_state) = goal::prove(goal.copy());
  let duration = start_time.elapsed();
  if CONFIG.emit_proofs {
    if let Outcome::Valid = result {
      let filename = goal_name_to_filename(&goal.name);
      let explanation = explain_top(
        &filename,
        &goal.name,
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
  Ok((result, duration))
}
