use std::{fs::create_dir_all, path::PathBuf, sync::Mutex};

use clap::Parser;
use lazy_static::lazy_static;
use log::Level;

#[derive(Parser)]
pub struct Args {
  pub filename: String,
  #[clap(short = 'd', long = "max-depth", default_value = "3")]
  pub max_split_depth: usize,
  #[clap(short = 's', long = "single-rhs")]
  pub single_rhs: bool,
  #[clap(short = 'i', long = "irreducible")]
  pub irreducible_only: bool,
  #[clap(short = 'c', long = "no-cond-split")]
  pub no_cond_split: bool,
  /// Mode
  #[clap(long = "cyclic")]
  pub cyclic: bool,
  #[clap(long = "no-uncyclic")]
  pub no_uncyclic: bool,
  /// Timeout
  #[clap(short = 't', long = "timeout", default_value = "0")]
  pub timeout: u64,
  /// Logging
  #[clap(short = 'l', long = "log", default_value = "ERROR")]
  pub log_level: String,
  #[clap(short = 'g', long = "save-graphs")]
  pub save_graphs: bool,
  #[clap(short = 'r', long = "save-results")]
  pub save_results: bool,
  /// Emit proofs under the proofs directory in the output directory
  #[clap(short = 'p', long = "emit-proofs")]
  pub emit_proofs: bool,
  #[clap(short = 'v', long = "verbose")]
  pub verbose: bool,
  #[clap(long = "verbose-proofs")]
  pub verbose_proofs: bool,
  /// Where to save outputs other than proofs
  #[clap(short = 'o', long = "output-directory", default_value = "target")]
  pub output_directory: PathBuf,
  /// Where to save proofs
  #[clap(long = "proofs-directory", default_value = "target/proofs")]
  pub proofs_directory: PathBuf,
  /// Only relevant when -p or --emit-proofs is passed.
  ///
  /// By default, when emitting proofs we prepend Cyclegg_ to data types and
  /// cyclegg_ to functions and variables so that Haskell doesn't complain about
  /// name clashes.
  ///
  /// This disables the name mangling for ease of debugging.
  #[clap(long = "unmangled-names")]
  pub unmangled_names: bool,
  /// Do not emit comments in proofs
  #[clap(long = "no-proof-comments")]
  pub no_proof_comments: bool,
  /// Only prove the proposition with this name
  #[clap(long = "prop")]
  pub prop: Option<String>,

  #[clap(long = "no-blocking-analysis")]
  pub no_blocking_analysis: bool,
}

impl Args {
  pub fn do_cyclic(&self) -> bool {
    self.cyclic
  }

  pub fn do_uncyclic(&self) -> bool {
    !self.no_uncyclic
  }
}

pub struct Config {
  pub prop: Option<String>,
  // This is a mutex because we want to be able to change it
  cyclic_mode: Mutex<bool>,
  // proof search parameters
  pub max_split_depth: usize,
  pub split_conditionals: bool,
  pub single_rhs: bool,
  pub irreducible_only: bool,
  // timeout
  pub timeout: Option<u64>,
  // logging
  pub log_level: Level,
  pub save_graphs: bool,
  pub save_results: bool,
  pub emit_proofs: bool,
  pub verbose: bool,
  pub verbose_proofs: bool,
  pub output_directory: PathBuf,
  pub proofs_directory: PathBuf,
  pub mangle_names: bool,
  pub proof_comments: bool,
  pub blocking_vars_analysis: bool,
}

impl Config {
  fn from_args(args: &Args) -> Self {
    // Make the output directory if it doesn't exist.
    create_dir_all(&args.output_directory).unwrap();
    let emit_proofs = args.emit_proofs;
    if emit_proofs {
      // Make the proofs directory if it doesn't exist.
      create_dir_all(&args.proofs_directory).unwrap();
    }
    let mangle_names = !args.unmangled_names && emit_proofs;
    Self {
      cyclic_mode: Mutex::new(false),
      max_split_depth: if mangle_names {
        // Why the +1? Because mangling the names prepends a Cyclegg_ to
        // everything, which means that our depth check (which naively looks at
        // how many underscores there are) will return 1 greater than it should.
        args.max_split_depth + 1
      } else {
        args.max_split_depth
      },
      split_conditionals: !args.no_cond_split,
      single_rhs: args.single_rhs,
      irreducible_only: args.irreducible_only,
      timeout: if args.timeout == 0 {
        None
      } else {
        Some(args.timeout)
      },
      log_level: args.log_level.parse().unwrap(),
      save_graphs: args.save_graphs,
      save_results: args.save_results,
      emit_proofs,
      verbose: args.verbose,
      verbose_proofs: args.verbose_proofs,
      output_directory: args.output_directory.clone(),
      proofs_directory: args.proofs_directory.clone(),
      mangle_names,
      proof_comments: !args.no_proof_comments,
      prop: args.prop.clone(),
      blocking_vars_analysis: !args.no_blocking_analysis,
    }
  }

  pub fn is_cyclic(&self) -> bool {
    *self.cyclic_mode.lock().unwrap()
  }

  pub fn set_cyclic(&self, cyclic: bool) {
    *self.cyclic_mode.lock().unwrap() = cyclic;
  }
}

lazy_static! {
  pub static ref ARGS: Args = Args::parse();
  pub static ref CONFIG: Config = Config::from_args(&ARGS);
}
