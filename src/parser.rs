use std::{collections::HashSet};
use symbolic_expressions::*;
use egg::{*};

use crate::ast::*;
use crate::goal::{*};

#[derive(Default)]
struct ParserState {
  env: Env,
  context: Context,
  rules: Vec<Rw>,
  goals: Vec<Goal>,
}

impl ParserState {
  /// Return all function definitions used in exprs,
  /// including the functions transitively used in those definitions.
  pub fn used_definitions(&self, exprs: Vec<&Expr>) -> Vec<Rw> {
    let mut used_names = HashSet::new();
    let mut used_defs = vec![];
    let mut worklist = vec![];
    for expr in exprs {
      let expr_as_nodes_or_var: Vec<ENodeOrVar<SymbolLang>> = expr.as_ref().into_iter().map(|n| ENodeOrVar::ENode(n.clone())).collect();
      let expr_as_pattern: PatternAst<SymbolLang> = PatternAst::from(expr_as_nodes_or_var);
      self.add_functions(&expr_as_pattern, &mut used_names, &mut worklist);
    }
    while let Some(s) = worklist.pop() {
      let def_rules = self.definition(&s);
      for rule in def_rules {
        used_defs.push(rule.clone());
        let rhs = rule.applier.get_pattern_ast().unwrap();
        self.add_functions(&rhs, &mut used_names, &mut worklist);
      }
    }
    used_defs
  }

  /// Add all functions mentioned in e to used_names and worklist.
  fn add_functions(&self, e: &PatternAst<SymbolLang>, used_names: &mut HashSet<Symbol>, worklist: &mut Vec<Symbol>) {
    for node_or_var in e.as_ref() {
      if let ENodeOrVar::ENode(node) = node_or_var {
        let s = node.op;
        if self.context.contains_key(&s) && !is_constructor(&s.to_string()) && !used_names.contains(&s) {
          used_names.insert(s);
          worklist.push(s);
        }
      }
    }
  }

  /// Name of the rule that converts a partial application of name into a first-order application.
  fn part_app_rule(name: &Symbol) -> String {
    format!("apply-{}", name)
  }

  /// Return all rules that define the function name, 
  /// including the rule that defines conversion from partial to first-order application.
  fn definition(&self, name: &Symbol) -> Vec<&Rw> {
    let mut res = Vec::new();
    for r in &self.rules {
      if r.name.to_string() == ParserState::part_app_rule(name) {
        res.push(r);
      } else {
        let lhs_pat = r.searcher.get_pattern_ast().unwrap();
        let lhs_head = lhs_pat.as_ref().iter().last().unwrap();
        if let ENodeOrVar::ENode(n) = lhs_head {
          if n.op == *name {
            res.push(r);
          }
        }
      }
    }
    res
  }

  /// If type_ is an arrow type, return a rewrite that allows converting partial applications into regular first-order applications,
  /// that is: ($ ... ($ name ?x0) ... ?xn) => (name ?x0 ... ?xn).
  fn partial_application(name: &Symbol, type_: &Type) -> Option<Rw> {
    let (args, _) = type_.args_ret();
    if args.is_empty() {
      // This is not a function, so we can't partially apply it
      None
    } else {
      let wildcard = |i: usize| format!("?x{}", i).parse().unwrap();
      // RHS is a full first-order application of name to as many wildcards as there are arguments:
      let rhs: Pat = format!("({} {})", name, (0 .. args.len()).map(wildcard).collect::<Vec<String>>().join(" ")).parse().unwrap();
      // LHS is looks like this "($ ... ($ name ?x0) ... ?xn)":
      let mut lhs_str: String = format!("({} {} ?x0)", APPLY, name);
      for i in (0 .. args.len()).skip(1) {
        lhs_str = format!("({} {} ?x{})", APPLY, lhs_str, i);
      }
      let lhs: Pat = lhs_str.parse().unwrap();
      Some(Rewrite::new(ParserState::part_app_rule(name), lhs, rhs).unwrap())
    }
  }  
}

pub fn parse_file(filename: &str) -> Result<Vec<Goal>, SexpError> {
  let mut state = ParserState::default();
  let sexpr = parser::parse_file(filename).unwrap();

  for decl in sexpr.list()? {
    let decl_kind = decl.list()?[0].string()?.as_str();
    match decl_kind {
      "data" => {
        // This is a datatype declaration: parse name and constructor list:
        let name = decl.list()?[1].string()?;
        let cons = decl.list()?[2].list()?;
        let cons_names = cons.iter().map(|x| Symbol::from(x.string().unwrap())).collect();
        state.env.insert(Symbol::from(name), cons_names);        
      }
      "::" => {
        // This is a type binding: parse name and type:
        let name = Symbol::from(decl.list()?[1].string()?);
        let type_ = Type::new(decl.list()?[2].clone());
        if let Some(rw) = ParserState::partial_application(&name, &type_) {          
          state.rules.push(rw);
        }
        state.context.insert(name, type_);
      }
      "=>" => {
        // This is a rule: parse lhs and rhs:
        let lhs = decl.list()?[1].to_string();
        let rhs = decl.list()?[2].to_string();
        let searcher: Pattern<SymbolLang> = lhs.parse().unwrap();
        let applier: Pattern<SymbolLang> = rhs.parse().unwrap();        
        let rw = Rewrite::new(lhs, searcher, applier).unwrap();
        state.rules.push(rw);
      }
      "<=>" => {
        // This is a rule: parse lhs and rhs:
        let lhs = decl.list()?[1].to_string();
        let rhs = decl.list()?[2].to_string();
        let searcher: Pattern<SymbolLang> = lhs.parse().unwrap();
        let applier: Pattern<SymbolLang> = rhs.parse().unwrap();
        let rw = Rewrite::new(lhs.clone(), searcher.clone(), applier.clone()).unwrap();
        state.rules.push(rw);
        let rw = Rewrite::new(rhs.clone(), applier.clone(), searcher.clone()).unwrap();
        state.rules.push(rw);
      }
      "===" => {
        // This is a goal: parse name, parameter names, parameter types, lhs, and rhs:
        let name = decl.list()?[1].string()?;
        let param_name_list = decl.list()?[2].list()?;
        let param_names: Vec<Symbol> = param_name_list.iter().map(|x| Symbol::from(x.string().unwrap())).collect();
        let param_type_list = decl.list()?[3].list()?;
        let param_types: Vec<Type> = param_type_list.iter().map(|x| Type::new(x.clone())).collect();
        let params = param_names.into_iter().zip(param_types.into_iter()).collect();

        let lhs: Expr = decl.list()?[4].to_string().parse().unwrap();
        let rhs: Expr = decl.list()?[5].to_string().parse().unwrap();
        let rules = &state.used_definitions(vec![&lhs, &rhs]);
        let goal = Goal::top(name, &lhs, &rhs, params, &state.env, &state.context, rules);
        state.goals.push(goal);
      }
      _ => panic!("unknown declaration: {}", decl),
    }
  }
  Ok(state.goals)
}
