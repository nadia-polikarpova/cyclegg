use symbolic_expressions::*;
use egg::{*};

#[path = "./ast.rs"] pub mod ast;
#[path = "./config.rs"] pub mod config;
#[path = "./goal.rs"] pub mod goal;
use goal::{*, ast::*};

#[derive(Default)]
struct ParserState {
  env: Env,
  context: Context,
  rules: Vec<Rw>,
  goals: Vec<Goal>,
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
        let name = decl.list()?[1].string()?;
        let type_ = Type::new(decl.list()?[2].clone());
        state.context.insert(Symbol::from(name), type_);
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
        let goal = Goal::top(name, &lhs, &rhs, params, &state.env, &state.context, &state.rules);
        state.goals.push(goal);
      }
      _ => panic!("unknown declaration: {}", decl),
    }
  }
  Ok(state.goals)
}
