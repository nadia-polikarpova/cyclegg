use egg::*;
use std::collections::{HashMap, HashSet};

/// Denotation of an egraph (or its subgraph)
/// is a map from eclass ids to sets of expressions
type Denotation<L> = HashMap<Id, Vec<RecExpr<L>>>;

/// Compute the denotation of all roots in egraph, ignoring cycles
pub fn get_all_expressions<L: Language, A: Analysis<L>>(
  egraph: &EGraph<L, A>,
  roots: Vec<Id>,
) -> Denotation<L> {
  let mut memo = HashMap::new();
  for root in roots {
    collect_expressions(egraph, root, &mut memo);
  }
  memo
}

/// Compute the denotation of eclass ignoring cycles and store it in memo
fn collect_expressions<L: Language, A: Analysis<L>>(
  egraph: &EGraph<L, A>,
  eclass: Id,
  memo: &mut Denotation<L>,
) {
  if memo.get(&eclass).is_some() {
    // Already visited
  } else {
    // Initialize the memo entry for this eclass with an empty denotation,
    // collect denotations in a separate vector and update the map only at the end;
    // this guarantees that we are not following cycles
    memo.insert(eclass, vec![]);
    let mut denotations: Vec<RecExpr<L>> = vec![];
    // Join denotations of every node in the eclass
    for node in egraph[eclass].iter() {
      if node.is_leaf() {
        // If this node is a leaf, its denotation is itself
        let expr = RecExpr::from(vec![node.clone()]);
        denotations.push(expr);
      } else {
        // Otherwise, recursively collect the denotations of its children
        // and create a new expression from each tuple of their cross product.
        // Each products[i] stores the product of denotation sizes of all nodes from i+1 onwards
        let mut products: HashMap<Id, usize> = HashMap::new();
        for (i, c) in node.children().iter().enumerate() {
          collect_expressions(egraph, *c, memo);
          products.insert(*c, 1);
          for j in 0..i {
            products
              .entry(node.children()[j])
              .and_modify(|p| *p *= memo[c].len());
          }
        }
        // Now create the new expressions
        let c0 = &node.children()[0];
        // First compute the size of the cross product; we almost have it in products[c0]; just the size of c0's denotation is missing
        let cross_product_size = products[c0] * memo[c0].len();
        for k in 0..cross_product_size {
          // For the k-th element of the cross product, which element from the denotation of id should we take?
          // The formula is: k / (the product of all following denotation sizes) % this denotation size
          let lookup_id = |id: Id| k / products[&id] % memo[&id].len();
          let expr = node.join_recexprs(|id| memo.get(&id).unwrap()[lookup_id(id)].clone());
          denotations.push(expr);
        }
      }
    }
    memo.insert(eclass, denotations);
  }
}

/// Remove node from egraph
pub fn remove_node<L: Language, A: Analysis<L>>(egraph: &mut EGraph<L, A>, node: &L) {
  for c in egraph.classes_mut() {
    c.nodes.retain(|n| n != node);
  }
}

pub fn rec_expr_to_pattern_ast<L: Clone>(rec_expr: RecExpr<L>) -> RecExpr<ENodeOrVar<L>> {
  let enode_or_vars: Vec<ENodeOrVar<L>> = rec_expr
    .as_ref()
    .iter()
    .cloned()
    .map(|node| ENodeOrVar::ENode(node))
    .collect();
  enode_or_vars.into()
}

/// A term whose root is a given enode and children are extracted by extractor
pub fn extract_with_node<L: Language, A: Analysis<L>, CF: CostFunction<L>>(
  enode: &L,
  extractor: &Extractor<CF, L, A>,
) -> RecExpr<L> {
  enode.join_recexprs(|id| extractor.find_best(id).1)
}

/// Variables of a pattern as a set
pub fn var_set<L: Language>(pattern: &Pattern<L>) -> HashSet<Var> {
  pattern.vars().iter().cloned().collect()
}

/// Like egg's Condition, but for searchers
pub trait SearchCondition<L, N>
where
  L: Language,
  N: Analysis<L>,
{
  fn check(&self, egraph: &EGraph<L, N>, eclass: Id, subst: &Subst) -> bool;
}

/// Conditional searcher
pub struct ConditionalSearcher<C, S> {
  /// The searcher we apply first
  pub searcher: S,
  /// The condition we will check on each match found by the searcher
  pub condition: C,
}

impl<C, S, N, L> Searcher<L, N> for ConditionalSearcher<C, S>
where
  C: SearchCondition<L, N>,
  S: Searcher<L, N>,
  L: Language,
  N: Analysis<L>,
{
  fn search_eclass_with_limit(
    &self,
    egraph: &EGraph<L, N>,
    eclass: Id,
    limit: usize,
  ) -> Option<SearchMatches<L>> {
    // Use the underlying searcher first
    let matches = self
      .searcher
      .search_eclass_with_limit(egraph, eclass, limit)?;
    // Filter the matches using the condition
    let filtered_matches: Vec<Subst> = matches
      .substs
      .into_iter()
      .filter(|subst| self.condition.check(egraph, eclass, subst))
      .collect();
    if filtered_matches.is_empty() {
      // If all substitutions were filtered out,
      // it's as if this eclass hasn't matched at all
      None
    } else {
      Some(SearchMatches {
        eclass: matches.eclass,
        substs: filtered_matches,
        ast: matches.ast,
      })
    }
  }

  fn vars(&self) -> Vec<Var> {
    self.searcher.vars()
  }
}
