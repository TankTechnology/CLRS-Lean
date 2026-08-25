import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_21

/-! # Chapter 21 flagship trust surface -/

#check CLRS.MST.safe_edge_of_lightest_crossing
#check CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty
#check CLRS.MST.FiniteGraph.prim_minimum_spanning_tree

#assert_axioms CLRS.MST.safe_edge_of_lightest_crossing
#assert_axioms CLRS.MST.FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty
#assert_axioms CLRS.MST.FiniteGraph.prim_minimum_spanning_tree

example : CLRS.MST.kruskal (fun _ _ => true) [1, 2] ∅ = ({1, 2} : Finset Nat) := by
  decide
