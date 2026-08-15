import CLRSLean.FourthEdition.Chapter_22

/-!
# Fourth-edition Chapter 22 interface checks

These checks pin the public theorem interface of the native fourth-edition
§22.5 (proofs of shortest-paths properties) additions, alongside the existing
§22.1–§22.4 shortest-path results.
-/

namespace CLRS
namespace Chapter24

-- §22.5 shortest-paths properties (backbone + new lemmas)
#check WeightedGraph.shortestDist
#check WeightedGraph.shortestDist_isShortestDist
#check WeightedGraph.noPath_iff_top
#check WeightedGraph.shortestDist_le_walkWeight
#check WeightedGraph.shortestDist_triangleInequality

-- §22.5 triangle inequality iterated along a walk
#check WeightedGraph.shortestDist_triangle_walk

-- §22.5 subpath property (Lemma 22.10)
#check WeightedGraph.subpath_isShortest

-- §22.5 convergence / path-relaxation (Lemmas 22.14-22.15)
#check WeightedGraph.relaxDist_antitone
#check WeightedGraph.shortestDist_convergence
#check WeightedGraph.relaxDist_eq_of_shortest_walk

-- §22.5 predecessor-subgraph property (Lemma 22.16)
#check WeightedGraph.predecessor
#check WeightedGraph.preds_nonempty_of_walk
#check WeightedGraph.shortestDist_eq_inf_preds
#check WeightedGraph.predecessor_isPredecessor
#check WeightedGraph.predecessor_inf_eq
#check WeightedGraph.predecessor_tight

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms WeightedGraph.subpath_isShortest
#print axioms WeightedGraph.shortestDist_convergence
#print axioms WeightedGraph.relaxDist_eq_of_shortest_walk
#print axioms WeightedGraph.predecessor_tight

end Chapter24
end CLRS
