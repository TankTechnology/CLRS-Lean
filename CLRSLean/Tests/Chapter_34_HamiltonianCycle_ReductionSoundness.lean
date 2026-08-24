import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Soundness

namespace CLRS.Tests.Chapter34HamiltonianCycleReductionSoundness

open Chapter34
open Chapter34.HamiltonianCycleReduction

def oneEdgeOneSelector : VertexCoverInstance where
  vertexCount := 2
  targetSize := 1
  edges := [(0, 1)]

def oneEdgeCycle : List Nat :=
  [12, 0, 1, 2, 6, 7, 8, 9, 10, 11, 3, 4, 5]

example : (clrsHamiltonianInstance oneEdgeOneSelector).ListRepresentsHamiltonianCycle
    oneEdgeCycle := by
  decide

example :
    CycleLinked oneEdgeCycle (globalWidgetVertex 0 2)
        (globalWidgetVertex 0 3) ∨
  CycleLinked oneEdgeCycle (globalWidgetVertex 0 2)
        (globalWidgetVertex 0 6) := by
  apply cycleLinked_globalWidgetVertex_two_choice
    (I := oneEdgeOneSelector) (vertices := oneEdgeCycle) (occurrence := 0)
  · decide
  · decide

example :
    UsesWidgetSplitTraversal oneEdgeCycle 0 ∨
      UsesWidgetLeftFullTraversal oneEdgeCycle 0 ∨
      UsesWidgetRightFullTraversal oneEdgeCycle 0 := by
  apply cycle_uses_allowed_widget_traversal
    (I := oneEdgeOneSelector) (vertices := oneEdgeCycle) (occurrence := 0)
  · decide
  · decide
  · decide

#print axioms adj_globalWidgetInternalVertex_iff
#print axioms adj_globalWidgetVertex_two_iff
#print axioms cycle_neighbors_globalWidgetVertex_one
#print axioms cycleLinked_symm
#print axioms cycleLinked_other_of_adj_iff_three
#print axioms cycleLinked_globalWidgetVertex_two_choice
#print axioms cycleLinked_globalWidgetVertex_three_choice
#print axioms cycleLinked_globalWidgetVertex_eight_choice
#print axioms cycleLinked_globalWidgetVertex_nine_choice
#print axioms exists_cycleLinked_boundary
#print axioms not_closed_widget_crossing_pattern
#print axioms cycle_uses_allowed_widget_traversal

end CLRS.Tests.Chapter34HamiltonianCycleReductionSoundness
