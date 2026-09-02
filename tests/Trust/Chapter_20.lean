import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_20

/-! # Chapter 20 flagship trust surface -/

#check CLRS.Chapter22.Graph.bfsState_correct
#check CLRS.Chapter22.Graph.bfsStateWithCost_cost_le
#check CLRS.Chapter22.Graph.dfsWithCost_cost_eq
#check CLRS.Chapter22.Graph.dfsWithCost_cost_le
#check CLRS.Chapter22.Graph.dfsTopologicalSort_isTopologicalOrder
#check CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition

#assert_axioms CLRS.Chapter22.Graph.bfsState_correct
#assert_axioms CLRS.Chapter22.Graph.bfsStateWithCost_cost_le
#assert_axioms CLRS.Chapter22.Graph.dfsWithCost_cost_eq
#assert_axioms CLRS.Chapter22.Graph.dfsWithCost_cost_le
#assert_axioms CLRS.Chapter22.Graph.dfsTopologicalSort_isTopologicalOrder
#assert_axioms CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition

example :
    let G : CLRS.Chapter22.Graph (Fin 2) :=
      { vertices := Finset.univ
        adj := fun v => if v = 0 then {1} else ∅
        adj_sub := by simp
        adj_outside := by simp }
    G.Adj 0 1 := by
  simp [CLRS.Chapter22.Graph.Adj]
