import CLRSLean.FourthEdition.Chapter_19.Section_19_2_Linked_List_Representation.WeightedExecution
import CLRSLean.Audit.Axioms

open CLRS.Chapter21 CLRS.Chapter21.LinkedList
open CLRS.Chapter21.LinkedList.WeightedExecution

private def balanced : List (Operation (Fin 4)) :=
  [.find 0, .union 0 1, .find 0, .union 2 3, .union 1 3, .find 2, .union 0 2, .find 0]

example : (execute (State.singleton 4) balanced).outputs =
    [some 0, none, some 1, none, none, some 3, none, some 3] := by native_decide
example : (execute (State.singleton 4) balanced).rewrites = 4 := by native_decide
example : (execute (State.singleton 4) balanced).charged = 12 := by native_decide
example : List.ofFn (execute (State.singleton 4) balanced).moves = [2, 1, 1, 0] := by native_decide
example : List.ofFn (execute (State.singleton 4) balanced).state.setSize = [4, 4, 4, 4] := by native_decide
example : (execute (State.singleton 4) balanced).state.sameSet 0 3 := by
  unfold State.sameSet
  native_decide

private def star : List (Operation (Fin 4)) := [.union 0 1, .union 1 2, .union 1 3]
example : (execute (State.singleton 4) star).rewrites = 3 := by native_decide
example : List.ofFn (execute (State.singleton 4) star).moves = [1, 0, 1, 1] := by native_decide
example : (execute (State.singleton 0) []).charged = 0 := by native_decide
example : (execute (State.singleton 1) [.union 0 0, .find 0]).outputs = [none, some 0] := by native_decide
example : (execute (State.singleton 1) [.union 0 0, .find 0]).rewrites = 0 := by native_decide

-- The size invariant is necessary when relating native stored-size charges to
-- actual changes; arbitrary malformed states cannot satisfy that bridge.
private def malformed : State 2 := ⟨id, fun _ => 100⟩
example : (malformed.weightedUnion 0 1).2 = 100 := by native_decide
example : (changes malformed (malformed.weightedUnion 0 1).1).length = 1 := by native_decide

example {n : Nat} (ops : List (Operation (Fin n))) :
    (execute (State.singleton n) ops).rewrites ≤ n * Nat.log2 n :=
  execute_singleton_rewrites_le ops

#assert_axioms singleton_sized
#assert_axioms union_sized
#assert_axioms union_changes_cost
#assert_axioms execute_rewrites_eq_sum
#assert_axioms execute_singleton_moves_le
#assert_axioms execute_singleton_rewrites_le
#assert_axioms execute_refines_spec
#assert_axioms execute_find_output
#assert_axioms execute_find_representative
#assert_axioms execute_singleton_charged_le
