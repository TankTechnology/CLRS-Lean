import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_06

/-! # Chapter 6 flagship trust surface -/

#check CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_log_cost
#check CLRS.Chapter06.buildMaxHeapLinearBound_isBigO_n
#check CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct
#check CLRS.Chapter06.arrayHeapInsert_state_correct
#check CLRS.Chapter06.arrayHeapDelete?_state_correct

#assert_axioms CLRS.Chapter06.arrayHeapSortInPlaceWithCost_correct_and_log_cost
#assert_axioms CLRS.Chapter06.buildMaxHeapLinearBound_isBigO_n

/-- Package the advertised array-level priority-queue updates into one
audit declaration, keeping the chapter-wide flagship budget at three. -/
private def IncreaseKeyStateContract : Prop :=
  ∀ {a rest : List Nat} {heapSize i key : Nat},
    CLRS.Chapter06.ArrayMaxHeap a heapSize →
    CLRS.Chapter06.arrayHeapIncreaseKey? a heapSize i key = some rest →
      i < heapSize ∧
        heapSize ≤ a.length ∧
        CLRS.Chapter06.valAt a i ≤ key ∧
        CLRS.Chapter06.ArrayMaxHeap rest heapSize ∧
        rest.length = a.length ∧
        rest.Perm (a.set i key)

private def DeleteStateContract : Prop :=
  ∀ {a rest : List Nat} {heapSize i deleted newHeapSize : Nat},
    CLRS.Chapter06.ArrayMaxHeap a heapSize →
    CLRS.Chapter06.arrayHeapDelete? a heapSize i =
        some (deleted, rest, newHeapSize) →
      i < heapSize ∧
        heapSize ≤ a.length ∧
        deleted = CLRS.Chapter06.valAt a i ∧
        newHeapSize + 1 = heapSize ∧
        CLRS.Chapter06.ArrayMaxHeap rest newHeapSize ∧
        rest.length = a.length ∧
        rest.Perm (a.set i (CLRS.Chapter06.valAt a 0)) ∧
        ∀ {k : Nat}, k < heapSize →
          CLRS.Chapter06.valAt a k ≤ CLRS.Chapter06.valAt a 0

private def InsertStateContract : Prop :=
  ∀ {a : List Nat} (key : Nat),
    CLRS.Chapter06.ArrayMaxHeap a a.length →
      CLRS.Chapter06.ArrayMaxHeap
          (CLRS.Chapter06.arrayHeapInsert a key) (a.length + 1) ∧
        (CLRS.Chapter06.arrayHeapInsert a key).length = a.length + 1 ∧
        (CLRS.Chapter06.arrayHeapInsert a key).Perm (key :: a)

private theorem priorityQueue_state_bundle :
    IncreaseKeyStateContract ∧ InsertStateContract ∧ DeleteStateContract :=
  ⟨CLRS.Chapter06.arrayHeapIncreaseKey?_state_correct,
    CLRS.Chapter06.arrayHeapInsert_state_correct,
    CLRS.Chapter06.arrayHeapDelete?_state_correct⟩

#assert_axioms priorityQueue_state_bundle

example : CLRS.Chapter06.arrayHeapSortInPlace [4, 1, 3, 2] = [1, 2, 3, 4] := by
  decide
