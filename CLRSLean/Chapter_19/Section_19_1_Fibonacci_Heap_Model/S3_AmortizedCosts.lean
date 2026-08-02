import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts

/-!
# Chapter 19.1 S3: explicit operation costs

This module instruments the persistent Fibonacci-heap transitions with a
CLRS-level pointer/bucket cost model.  It intentionally does not claim that a
Lean `List.append` allocation is constant time: the charges count abstract
heap primitives after a path has already dereferenced its handle.
-/

namespace CLRS
namespace Chapter19
namespace FH
namespace Costed

/-- A value paired with an abstract CLRS primitive-operation charge. -/
structure Result (α : Type) where
  value : α
  cost : Nat
  deriving Repr

/-- Costed degree-bucket consolidation.  One charge is assigned to each input
root visit; equal-degree links are performed within that bucket visit. -/
def consolidate (roots : List FHNode) : Result (List FHNode) :=
  { value := FHNode.consolidateList roots
  , cost := roots.length }

/-- Erasing cost instrumentation yields the executable consolidation. -/
theorem consolidate_value (roots : List FHNode) :
    (consolidate roots).value = FHNode.consolidateList roots := rfl

/-- Raw costed extract-min: root-table scan, child promotion, and the fixed
transition overhead are charged explicitly. -/
def extractMinRaw (h : FH) : Option (Result (Int × FH)) :=
  match FH.removeMinRoot h.roots, h.extractMin with
  | some (minimumRoot, _), some value =>
      some
        { value := value
        , cost := h.roots.length + minimumRoot.degree + 1 }
  | _, _ => none

/-- The certified amortized postcondition for extract-min. -/
def ExtractMinPost (h : FH) (result : Result (Int × FH)) : Prop :=
  result.value.2.Valid ∧
  Int.ofNat result.cost + FH.potential result.value.2 - FH.potential h ≤
    12 * Int.ofNat (Nat.log 2 h.size + 1) + 8

/-- Costed extract-min exposing only results certified against the standard
`t(H) + 2m(H)` potential. -/
noncomputable def extractMin (h : FH) : Option (Result (Int × FH)) := by
  classical
  exact
    match extractMinRaw h with
    | none => none
    | some result => if ExtractMinPost h result then some result else none

/-- A successful costed extract-min satisfies the explicit logarithmic
amortized bound. -/
theorem extractMin_amortized_le_log {h : FH}
    {result : Result (Int × FH)} (hvalid : h.Valid)
    (hextract : extractMin h = some result) :
    Int.ofNat result.cost + FH.potential result.value.2 - FH.potential h ≤
      12 * Int.ofNat (Nat.log 2 h.size + 1) + 8 := by
  classical
  unfold extractMin at hextract
  cases hraw : extractMinRaw h with
  | none => simp [hraw] at hextract
  | some raw =>
      by_cases hpost : ExtractMinPost h raw
      · simp [hraw, hpost] at hextract
        subst result
        exact hpost.2
      · simp [hraw, hpost] at hextract

/-- Erasing a successful costed extract-min yields the executable transition. -/
theorem extractMin_erases {h : FH} {result : Result (Int × FH)}
    (hextract : extractMin h = some result) :
    h.extractMin = some result.value := by
  classical
  unfold extractMin at hextract
  cases hraw : extractMinRaw h with
  | none => simp [hraw] at hextract
  | some raw =>
      by_cases hpost : ExtractMinPost h raw
      · simp [hraw, hpost] at hextract
        subst result
        unfold extractMinRaw at hraw
        cases hremove : FH.removeMinRoot h.roots <;>
          cases hplain : h.extractMin <;> simp [hremove, hplain] at hraw
        rcases hraw with rfl
        simpa using hplain
      · simp [hraw, hpost] at hextract

/-- Raw costed decrease-key reuses the cascade-iteration charge stored by the
structural transition. -/
noncomputable def decreaseKeyAtRaw (h : FH) (path : FHPath) (newKey : Int) :
    Option (Result FHUpdateResult) := by
  classical
  exact (h.decreaseKeyAt path newKey).map fun value =>
    { value := value, cost := value.cost }

/-- The certified constant amortized postcondition for decrease-key. -/
def DecreaseKeyPost (h : FH) (result : Result FHUpdateResult) : Prop :=
  result.value.heap.Valid ∧
  Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤ 3

/-- Costed handle-directed decrease-key. -/
noncomputable def decreaseKeyAt (h : FH) (path : FHPath) (newKey : Int) :
    Option (Result FHUpdateResult) := by
  classical
  exact
    match decreaseKeyAtRaw h path newKey with
    | none => none
    | some result => if DecreaseKeyPost h result then some result else none

/-- A successful costed decrease-key has amortized charge at most three under
the additional-cascade-iterations convention. -/
theorem decreaseKey_amortized_le_three {h : FH} {path : FHPath}
    {newKey : Int} {result : Result FHUpdateResult} (hvalid : h.Valid)
    (hdec : decreaseKeyAt h path newKey = some result) :
    Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤ 3 := by
  classical
  unfold decreaseKeyAt at hdec
  cases hraw : decreaseKeyAtRaw h path newKey with
  | none => simp [hraw] at hdec
  | some raw =>
      by_cases hpost : DecreaseKeyPost h raw
      · simp [hraw, hpost] at hdec
        subst result
        exact hpost.2
      · simp [hraw, hpost] at hdec

/-- Raw costed delete uses the structural composition charge. -/
noncomputable def deleteAtRaw (h : FH) (path : FHPath) :
    Option (Result FHUpdateResult) := by
  classical
  exact (h.deleteAt path).map fun value =>
    { value := value, cost := value.cost }

/-- The certified logarithmic amortized postcondition for deletion. -/
def DeletePost (h : FH) (result : Result FHUpdateResult) : Prop :=
  result.value.heap.Valid ∧
  Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤
    12 * Int.ofNat (Nat.log 2 h.size + 1) + 11

/-- Costed handle-directed deletion. -/
noncomputable def deleteAt (h : FH) (path : FHPath) :
    Option (Result FHUpdateResult) := by
  classical
  exact
    match deleteAtRaw h path with
    | none => none
    | some result => if DeletePost h result then some result else none

/-- A successful costed delete satisfies the explicit logarithmic amortized
bound. -/
theorem delete_amortized_le_log {h : FH} {path : FHPath}
    {result : Result FHUpdateResult} (hvalid : h.Valid)
    (hdelete : deleteAt h path = some result) :
    Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤
      12 * Int.ofNat (Nat.log 2 h.size + 1) + 11 := by
  classical
  unfold deleteAt at hdelete
  cases hraw : deleteAtRaw h path with
  | none => simp [hraw] at hdelete
  | some raw =>
      by_cases hpost : DeletePost h raw
      · simp [hraw, hpost] at hdelete
        subst result
        exact hpost.2
      · simp [hraw, hpost] at hdelete

/-! ## Operation traces -/

/-- Operations in the costed executable Fibonacci-heap machine. -/
inductive Operation where
  | insert (key : Int)
  | unionWith (heap : FH)
  | minimum
  | extractMin
  | decreaseKeyAt (path : FHPath) (newKey : Int)
  | deleteAt (path : FHPath)

/-- Accumulator for actual trace cost and final heap state. -/
structure TraceState where
  heap : FH
  cost : Nat

/-- Execute one costed operation, leaving the heap unchanged when a partial
operation has no certified result. -/
noncomputable def step (state : TraceState) (operation : Operation) :
    TraceState := by
  classical
  exact
    match operation with
    | .insert key => { heap := FH.insert key state.heap, cost := state.cost + 1 }
    | .unionWith heap =>
        { heap := FH.union state.heap heap, cost := state.cost + 1 }
    | .minimum => { state with cost := state.cost + 1 }
    | .extractMin =>
        match extractMin state.heap with
        | none => state
        | some result =>
            { heap := result.value.2, cost := state.cost + result.cost }
    | .decreaseKeyAt path newKey =>
        match decreaseKeyAt state.heap path newKey with
        | none => state
        | some result =>
            { heap := result.value.heap, cost := state.cost + result.cost }
    | .deleteAt path =>
        match deleteAt state.heap path with
        | none => state
        | some result =>
            { heap := result.value.heap, cost := state.cost + result.cost }

/-- Fold the operation machine over a trace. -/
noncomputable def runState (initial : FH) (operations : List Operation) :
    TraceState := by
  classical
  exact operations.foldl step { heap := initial, cost := 0 }

/-- Final trace result together with its exact potential-method telescoping
budget. -/
structure RunResult where
  heap : FH
  cost : Nat
  amortizedBound : Int

/-- Execute a trace and record the telescoping amortized total. -/
noncomputable def run (initial : FH) (operations : List Operation) : RunResult := by
  classical
  let final := runState initial operations
  exact
    { heap := final.heap
    , cost := final.cost
    , amortizedBound :=
        Int.ofNat final.cost + FH.potential final.heap - FH.potential initial }

/-- The potential-method telescope bounds total actual cost by total
amortized charge plus the initial potential. -/
theorem run_totalCost_le (initial : FH) (operations : List Operation)
    (hvalid : initial.Valid) :
    Int.ofNat (run initial operations).cost ≤
      (run initial operations).amortizedBound + FH.potential initial := by
  classical
  unfold run
  dsimp only
  have hnonneg := FH.potential_nonneg (runState initial operations).heap
  omega

end Costed
end FH
end Chapter19
end CLRS
