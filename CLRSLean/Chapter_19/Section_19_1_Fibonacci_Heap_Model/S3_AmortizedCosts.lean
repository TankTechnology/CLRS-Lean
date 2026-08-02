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

/-- Costed extract-min.  The implementation is fully executable; its
amortized certificate is established below instead of checked at runtime. -/
def extractMin (h : FH) : Option (Result (Int × FH)) :=
  extractMinRaw h

/-- A raw costed result exposes the selected root, the executable transition,
and its exact abstract charge. -/
theorem extractMinRaw_components {h : FH} {result : Result (Int × FH)}
    (hextract : extractMinRaw h = some result) :
    ∃ minimumRoot rest value,
      FH.removeMinRoot h.roots = some (minimumRoot, rest) ∧
      h.extractMin = some value ∧
      result.value = value ∧
      result.cost = h.roots.length + minimumRoot.degree + 1 := by
  unfold extractMinRaw at hextract
  cases hremove : FH.removeMinRoot h.roots with
  | none => simp [hremove] at hextract
  | some pair =>
      rcases pair with ⟨minimumRoot, rest⟩
      cases hplain : h.extractMin with
      | none => simp [hremove, hplain] at hextract
      | some value =>
          simp [hremove, hplain] at hextract
          subst result
          exact ⟨minimumRoot, rest, value, rfl, rfl, rfl, rfl⟩

/-- A successful costed extract-min satisfies the explicit logarithmic
amortized bound. -/
theorem extractMin_amortized_le_log {h : FH}
    {result : Result (Int × FH)} (hvalid : h.Valid)
    (hextract : extractMin h = some result) :
    Int.ofNat result.cost + FH.potential result.value.2 - FH.potential h ≤
      12 * Int.ofNat (Nat.log 2 h.size + 1) + 8 := by
  obtain ⟨minimumRoot, rest, value, hremove, hplain, hvalue, hcost⟩ :=
    extractMinRaw_components (show extractMinRaw h = some result from hextract)
  rcases value with ⟨minimum, h'⟩
  have hvalid' : h'.Valid := FH.extractMin_valid hvalid hplain
  have hsize' : h'.size + 1 = h.size := FH.extractMin_size hvalid hplain
  have hselected := FH.removeMinRoot_good hremove hvalid.1
  have hminimumMem : minimumRoot ∈ h.roots :=
    (FH.removeMinRoot_perm hremove).mem_iff.mp (by simp)
  have hminimumSize : minimumRoot.size ≤ h.size := by
    rw [hvalid.2.2.2.1]
    exact FHNode.size_le_forestSize_of_mem hminimumMem
  have hminimumDegree :
      minimumRoot.degree ≤ 2 * Nat.log 2 h.size + 1 :=
    FHNode.wellformed_degree_le_twice_log_two minimumRoot hselected.2.1
      hminimumSize
  have hrootDegree : ∀ root ∈ h'.roots,
      root.degree ≤ 2 * Nat.log 2 h.size + 1 := by
    intro root hroot
    have hrootSize : root.size ≤ h'.size := by
      rw [hvalid'.2.2.2.1]
      exact FHNode.size_le_forestSize_of_mem hroot
    exact FHNode.wellformed_degree_le_twice_log_two root
      (hvalid'.1.2 root hroot) (by omega)
  have hrootCount :
      h'.roots.length ≤ 2 * Nat.log 2 h.size + 1 + 1 :=
    FHNode.length_le_succ_of_degreeStrict
      (FH.extractMin_degreeStrict hvalid hplain) hrootDegree
  have hmarks :
      FHNode.forestMarks h'.roots ≤ FHNode.forestMarks h.roots :=
    FH.extractMin_forestMarks_le hvalid hplain
  rw [hvalue, hcost]
  unfold FH.potential
  simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
  omega

/-- Erasing a successful costed extract-min yields the executable transition. -/
theorem extractMin_erases {h : FH} {result : Result (Int × FH)}
    (hextract : extractMin h = some result) :
    h.extractMin = some result.value := by
  obtain ⟨minimumRoot, rest, value, hremove, hplain, hvalue, hcost⟩ :=
    extractMinRaw_components (show extractMinRaw h = some result from hextract)
  simpa [hvalue] using hplain

/-- Raw costed decrease-key reuses the cascade-iteration charge stored by the
structural transition. -/
def decreaseKeyAtRaw (h : FH) (path : FHPath) (newKey : Int) :
    Option (Result FHUpdateResult) :=
  (h.decreaseKeyAtRaw path newKey).map fun value =>
    { value := value, cost := value.cost }

/-- The certified constant amortized postcondition for decrease-key. -/
def DecreaseKeyPost (h : FH) (result : Result FHUpdateResult) : Prop :=
  result.value.heap.Valid ∧
  Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤ 3

/-- Costed handle-directed decrease-key.  Certification is a theorem about
the executable result, rather than a proposition-valued runtime filter. -/
def decreaseKeyAt (h : FH) (path : FHPath) (newKey : Int) :
    Option (Result FHUpdateResult) :=
  decreaseKeyAtRaw h path newKey

/-- A successful costed decrease-key has amortized charge at most three under
the additional-cascade-iterations convention. -/
theorem decreaseKey_amortized_le_three {h : FH} {path : FHPath}
    {newKey : Int} {result : Result FHUpdateResult} (hvalid : h.Valid)
    (hdec : decreaseKeyAt h path newKey = some result) :
    Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤ 3 := by
  unfold decreaseKeyAt decreaseKeyAtRaw at hdec
  cases hraw : h.decreaseKeyAtRaw path newKey with
  | none => simp [hraw] at hdec
  | some raw =>
      simp [hraw] at hdec
      subst result
      exact FH.decreaseKeyAtRaw_amortized hvalid hraw

/-- Erasing the cost wrapper yields the structural decrease-key transition. -/
theorem decreaseKeyAt_erases {h : FH} {path : FHPath} {newKey : Int}
    {result : Result FHUpdateResult}
    (hdec : decreaseKeyAt h path newKey = some result) :
    h.decreaseKeyAtRaw path newKey = some result.value := by
  unfold decreaseKeyAt decreaseKeyAtRaw at hdec
  cases hraw : h.decreaseKeyAtRaw path newKey with
  | none => simp [hraw] at hdec
  | some raw =>
      simp [hraw] at hdec
      subst result
      rfl

/-- Raw costed delete composes the executable decrease-key and extract-min
machines.  Its outer charge is the sum of their abstract charges, while the
embedded structural result retains the core transition's own cost field. -/
def deleteAtRaw (h : FH) (path : FHPath) :
    Option (Result FHUpdateResult) := do
  let cursor ← h.openPath path
  let minimum ← h.minimum
  let decreased ← decreaseKeyAtRaw h path (minimum - 1)
  let extracted ← extractMinRaw decreased.value.heap
  pure
    { value :=
        { oldKey := cursor.focus.key
        , heap := extracted.value.2
        , cost := decreased.value.cost + 1 }
    , cost := decreased.cost + extracted.cost }

/-- The certified logarithmic amortized postcondition for deletion. -/
def DeletePost (h : FH) (result : Result FHUpdateResult) : Prop :=
  result.value.heap.Valid ∧
  Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤
    12 * Int.ofNat (Nat.log 2 h.size + 1) + 11

/-- Costed handle-directed deletion, with certification supplied by theorem. -/
def deleteAt (h : FH) (path : FHPath) :
    Option (Result FHUpdateResult) :=
  deleteAtRaw h path

/-- A successful costed delete exposes both component transitions. -/
theorem deleteAtRaw_components {h : FH} {path : FHPath}
    {result : Result FHUpdateResult}
    (hdelete : deleteAtRaw h path = some result) :
    ∃ cursor minimum decreased extracted,
      h.openPath path = some cursor ∧
      h.minimum = some minimum ∧
      decreaseKeyAtRaw h path (minimum - 1) = some decreased ∧
      extractMinRaw decreased.value.heap = some extracted ∧
      result.value =
        { oldKey := cursor.focus.key
        , heap := extracted.value.2
        , cost := decreased.value.cost + 1 } ∧
      result.cost = decreased.cost + extracted.cost := by
  unfold deleteAtRaw at hdelete
  cases hopen : h.openPath path with
  | none => simp [hopen] at hdelete
  | some cursor =>
      simp only [hopen, Option.bind_eq_bind, Option.bind_some] at hdelete
      cases hminimum : h.minimum with
      | none => simp [hminimum] at hdelete
      | some minimum =>
          simp only [hminimum, Option.bind_eq_bind, Option.bind_some] at hdelete
          cases hdecreased : decreaseKeyAtRaw h path (minimum - 1) with
          | none => simp [hdecreased] at hdelete
          | some decreased =>
              simp only [hdecreased, Option.bind_eq_bind, Option.bind_some] at hdelete
              cases hextracted : extractMinRaw decreased.value.heap with
              | none => simp [hextracted] at hdelete
              | some extracted =>
                  simp [hextracted] at hdelete
                  subst result
                  exact ⟨cursor, minimum, decreased, extracted,
                    by simpa using hopen,
                    by simpa using hminimum,
                    by simpa using hdecreased,
                    by simpa using hextracted,
                    rfl, rfl⟩

/-- A successful costed delete satisfies the explicit logarithmic amortized
bound. -/
theorem delete_amortized_le_log {h : FH} {path : FHPath}
    {result : Result FHUpdateResult} (hvalid : h.Valid)
    (hdelete : deleteAt h path = some result) :
    Int.ofNat result.cost + FH.potential result.value.heap - FH.potential h ≤
      12 * Int.ofNat (Nat.log 2 h.size + 1) + 11 := by
  obtain ⟨cursor, minimum, decreased, extracted, hopen, hminimum,
      hdecreased, hextracted, hvalue, hcost⟩ :=
    deleteAtRaw_components (show deleteAtRaw h path = some result from hdelete)
  have hdecreasedCore :
      h.decreaseKeyAtRaw path (minimum - 1) = some decreased.value :=
    decreaseKeyAt_erases hdecreased
  have hdecreasedCorrect :=
    FH.decreaseKeyAtRaw_correct hvalid hdecreasedCore
  have hdecreasedBound := decreaseKey_amortized_le_three hvalid hdecreased
  have hextractedPlain :
      decreased.value.heap.extractMin = some extracted.value :=
    extractMin_erases hextracted
  have hextractedBound :=
    extractMin_amortized_le_log hdecreasedCorrect.2.2.2 hextracted
  have hsameSize : decreased.value.heap.size = h.size :=
    hdecreasedCorrect.2.2.1
  rw [hsameSize] at hextractedBound
  rw [hvalue, hcost]
  simp only [Int.ofNat_eq_natCast, Nat.cast_add] at hdecreasedBound hextractedBound ⊢
  omega

/-- Erasing the cost wrapper yields the executable structural deletion. -/
theorem deleteAt_erases {h : FH} {path : FHPath}
    {result : Result FHUpdateResult}
    (hdelete : deleteAt h path = some result) :
    h.deleteAtRaw path = some result.value := by
  obtain ⟨cursor, minimum, decreased, extracted, hopen, hminimum,
      hdecreased, hextracted, hvalue, hcost⟩ :=
    deleteAtRaw_components (show deleteAtRaw h path = some result from hdelete)
  have hdecreasedCore :
      h.decreaseKeyAtRaw path (minimum - 1) = some decreased.value :=
    decreaseKeyAt_erases hdecreased
  have hextractedPlain :
      decreased.value.heap.extractMin = some extracted.value :=
    extractMin_erases hextracted
  unfold FH.deleteAtRaw
  simp [hopen, hminimum, hdecreasedCore, hextractedPlain, hvalue]

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

namespace Operation

/-- Preconditions carried by a trace.  Only union needs an additional valid
heap; all other partial operations safely leave the state unchanged when their
handle or minimum is absent. -/
def Admissible : Operation → Prop
  | .unionWith heap => heap.Valid
  | _ => True

/-- Per-operation amortized budget.  Union transfers the second heap's
potential into the one-state machine, so that potential appears explicitly in
its budget. -/
def bound (source : FH) : Operation → Int
  | .insert _ => 2
  | .unionWith heap => 1 + heap.potential
  | .minimum => 1
  | .extractMin => 12 * Int.ofNat (Nat.log 2 source.size + 1) + 8
  | .decreaseKeyAt _ _ => 3
  | .deleteAt _ => 12 * Int.ofNat (Nat.log 2 source.size + 1) + 11

end Operation

/-- Execute one costed operation, leaving the heap unchanged when a partial
operation has no executable result. -/
def step (state : TraceState) (operation : Operation) : TraceState :=
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

/-- Every admissible machine step preserves full heap validity. -/
theorem step_valid {state : TraceState} {operation : Operation}
    (hvalid : state.heap.Valid) (hadmissible : operation.Admissible) :
    (step state operation).heap.Valid := by
  cases operation with
  | insert key => simpa [step] using FH.insert_valid key state.heap hvalid
  | unionWith heap => simpa [step] using FH.union_valid state.heap heap hvalid hadmissible
  | minimum => simpa [step] using hvalid
  | extractMin =>
      cases hextract : extractMin state.heap with
      | none => simpa [step, hextract] using hvalid
      | some result =>
          simp only [step, hextract]
          exact FH.extractMin_valid hvalid (extractMin_erases hextract)
  | decreaseKeyAt path newKey =>
      cases hdecrease : decreaseKeyAt state.heap path newKey with
      | none => simpa [step, hdecrease] using hvalid
      | some result =>
          simp only [step, hdecrease]
          exact (FH.decreaseKeyAtRaw_correct hvalid
            (decreaseKeyAt_erases hdecrease)).2.2.2
  | deleteAt path =>
      cases hdelete : deleteAt state.heap path with
      | none => simpa [step, hdelete] using hvalid
      | some result =>
          simp only [step, hdelete]
          exact (FH.deleteAtRaw_correct hvalid (deleteAt_erases hdelete)).2.2

/-- The actual cost increment plus the potential change of one step. -/
def stepCharge (state : TraceState) (operation : Operation) : Int :=
  let next := step state operation
  Int.ofNat next.cost - Int.ofNat state.cost +
    next.heap.potential - state.heap.potential

/-- Each executable transition satisfies its advertised amortized budget. -/
theorem stepCharge_le_bound {state : TraceState} {operation : Operation}
    (hvalid : state.heap.Valid) (hadmissible : operation.Admissible) :
    stepCharge state operation ≤ operation.bound state.heap := by
  cases operation with
  | insert key =>
      simp only [stepCharge, step, Operation.bound]
      rw [FH.potential_insert]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
      omega
  | unionWith heap =>
      simp only [stepCharge, step, Operation.bound]
      rw [FH.potential_union]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
      omega
  | minimum =>
      simp only [stepCharge, step, Operation.bound]
      simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]
      omega
  | extractMin =>
      cases hextract : extractMin state.heap with
      | none =>
          simp [stepCharge, step, Operation.bound, hextract]
          positivity
      | some result =>
          have hbound := extractMin_amortized_le_log hvalid hextract
          simp only [stepCharge, step, Operation.bound, hextract,
            Int.ofNat_eq_natCast, Nat.cast_add] at hbound ⊢
          omega
  | decreaseKeyAt path newKey =>
      cases hdecrease : decreaseKeyAt state.heap path newKey with
      | none => simp [stepCharge, step, Operation.bound, hdecrease]
      | some result =>
          have hbound := decreaseKey_amortized_le_three hvalid hdecrease
          simp only [stepCharge, step, Operation.bound, hdecrease,
            Int.ofNat_eq_natCast, Nat.cast_add] at hbound ⊢
          omega
  | deleteAt path =>
      cases hdelete : deleteAt state.heap path with
      | none =>
          simp [stepCharge, step, Operation.bound, hdelete]
          positivity
      | some result =>
          have hbound := delete_amortized_le_log hvalid hdelete
          simp only [stepCharge, step, Operation.bound, hdelete,
            Int.ofNat_eq_natCast, Nat.cast_add] at hbound ⊢
          omega

/-- Execute a trace from an arbitrary accumulator state. -/
def runFrom : TraceState → List Operation → TraceState
  | state, [] => state
  | state, operation :: operations =>
      runFrom (step state operation) operations

/-- Execute a trace from a heap with zero accumulated actual cost. -/
def runState (initial : FH) (operations : List Operation) : TraceState :=
  runFrom { heap := initial, cost := 0 } operations

/-- Dynamic trace precondition, evaluated at each intermediate state. -/
def TraceAdmissible : TraceState → List Operation → Prop
  | _, [] => True
  | state, operation :: operations =>
      operation.Admissible ∧
        TraceAdmissible (step state operation) operations

/-- Exact sum of the per-step amortized charges. -/
def traceAmortized : TraceState → List Operation → Int
  | _, [] => 0
  | state, operation :: operations =>
      stepCharge state operation +
        traceAmortized (step state operation) operations

/-- Sum of the advertised per-operation bounds along a trace. -/
def traceBound : TraceState → List Operation → Int
  | _, [] => 0
  | state, operation :: operations =>
      operation.bound state.heap + traceBound (step state operation) operations

/-- Validity propagates through every admissible operation in a trace. -/
theorem runFrom_valid {state : TraceState} {operations : List Operation}
    (hvalid : state.heap.Valid)
    (hadmissible : TraceAdmissible state operations) :
    (runFrom state operations).heap.Valid := by
  induction operations generalizing state with
  | nil => simpa [runFrom] using hvalid
  | cons operation operations ih =>
      exact ih (step_valid hvalid hadmissible.1) hadmissible.2

/-- The sum of local amortized charges telescopes exactly to total actual cost
change plus the endpoint potential difference. -/
theorem traceAmortized_eq (state : TraceState) (operations : List Operation) :
    traceAmortized state operations =
      Int.ofNat (runFrom state operations).cost - Int.ofNat state.cost +
        (runFrom state operations).heap.potential - state.heap.potential := by
  induction operations generalizing state with
  | nil => simp [traceAmortized, runFrom]
  | cons operation operations ih =>
      rw [traceAmortized, runFrom, ih]
      simp only [stepCharge]
      omega

/-- The true trace-level amortized sum is bounded by the sum of the certified
per-operation budgets. -/
theorem traceAmortized_le_traceBound {state : TraceState}
    {operations : List Operation} (hvalid : state.heap.Valid)
    (hadmissible : TraceAdmissible state operations) :
    traceAmortized state operations ≤ traceBound state operations := by
  induction operations generalizing state with
  | nil => simp [traceAmortized, traceBound]
  | cons operation operations ih =>
      rw [traceAmortized, traceBound]
      exact add_le_add (stepCharge_le_bound hvalid hadmissible.1)
        (ih (step_valid hvalid hadmissible.1) hadmissible.2)

/-- Final trace result together with its exact potential-method telescoping
budget. -/
structure RunResult where
  heap : FH
  cost : Nat
  amortizedBound : Int

/-- Execute a trace and record the sum of its local amortized charges. -/
def run (initial : FH) (operations : List Operation) : RunResult := by
  let final := runState initial operations
  exact
    { heap := final.heap
    , cost := final.cost
    , amortizedBound :=
        traceAmortized { heap := initial, cost := 0 } operations }

/-- The recorded amortized total is the genuine per-step telescope. -/
theorem run_amortized_eq (initial : FH) (operations : List Operation) :
    (run initial operations).amortizedBound =
      Int.ofNat (run initial operations).cost +
        (run initial operations).heap.potential - initial.potential := by
  unfold run runState
  dsimp only
  rw [traceAmortized_eq]
  simp

/-- An admissible valid trace stays valid. -/
theorem run_valid {initial : FH} {operations : List Operation}
    (hvalid : initial.Valid)
    (hadmissible :
      TraceAdmissible { heap := initial, cost := 0 } operations) :
    (run initial operations).heap.Valid := by
  simpa [run, runState] using runFrom_valid hvalid hadmissible

/-- The recorded amortized total is bounded by the dynamic sum of all
operation-specific certificates. -/
theorem run_amortized_le_bound {initial : FH} {operations : List Operation}
    (hvalid : initial.Valid)
    (hadmissible :
      TraceAdmissible { heap := initial, cost := 0 } operations) :
    (run initial operations).amortizedBound ≤
      traceBound { heap := initial, cost := 0 } operations := by
  simpa [run] using traceAmortized_le_traceBound hvalid hadmissible

/-- The potential-method telescope bounds total actual cost by total
amortized charge plus the initial potential. -/
theorem run_totalCost_le (initial : FH) (operations : List Operation)
    (hvalid : initial.Valid) :
    Int.ofNat (run initial operations).cost ≤
      (run initial operations).amortizedBound + FH.potential initial := by
  rw [run_amortized_eq]
  have hnonneg := FH.potential_nonneg (run initial operations).heap
  omega

end Costed
end FH
end Chapter19
end CLRS
