import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# CLRS Section 17.4 - Dynamic tables

This first-pass section keeps dynamic tables at the abstract size/count level.
It records the state invariant and a conservative potential wrapper that later
resize-transition proofs can instantiate.

Main results:

- Predicate {lit}`DynamicTableState.Valid`: the number of stored elements does
  not exceed allocated table size.
- Theorem {lit}`dynamicPotential_nonneg`: the first-pass table potential is
  nonnegative.
- Theorems {lit}`dynamicTableInsertSize_fits` and
  {lit}`dynamicTableDeleteSize_fits`: the first-pass capacity choices can hold
  the post-operation number of stored elements.
- Theorems {lit}`dynamicTableInsertSize_ge_size` and
  {lit}`dynamicTableDeleteSize_le_size`: insertion never shrinks capacity, and
  deletion never grows capacity for a valid table.
- Theorems {lit}`dynamicTableInsertSize_of_fits`,
  {lit}`dynamicTableInsertSize_of_expand`,
  {lit}`dynamicTableDeleteSize_of_contract`, and
  {lit}`dynamicTableDeleteSize_of_no_contract`: direct case specifications for
  the first-pass capacity-choice definitions.
- Theorems {lit}`dynamicTableInsertCost_le_num_succ` and
  {lit}`dynamicTableDeleteCost_le_num`: the first-pass transition costs are
  bounded by the natural element-count copying budgets.
- Theorems {lit}`dynamicTableInsertCost_pos` and
  {lit}`dynamicTableDeleteCost_pos_of_nonempty`: first-pass nonempty
  transitions have positive actual cost.
- Theorems {lit}`dynamicTableInsertCost_of_fits`,
  {lit}`dynamicTableInsertCost_of_expand`,
  {lit}`dynamicTableDeleteCost_empty`,
  {lit}`dynamicTableDeleteCost_of_contract`, and
  {lit}`dynamicTableDeleteCost_of_no_contract`: direct case specifications for
  the first-pass actual-cost definitions.
- Theorem {lit}`dynamicTableInsert_valid`: the first-pass insertion transition
  preserves the table-size invariant.
- Theorem {lit}`dynamicTableDelete_valid`: the first-pass deletion/contraction
  transition preserves the table-size invariant.
- Theorems {lit}`dynamicTableInsert_num`, {lit}`dynamicTableInsert_size`,
  {lit}`dynamicTableDelete_num`, and {lit}`dynamicTableDelete_size`: direct
  post-state field equations for the transition wrappers.
- Theorems {lit}`dynamicTableInsert_num_gt`,
  {lit}`dynamicTableInsert_num_ge`, {lit}`dynamicTableDelete_num_le`,
  {lit}`dynamicTableDelete_num_empty`, and
  {lit}`dynamicTableDelete_num_lt_of_nonempty`: direct post-state
  stored-count direction corollaries for insertion and deletion.
- Theorems {lit}`dynamicTableInsert_capacity_fits`,
  {lit}`dynamicTableInsert_capacity_ge_size`,
  {lit}`dynamicTableDelete_capacity_fits`, and
  {lit}`dynamicTableDelete_capacity_le_size`: direct post-state capacity
  corollaries for insertion and deletion.
- Theorems {lit}`dynamicTableInsert_amortizedBound` and
  {lit}`dynamicTableDelete_amortizedBound`: the concrete first-pass transitions
  instantiate the generic amortized-cost wrapper.
- Theorem {lit}`dynamicTable_amortizedBound`: the abstract dynamic-table
  amortized cost is bounded by actual cost plus the post-operation potential.

Current gaps:

- Mutable-array copying and allocator semantics are deferred.
-/

namespace CLRS
namespace Chapter17

/-- Abstract dynamic-table state: stored element count and allocated size. -/
structure DynamicTableState where
  num : Nat
  size : Nat

namespace DynamicTableState

/-- The table never stores more elements than its allocated size. -/
def Valid (s : DynamicTableState) : Prop :=
  s.num <= s.size

end DynamicTableState

/--
A simple nonnegative potential for first-pass dynamic-table amortized wrappers.
Later resize-specific proofs can replace this with the sharper CLRS potential.
-/
def dynamicPotential (s : DynamicTableState) : Int :=
  Int.ofNat (2 * s.num + s.size)

/-- The first-pass dynamic-table potential is nonnegative. -/
theorem dynamicPotential_nonneg (s : DynamicTableState) :
    0 <= dynamicPotential s := by
  unfold dynamicPotential
  exact Int.natCast_nonneg (2 * s.num + s.size)

/-- Abstract dynamic-table amortized cost for one state transition. -/
def dynamicTableAmortizedCost
    (before after : DynamicTableState) (actual : Nat) : Int :=
  Int.ofNat actual + dynamicPotential after - dynamicPotential before

/--
Allocated size after one insertion.  If the existing table has room, keep its
size; otherwise choose a capacity that both fits the new element and doubles the
old allocation budget.
-/
def dynamicTableInsertSize (s : DynamicTableState) : Nat :=
  if s.num + 1 <= s.size then
    s.size
  else
    max (s.num + 1) (2 * s.size)

/-- First-pass dynamic-table insertion transition. -/
def dynamicTableInsert (s : DynamicTableState) : DynamicTableState :=
  { num := s.num + 1, size := dynamicTableInsertSize s }

/-- First-pass insertion cost: one write plus copied elements on expansion. -/
def dynamicTableInsertCost (s : DynamicTableState) : Nat :=
  if s.num + 1 <= s.size then
    1
  else
    s.num + 1

/-- Dynamic-table insertion has positive first-pass actual cost. -/
theorem dynamicTableInsertCost_pos (s : DynamicTableState) :
    0 < dynamicTableInsertCost s := by
  unfold dynamicTableInsertCost
  by_cases hfit : s.num + 1 <= s.size
  · simp [hfit]
  · simp [hfit]

/-- Insertion into a table with spare capacity costs one write. -/
theorem dynamicTableInsertCost_of_fits (s : DynamicTableState)
    (hfit : s.num + 1 <= s.size) :
    dynamicTableInsertCost s = 1 := by
  simp [dynamicTableInsertCost, hfit]

/-- Insertion into a full table costs the post-insertion element count. -/
theorem dynamicTableInsertCost_of_expand (s : DynamicTableState)
    (hfull : ¬ s.num + 1 <= s.size) :
    dynamicTableInsertCost s = s.num + 1 := by
  simp [dynamicTableInsertCost, hfull]

/-- The first-pass insertion cost is bounded by the post-insertion element count. -/
theorem dynamicTableInsertCost_le_num_succ (s : DynamicTableState) :
    dynamicTableInsertCost s <= s.num + 1 := by
  unfold dynamicTableInsertCost
  by_cases hfit : s.num + 1 <= s.size
  · simp [hfit]
  · simp [hfit]

/-- Insertion with spare capacity keeps the old allocation size. -/
theorem dynamicTableInsertSize_of_fits (s : DynamicTableState)
    (hfit : s.num + 1 <= s.size) :
    dynamicTableInsertSize s = s.size := by
  simp [dynamicTableInsertSize, hfit]

/-- Insertion without spare capacity uses the first-pass expansion choice. -/
theorem dynamicTableInsertSize_of_expand (s : DynamicTableState)
    (hfull : ¬ s.num + 1 <= s.size) :
    dynamicTableInsertSize s = max (s.num + 1) (2 * s.size) := by
  simp [dynamicTableInsertSize, hfull]

/-- The insertion capacity choice can hold the inserted element. -/
theorem dynamicTableInsertSize_fits (s : DynamicTableState) :
    s.num + 1 <= dynamicTableInsertSize s := by
  unfold dynamicTableInsertSize
  by_cases hfit : s.num + 1 <= s.size
  · simp [hfit]
  · simp [hfit]

/-- The insertion capacity choice never shrinks the table. -/
theorem dynamicTableInsertSize_ge_size (s : DynamicTableState) :
    s.size <= dynamicTableInsertSize s := by
  unfold dynamicTableInsertSize
  by_cases hfit : s.num + 1 <= s.size
  · simp [hfit]
  · simp [hfit]
    exact Or.inr (by omega)

/-- Dynamic-table insertion increments the stored-element count by one. -/
theorem dynamicTableInsert_num (s : DynamicTableState) :
    (dynamicTableInsert s).num = s.num + 1 := by
  rfl

/-- Dynamic-table insertion sets the post-state capacity to the insertion capacity choice. -/
theorem dynamicTableInsert_size (s : DynamicTableState) :
    (dynamicTableInsert s).size = dynamicTableInsertSize s := by
  rfl

/-- Dynamic-table insertion strictly increases the stored-element count. -/
theorem dynamicTableInsert_num_gt (s : DynamicTableState) :
    s.num < (dynamicTableInsert s).num := by
  rw [dynamicTableInsert_num]
  exact Nat.lt_succ_self s.num

/-- Dynamic-table insertion never decreases the stored-element count. -/
theorem dynamicTableInsert_num_ge (s : DynamicTableState) :
    s.num <= (dynamicTableInsert s).num := by
  exact Nat.le_of_lt (dynamicTableInsert_num_gt s)

/-- Dynamic-table insertion leaves enough capacity for the post-insertion count. -/
theorem dynamicTableInsert_capacity_fits (s : DynamicTableState) :
    (dynamicTableInsert s).num <= (dynamicTableInsert s).size := by
  exact dynamicTableInsertSize_fits s

/-- Dynamic-table insertion never shrinks the post-state capacity below the old size. -/
theorem dynamicTableInsert_capacity_ge_size (s : DynamicTableState) :
    s.size <= (dynamicTableInsert s).size := by
  exact dynamicTableInsertSize_ge_size s

/-- Dynamic-table insertion preserves the table-size invariant. -/
theorem dynamicTableInsert_valid (s : DynamicTableState)
    (_hvalid : DynamicTableState.Valid s) :
    DynamicTableState.Valid (dynamicTableInsert s) := by
  unfold DynamicTableState.Valid dynamicTableInsert
  exact dynamicTableInsertSize_fits s

/--
Allocated size after one deletion.  If the post-deletion load is low, shrink
toward half the old allocation while keeping enough room for all stored
elements.
-/
def dynamicTableDeleteSize (s : DynamicTableState) : Nat :=
  let newNum := s.num - 1
  if 4 * newNum <= s.size then
    max newNum (s.size / 2)
  else
    s.size

/-- First-pass dynamic-table deletion/contraction transition. -/
def dynamicTableDelete (s : DynamicTableState) : DynamicTableState :=
  { num := s.num - 1, size := dynamicTableDeleteSize s }

/-- First-pass deletion cost: one deletion plus copied elements on contraction. -/
def dynamicTableDeleteCost (s : DynamicTableState) : Nat :=
  if s.num = 0 then
    0
  else if 4 * (s.num - 1) <= s.size then
    s.num
  else
    1

/-- Deleting from a nonempty dynamic table has positive first-pass actual cost. -/
theorem dynamicTableDeleteCost_pos_of_nonempty (s : DynamicTableState)
    (hnum : s.num ≠ 0) :
    0 < dynamicTableDeleteCost s := by
  unfold dynamicTableDeleteCost
  simp [hnum]
  by_cases hcontract : 4 * (s.num - 1) <= s.size
  · simp [hcontract]
    omega
  · simp [hcontract]

/-- Deleting from an empty table has zero first-pass cost. -/
theorem dynamicTableDeleteCost_empty (s : DynamicTableState)
    (hempty : s.num = 0) :
    dynamicTableDeleteCost s = 0 := by
  simp [dynamicTableDeleteCost, hempty]

/-- Contracting after deletion costs copying the remaining represented elements. -/
theorem dynamicTableDeleteCost_of_contract (s : DynamicTableState)
    (hnum : s.num ≠ 0) (hcontract : 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteCost s = s.num := by
  simp [dynamicTableDeleteCost, hnum, hcontract]

/-- Deletion without contraction costs one unit in the first-pass model. -/
theorem dynamicTableDeleteCost_of_no_contract (s : DynamicTableState)
    (hnum : s.num ≠ 0) (hcontract : ¬ 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteCost s = 1 := by
  simp [dynamicTableDeleteCost, hnum, hcontract]

/-- The first-pass deletion cost is bounded by the pre-deletion element count. -/
theorem dynamicTableDeleteCost_le_num (s : DynamicTableState) :
    dynamicTableDeleteCost s <= s.num := by
  unfold dynamicTableDeleteCost
  by_cases hempty : s.num = 0
  · simp [hempty]
  · simp [hempty]
    by_cases hcontract : 4 * (s.num - 1) <= s.size
    · simp [hcontract]
    · simp [hcontract]
      omega

/-- Deletion with low post-deletion load uses the first-pass contraction choice. -/
theorem dynamicTableDeleteSize_of_contract (s : DynamicTableState)
    (hcontract : 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteSize s = max (s.num - 1) (s.size / 2) := by
  simp [dynamicTableDeleteSize, hcontract]

/-- Deletion without contraction keeps the old allocation size. -/
theorem dynamicTableDeleteSize_of_no_contract (s : DynamicTableState)
    (hcontract : ¬ 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteSize s = s.size := by
  simp [dynamicTableDeleteSize, hcontract]

/-- The deletion capacity choice can hold the remaining elements of a valid table. -/
theorem dynamicTableDeleteSize_fits (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    s.num - 1 <= dynamicTableDeleteSize s := by
  unfold DynamicTableState.Valid at hvalid
  unfold dynamicTableDeleteSize
  by_cases hcontract : 4 * (s.num - 1) <= s.size
  · simp [hcontract]
  · simp [hcontract]
    omega

/-- The deletion capacity choice never grows a valid table. -/
theorem dynamicTableDeleteSize_le_size (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    dynamicTableDeleteSize s <= s.size := by
  unfold DynamicTableState.Valid at hvalid
  unfold dynamicTableDeleteSize
  by_cases hcontract : 4 * (s.num - 1) <= s.size
  · simp [hcontract]
    constructor
    · omega
    · exact Nat.div_le_self s.size 2
  · simp [hcontract]

/-- Dynamic-table deletion decrements the stored-element count, saturating at zero. -/
theorem dynamicTableDelete_num (s : DynamicTableState) :
    (dynamicTableDelete s).num = s.num - 1 := by
  rfl

/-- Dynamic-table deletion sets the post-state capacity to the deletion capacity choice. -/
theorem dynamicTableDelete_size (s : DynamicTableState) :
    (dynamicTableDelete s).size = dynamicTableDeleteSize s := by
  rfl

/-- Dynamic-table deletion never increases the stored-element count. -/
theorem dynamicTableDelete_num_le (s : DynamicTableState) :
    (dynamicTableDelete s).num <= s.num := by
  rw [dynamicTableDelete_num]
  exact Nat.sub_le s.num 1

/-- Deleting from an empty table leaves the stored-element count at zero. -/
theorem dynamicTableDelete_num_empty (s : DynamicTableState)
    (hempty : s.num = 0) :
    (dynamicTableDelete s).num = 0 := by
  rw [dynamicTableDelete_num, hempty]

/-- Deleting from a nonempty table strictly decreases the stored-element count. -/
theorem dynamicTableDelete_num_lt_of_nonempty (s : DynamicTableState)
    (hnum : s.num ≠ 0) :
    (dynamicTableDelete s).num < s.num := by
  rw [dynamicTableDelete_num]
  omega

/-- Dynamic-table deletion leaves enough capacity for the post-deletion count. -/
theorem dynamicTableDelete_capacity_fits (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    (dynamicTableDelete s).num <= (dynamicTableDelete s).size := by
  exact dynamicTableDeleteSize_fits s hvalid

/-- Dynamic-table deletion never grows the post-state capacity for a valid table. -/
theorem dynamicTableDelete_capacity_le_size (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    (dynamicTableDelete s).size <= s.size := by
  exact dynamicTableDeleteSize_le_size s hvalid

/-- Dynamic-table deletion/contraction preserves the table-size invariant. -/
theorem dynamicTableDelete_valid (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    DynamicTableState.Valid (dynamicTableDelete s) := by
  unfold DynamicTableState.Valid dynamicTableDelete
  exact dynamicTableDeleteSize_fits s hvalid

/--
The abstract amortized transition cost is bounded by actual cost plus the
post-operation potential, because the pre-operation potential is nonnegative.
-/
theorem dynamicTable_amortizedBound
    (before after : DynamicTableState) (actual : Nat) :
    dynamicTableAmortizedCost before after actual <=
      Int.ofNat actual + dynamicPotential after := by
  have hnonneg : 0 <= dynamicPotential before := dynamicPotential_nonneg before
  unfold dynamicTableAmortizedCost
  omega

/-- The concrete first-pass insertion transition instantiates the generic bound. -/
theorem dynamicTableInsert_amortizedBound (s : DynamicTableState) :
    dynamicTableAmortizedCost s (dynamicTableInsert s) (dynamicTableInsertCost s) <=
      Int.ofNat (dynamicTableInsertCost s) + dynamicPotential (dynamicTableInsert s) := by
  exact dynamicTable_amortizedBound s (dynamicTableInsert s) (dynamicTableInsertCost s)

/-- The concrete first-pass deletion transition instantiates the generic bound. -/
theorem dynamicTableDelete_amortizedBound (s : DynamicTableState) :
    dynamicTableAmortizedCost s (dynamicTableDelete s) (dynamicTableDeleteCost s) <=
      Int.ofNat (dynamicTableDeleteCost s) + dynamicPotential (dynamicTableDelete s) := by
  exact dynamicTable_amortizedBound s (dynamicTableDelete s) (dynamicTableDeleteCost s)

end Chapter17
end CLRS
