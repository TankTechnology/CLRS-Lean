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
- Theorems {lit}`dynamicTableInsert_potential_nonneg` and
  {lit}`dynamicTableDelete_potential_nonneg`: concrete post-transition states
  have nonnegative first-pass potential.
- Theorems {lit}`dynamicTableInsertSize_fits` and
  {lit}`dynamicTableDeleteSize_fits`: the first-pass capacity choices can hold
  the post-operation number of stored elements.
- Theorems {lit}`dynamicTableInsertSize_ge_size` and
  {lit}`dynamicTableDeleteSize_le_size`: insertion never shrinks capacity, and
  deletion never grows capacity for a valid table.
- Theorems {lit}`dynamicTableInsertSize_ge_double_of_expand`,
  {lit}`dynamicTableInsert_capacity_ge_double_of_expand`,
  {lit}`dynamicTableDeleteSize_le_half_of_contract`, and
  {lit}`dynamicTableDelete_capacity_le_half_of_contract`: direct capacity
  direction wrappers for resizing branches.
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
- Theorems {lit}`dynamicTableDeleteCost_pos_iff_nonempty` and
  {lit}`dynamicTableDeleteCost_zero_iff_empty`: deletion cost positivity and
  zero-cost behavior exactly match whether the table is nonempty.
- Theorems {lit}`dynamicTableInsertCost_of_fits`,
  {lit}`dynamicTableInsertCost_of_expand`,
  {lit}`dynamicTableDeleteCost_empty`,
  {lit}`dynamicTableDeleteCost_of_contract`, and
  {lit}`dynamicTableDeleteCost_of_no_contract`: direct case specifications for
  the first-pass actual-cost definitions.
- Theorems {lit}`dynamicTableDeleteCost_eq_num_of_contract` and
  {lit}`dynamicTableDeleteCost_eq_one_of_no_contract`: deletion actual-cost
  branch wrappers without an explicit nonempty-table premise.
- Theorem {lit}`dynamicTableInsert_valid`: the first-pass insertion transition
  preserves the table-size invariant.
- Theorem {lit}`dynamicTableDelete_valid`: the first-pass deletion/contraction
  transition preserves the table-size invariant.
- Theorems {lit}`dynamicTableInsert_num`, {lit}`dynamicTableInsert_size`,
  {lit}`dynamicTableDelete_num`, and {lit}`dynamicTableDelete_size`: direct
  post-state field equations for the transition wrappers.
- Theorems {lit}`dynamicTableInsert_size_of_fits`,
  {lit}`dynamicTableInsert_size_of_expand`,
  {lit}`dynamicTableDelete_size_of_contract`, and
  {lit}`dynamicTableDelete_size_of_no_contract`: direct post-state
  allocation-size case specifications for the transition wrappers.
- Theorems {lit}`dynamicTableInsert_num_gt`,
  {lit}`dynamicTableInsert_num_pos`, {lit}`dynamicTableInsert_num_ge`,
  {lit}`dynamicTableDelete_num_le`, {lit}`dynamicTableDelete_num_empty`, and
  {lit}`dynamicTableDelete_num_pos_of_one_lt`, and
  {lit}`dynamicTableDelete_num_lt_of_nonempty`: direct post-state stored-count
  direction corollaries for insertion and deletion.
- Theorems {lit}`dynamicTableInsert_capacity_fits`,
  {lit}`dynamicTableInsert_capacity_pos`,
  {lit}`dynamicTableInsert_capacity_ge_size`,
  {lit}`dynamicTableDelete_capacity_fits`,
  {lit}`dynamicTableDelete_capacity_pos_of_one_lt`, and
  {lit}`dynamicTableDelete_capacity_le_size`: direct post-state capacity
  corollaries for insertion and deletion.
- Theorems {lit}`dynamicTableInsert_amortizedBound` and
  {lit}`dynamicTableDelete_amortizedBound`: the concrete first-pass transitions
  instantiate the generic amortized-cost wrapper.
- Theorems {lit}`dynamicTableInsert_amortizedCost_eq` and
  {lit}`dynamicTableDelete_amortizedCost_eq`: concrete transition amortized
  costs unfold to actual cost plus the post-potential minus the pre-potential.
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

/-- The insertion expansion branch allocates at least double the old capacity. -/
theorem dynamicTableInsertSize_ge_double_of_expand (s : DynamicTableState)
    (hfull : ¬ s.num + 1 <= s.size) :
    2 * s.size <= dynamicTableInsertSize s := by
  rw [dynamicTableInsertSize_of_expand s hfull]
  exact le_max_right (s.num + 1) (2 * s.size)

/-- Dynamic-table insertion increments the stored-element count by one. -/
theorem dynamicTableInsert_num (s : DynamicTableState) :
    (dynamicTableInsert s).num = s.num + 1 := by
  rfl

/-- Dynamic-table insertion sets the post-state capacity to the insertion capacity choice. -/
theorem dynamicTableInsert_size (s : DynamicTableState) :
    (dynamicTableInsert s).size = dynamicTableInsertSize s := by
  rfl

/-- Insertion with spare capacity keeps the post-state allocation size. -/
theorem dynamicTableInsert_size_of_fits (s : DynamicTableState)
    (hfit : s.num + 1 <= s.size) :
    (dynamicTableInsert s).size = s.size := by
  rw [dynamicTableInsert_size, dynamicTableInsertSize_of_fits s hfit]

/-- Insertion without spare capacity uses the expansion choice as the post-state size. -/
theorem dynamicTableInsert_size_of_expand (s : DynamicTableState)
    (hfull : ¬ s.num + 1 <= s.size) :
    (dynamicTableInsert s).size = max (s.num + 1) (2 * s.size) := by
  rw [dynamicTableInsert_size, dynamicTableInsertSize_of_expand s hfull]

/-- Dynamic-table insertion strictly increases the stored-element count. -/
theorem dynamicTableInsert_num_gt (s : DynamicTableState) :
    s.num < (dynamicTableInsert s).num := by
  rw [dynamicTableInsert_num]
  exact Nat.lt_succ_self s.num

/-- Dynamic-table insertion leaves a positive stored-element count. -/
theorem dynamicTableInsert_num_pos (s : DynamicTableState) :
    0 < (dynamicTableInsert s).num := by
  rw [dynamicTableInsert_num]
  exact Nat.succ_pos s.num

/-- Dynamic-table insertion never decreases the stored-element count. -/
theorem dynamicTableInsert_num_ge (s : DynamicTableState) :
    s.num <= (dynamicTableInsert s).num := by
  exact Nat.le_of_lt (dynamicTableInsert_num_gt s)

/-- Dynamic-table insertion leaves enough capacity for the post-insertion count. -/
theorem dynamicTableInsert_capacity_fits (s : DynamicTableState) :
    (dynamicTableInsert s).num <= (dynamicTableInsert s).size := by
  exact dynamicTableInsertSize_fits s

/-- Dynamic-table insertion leaves a positive post-state capacity. -/
theorem dynamicTableInsert_capacity_pos (s : DynamicTableState) :
    0 < (dynamicTableInsert s).size := by
  have hnum : 0 < (dynamicTableInsert s).num :=
    dynamicTableInsert_num_pos s
  have hfit : (dynamicTableInsert s).num <= (dynamicTableInsert s).size :=
    dynamicTableInsert_capacity_fits s
  omega

/-- Dynamic-table insertion never shrinks the post-state capacity below the old size. -/
theorem dynamicTableInsert_capacity_ge_size (s : DynamicTableState) :
    s.size <= (dynamicTableInsert s).size := by
  exact dynamicTableInsertSize_ge_size s

/-- The insertion expansion branch leaves post-state capacity at least double the old capacity. -/
theorem dynamicTableInsert_capacity_ge_double_of_expand (s : DynamicTableState)
    (hfull : ¬ s.num + 1 <= s.size) :
    2 * s.size <= (dynamicTableInsert s).size := by
  rw [dynamicTableInsert_size]
  exact dynamicTableInsertSize_ge_double_of_expand s hfull

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

/-- Insertion leaves a state with nonnegative first-pass potential. -/
theorem dynamicTableInsert_potential_nonneg (s : DynamicTableState) :
    0 <= dynamicPotential (dynamicTableInsert s) := by
  exact dynamicPotential_nonneg (dynamicTableInsert s)

/-- Deletion leaves a state with nonnegative first-pass potential. -/
theorem dynamicTableDelete_potential_nonneg (s : DynamicTableState) :
    0 <= dynamicPotential (dynamicTableDelete s) := by
  exact dynamicPotential_nonneg (dynamicTableDelete s)

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

/-- Dynamic-table deletion has positive cost exactly when the table is nonempty. -/
theorem dynamicTableDeleteCost_pos_iff_nonempty (s : DynamicTableState) :
    0 < dynamicTableDeleteCost s <-> s.num ≠ 0 := by
  constructor
  · intro hpos hempty
    have hzero : dynamicTableDeleteCost s = 0 :=
      dynamicTableDeleteCost_empty s hempty
    omega
  · intro hnum
    exact dynamicTableDeleteCost_pos_of_nonempty s hnum

/-- Dynamic-table deletion has zero cost exactly when the table is empty. -/
theorem dynamicTableDeleteCost_zero_iff_empty (s : DynamicTableState) :
    dynamicTableDeleteCost s = 0 <-> s.num = 0 := by
  constructor
  · intro hzero
    by_contra hnum
    have hpos : 0 < dynamicTableDeleteCost s :=
      dynamicTableDeleteCost_pos_of_nonempty s hnum
    omega
  · intro hempty
    exact dynamicTableDeleteCost_empty s hempty

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

/-- The contraction branch costs the pre-deletion element count, including empty tables. -/
theorem dynamicTableDeleteCost_eq_num_of_contract (s : DynamicTableState)
    (hcontract : 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteCost s = s.num := by
  by_cases hnum : s.num = 0
  · rw [hnum]
    exact dynamicTableDeleteCost_empty s hnum
  · exact dynamicTableDeleteCost_of_contract s hnum hcontract

/-- The no-contraction branch costs one unit and necessarily comes from a nonempty table. -/
theorem dynamicTableDeleteCost_eq_one_of_no_contract (s : DynamicTableState)
    (hcontract : ¬ 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteCost s = 1 := by
  have hnum : s.num ≠ 0 := by
    intro hempty
    apply hcontract
    rw [hempty]
    simp
  exact dynamicTableDeleteCost_of_no_contract s hnum hcontract

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

/-- The deletion contraction branch allocates no more than half the old capacity. -/
theorem dynamicTableDeleteSize_le_half_of_contract (s : DynamicTableState)
    (hcontract : 4 * (s.num - 1) <= s.size) :
    dynamicTableDeleteSize s <= s.size / 2 := by
  rw [dynamicTableDeleteSize_of_contract s hcontract]
  have hremaining : s.num - 1 <= s.size / 2 := by
    rw [Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    omega
  exact max_le hremaining le_rfl

/-- Dynamic-table deletion decrements the stored-element count, saturating at zero. -/
theorem dynamicTableDelete_num (s : DynamicTableState) :
    (dynamicTableDelete s).num = s.num - 1 := by
  rfl

/-- Dynamic-table deletion sets the post-state capacity to the deletion capacity choice. -/
theorem dynamicTableDelete_size (s : DynamicTableState) :
    (dynamicTableDelete s).size = dynamicTableDeleteSize s := by
  rfl

/-- Deletion with low post-deletion load uses the contraction choice as the post-state size. -/
theorem dynamicTableDelete_size_of_contract (s : DynamicTableState)
    (hcontract : 4 * (s.num - 1) <= s.size) :
    (dynamicTableDelete s).size = max (s.num - 1) (s.size / 2) := by
  rw [dynamicTableDelete_size, dynamicTableDeleteSize_of_contract s hcontract]

/-- Deletion without contraction keeps the old allocation size as the post-state size. -/
theorem dynamicTableDelete_size_of_no_contract (s : DynamicTableState)
    (hcontract : ¬ 4 * (s.num - 1) <= s.size) :
    (dynamicTableDelete s).size = s.size := by
  rw [dynamicTableDelete_size, dynamicTableDeleteSize_of_no_contract s hcontract]

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

/-- Deleting from a table with at least two elements leaves a positive count. -/
theorem dynamicTableDelete_num_pos_of_one_lt (s : DynamicTableState)
    (hnum : 1 < s.num) :
    0 < (dynamicTableDelete s).num := by
  rw [dynamicTableDelete_num]
  omega

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

/-- Deleting from a valid table with at least two elements leaves positive capacity. -/
theorem dynamicTableDelete_capacity_pos_of_one_lt (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) (hnum : 1 < s.num) :
    0 < (dynamicTableDelete s).size := by
  have hpost : 0 < (dynamicTableDelete s).num :=
    dynamicTableDelete_num_pos_of_one_lt s hnum
  have hfit : (dynamicTableDelete s).num <= (dynamicTableDelete s).size :=
    dynamicTableDelete_capacity_fits s hvalid
  omega

/-- Dynamic-table deletion never grows the post-state capacity for a valid table. -/
theorem dynamicTableDelete_capacity_le_size (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    (dynamicTableDelete s).size <= s.size := by
  exact dynamicTableDeleteSize_le_size s hvalid

/-- The deletion contraction branch leaves post-state capacity no more than half the old capacity. -/
theorem dynamicTableDelete_capacity_le_half_of_contract (s : DynamicTableState)
    (hcontract : 4 * (s.num - 1) <= s.size) :
    (dynamicTableDelete s).size <= s.size / 2 := by
  rw [dynamicTableDelete_size]
  exact dynamicTableDeleteSize_le_half_of_contract s hcontract

/-- Dynamic-table deletion/contraction preserves the table-size invariant. -/
theorem dynamicTableDelete_valid (s : DynamicTableState)
    (hvalid : DynamicTableState.Valid s) :
    DynamicTableState.Valid (dynamicTableDelete s) := by
  unfold DynamicTableState.Valid dynamicTableDelete
  exact dynamicTableDeleteSize_fits s hvalid

/-- Concrete insertion amortized cost unfolds to actual plus potential change. -/
theorem dynamicTableInsert_amortizedCost_eq (s : DynamicTableState) :
    dynamicTableAmortizedCost s (dynamicTableInsert s) (dynamicTableInsertCost s) =
      Int.ofNat (dynamicTableInsertCost s) +
        dynamicPotential (dynamicTableInsert s) - dynamicPotential s := by
  rfl

/-- Concrete deletion amortized cost unfolds to actual plus potential change. -/
theorem dynamicTableDelete_amortizedCost_eq (s : DynamicTableState) :
    dynamicTableAmortizedCost s (dynamicTableDelete s) (dynamicTableDeleteCost s) =
      Int.ofNat (dynamicTableDeleteCost s) +
        dynamicPotential (dynamicTableDelete s) - dynamicPotential s := by
  rfl

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
