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
- Theorem {lit}`dynamicTableInsert_valid`: the first-pass insertion transition
  preserves the table-size invariant.
- Theorem {lit}`dynamicTableDelete_valid`: the first-pass deletion/contraction
  transition preserves the table-size invariant.
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
