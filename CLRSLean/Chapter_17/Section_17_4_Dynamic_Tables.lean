import CLRSLean.Chapter_17.Section_17_1_Amortized_Framework

/-!
# CLRS Section 17.4 - Dynamic tables

This first-pass section keeps dynamic tables at the abstract size/count level.
It records the state invariant and a conservative potential wrapper that later
resize-transition proofs can instantiate.

Main results:

- Predicate {lit}`DynamicTableState.Valid`: the number of stored elements does
  not exceed allocated table size.
- Theorem {lit}`dynamicTableInsert_valid`: the first-pass insertion transition
  preserves the table-size invariant.
- Theorem {lit}`dynamicTable_amortizedBound`: the abstract dynamic-table
  amortized cost is bounded by actual cost plus the post-operation potential.

Current gaps:

- Contraction transition predicates remain future work.
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

/-- Dynamic-table insertion increments the stored-element count by one. -/
theorem dynamicTableInsert_num (s : DynamicTableState) :
    (dynamicTableInsert s).num = s.num + 1 := by
  rfl

/-- Dynamic-table insertion preserves the table-size invariant. -/
theorem dynamicTableInsert_valid (s : DynamicTableState)
    (_hvalid : DynamicTableState.Valid s) :
    DynamicTableState.Valid (dynamicTableInsert s) := by
  unfold DynamicTableState.Valid dynamicTableInsert dynamicTableInsertSize
  by_cases hfit : s.num + 1 <= s.size
  · simp [hfit]
  · simp [hfit]

/--
The abstract amortized transition cost is bounded by actual cost plus the
post-operation potential, because the pre-operation potential is nonnegative.
-/
theorem dynamicTable_amortizedBound
    (before after : DynamicTableState) (actual : Nat) :
    dynamicTableAmortizedCost before after actual <=
      Int.ofNat actual + dynamicPotential after := by
  have hnonneg : 0 <= dynamicPotential before := by
    unfold dynamicPotential
    exact Int.natCast_nonneg (2 * before.num + before.size)
  unfold dynamicTableAmortizedCost
  omega

/-- The concrete first-pass insertion transition instantiates the generic bound. -/
theorem dynamicTableInsert_amortizedBound (s : DynamicTableState) :
    dynamicTableAmortizedCost s (dynamicTableInsert s) (dynamicTableInsertCost s) <=
      Int.ofNat (dynamicTableInsertCost s) + dynamicPotential (dynamicTableInsert s) := by
  exact dynamicTable_amortizedBound s (dynamicTableInsert s) (dynamicTableInsertCost s)

end Chapter17
end CLRS
