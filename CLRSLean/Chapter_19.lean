import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model
import CLRSLean.Chapter_19.Section_19_4_Bounding_Maximum_Degree

/-!
# Chapter 19 - Fibonacci Heaps

Chapter 19 starts with a first-pass abstract Fibonacci-heap model.  The current
Lean surface represents a heap by a finite set of integer keys plus root/mark
counters, proves operation-level set specifications and direct membership
facts plus direct operation-key corollaries for insertion, extract-min,
decrease-key, and deletion, adds old-key preservation corollaries for the
set-updating operations and exact failed membership specifications after heap
operations, direct failed-membership preservation wrappers, exposes direct
operation-result validity wrappers for normalized counters, adds direct minimum
membership/lower-bound wrappers plus
insert/union/extract-min-remaining/decrease-key/delete minimum direct
membership/lower-bound wrappers, direct minimum/extract-min empty-result
wrappers, remaining/delete minimum nonempty-result wrappers, and positive/empty-result
minimum-after-update specifications plus nonempty-result query wrappers,
exposes the standard
potential function with zero-initial and nonnegativity facts, and
packages a conservative degree-bound wrapper for later subtree-size
strengthening, together with a Fibonacci-style lower-bound recurrence,
positivity, adjacent monotonicity, monotonicity, and the first exponential
growth bridge over even and half indices, plus conditional natural-log degree
budget wrappers.  The query surface includes empty-result specifications for
minimum and extract-min.

## Sections

* 19.1 Fibonacci-heap model: {lit}`partial`.
  Main results:
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_correct`,
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_valid`,
  {lit}`CLRS.Chapter19.FibHeap.makeHeap_minimum_none`,
  {lit}`CLRS.Chapter19.FibHeap.potential_makeHeap`,
  {lit}`CLRS.Chapter19.FibHeap.potential_nonneg`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_le`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.minimum_ne_none_of_nonempty`,
  {lit}`CLRS.Chapter19.FibHeap.insert_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_valid`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_self`,
  {lit}`CLRS.Chapter19.FibHeap.insert_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_le_inserted`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.insert_minimum_ne_none`,
  {lit}`CLRS.Chapter19.FibHeap.union_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_valid`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_mem_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_not_mem_of_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_le_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_le_right`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_left`,
  {lit}`CLRS.Chapter19.FibHeap.union_minimum_ne_none_of_right`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_valid`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_not_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_none_of_empty`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_ne_none_of_nonempty`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter19.FibHeap.extractMin_remaining_minimum_ne_none_of_remaining`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_valid`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_oldKey_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_oldKey_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_not_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_new`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.decreaseKey_minimum_ne_none`,
  {lit}`CLRS.Chapter19.FibHeap.delete_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_valid`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_mem_of_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_old`,
  {lit}`CLRS.Chapter19.FibHeap.delete_not_mem_of_eq`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_correct`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_ne`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_mem`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_le_old`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_iff`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_none_of_all_eq`,
  {lit}`CLRS.Chapter19.FibHeap.delete_minimum_ne_none_of_remaining`,
  {lit}`CLRS.Chapter19.FibHeap.heapPotential_telescope`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_step`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_pos`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_le_succ`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_monotone`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_add_two_ge_double`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_even_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.fibLowerBound_half_lower_bound`,
  {lit}`CLRS.Chapter19.FibHeap.degreeIndex_half_le_log_card`,
  {lit}`CLRS.Chapter19.FibHeap.degreeIndex_le_twice_log_card_add_one`, and
  {lit}`CLRS.Chapter19.FibHeap.degree_bound_log`.

* 19.4 Bounding the maximum degree: {lit}`partial`.
  A concrete rooted-tree model (`FTree`) with the CLRS Lemma 19.1 marked-tree
  invariant ({lit}`CLRS.Chapter19.FTree.Wellformed`), the true subtree-size
  theorem, its golden-ratio consequence, and the logarithmic maximum-degree
  bound.  Main results:
  {lit}`CLRS.Chapter19.FTree.wellformed_size_ge_fibLowerBound`,
  {lit}`CLRS.Chapter19.FTree.goldenRatio_pow_le_fibLowerBound`,
  {lit}`CLRS.Chapter19.FTree.wellformed_goldenRatio_pow_le_size`,
  {lit}`CLRS.Chapter19.FTree.wellformed_degree_le_logb`,
  {lit}`CLRS.Chapter19.FTree.wellformed_degree_le_floor_logb`,
  {lit}`CLRS.Chapter19.FTree.wellformed_degree_le_twice_log_two`,
  {lit}`CLRS.Chapter19.FTree.wellformed_append_child`,
  {lit}`CLRS.Chapter19.FTree.link_wellformed`, and
  {lit}`CLRS.Chapter19.FTree.exists_wellformed_size_eq_fibLowerBound`.

## Current Gaps

The pointer-level circular root lists, the executable `CONSOLIDATE` and
cascading-cut procedures, and the amortized-cost accounting over the potential
function remain strengthening targets.  Section 19.4 now seals the structural
combinatorial core those procedures rely on: the true Fibonacci subtree-size
degree bound `size(x) ≥ F(d+2) ≥ φ^d`, hence `D(n) ≤ ⌊log_φ n⌋`.
-/

namespace CLRS
namespace Chapter19
end Chapter19
end CLRS
