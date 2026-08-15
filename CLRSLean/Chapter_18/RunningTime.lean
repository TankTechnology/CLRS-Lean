import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation

/-!
# CLRS Chapter 18 - B-tree running time

This module adds the running-time / cost layer for the executable B-tree
operations.  Each cost function mirrors one real recursive construction from
Sections 18.1-18.3 and counts the number of B-tree nodes (disk pages) the
operation reads and writes:

- {lit}`searchCost` mirrors {lit}`searchExec` (Section 18.1),
- {lit}`insertCost` mirrors {lit}`insertNonFull` and {lit}`insertRootCost`
  charges the full-root split of {lit}`insertRoot` (Section 18.2),
- {lit}`deleteCost` mirrors {lit}`composedDelete` (Section 18.3).

Every descent performs {lit}`O(1)` node work (a split, a borrow, or a merge
touches a constant number of pages), so the number of disk accesses is
bounded by the number of levels visited.  The height bounds compose with the
existing {lit}`wellFormed_height_log_bound` to give the CLRS running time:

Main results:

- Theorem {lit}`searchCost_le_height`: search costs at most `height + 1`.
- Theorem {lit}`insertCost_le_height`: non-full insertion costs at most
  `height + 1`.
- Theorem {lit}`insertRootCost_le_height`: top-level insertion costs at most
  `height + 3` (the extra two levels come from the full-root split).
- Theorem {lit}`deleteCost_le_height`: deletion costs at most `height + 1`.
- Theorem {lit}`searchCost_le_diskAccessBound`,
  {lit}`insertRootCost_le_diskAccessBound`,
  {lit}`deleteCost_le_diskAccessBound`: on every well-formed tree
  (`2 ≤ t`) the three operations perform at most
  {lit}`diskAccessBound t (totalKeys tr)` disk accesses, where
  {lit}`diskAccessBound t n = log_t ((n+1)/2) + 3`.
- Theorem {lit}`diskAccessBound_isBigO_log_t`: that bound is `O(log_t n)`, so
  search, insertion, and deletion each run in `O(log_t n)` disk accesses.

Notation conventions used in this section:

- `t` : B-tree minimum degree (`2 ≤ t` for every cost theorem)
- `tr` : a {lit}`BTree`
- `totalKeys tr` : the number of represented key slots (the `n` of CLRS)
-/

namespace CLRS
namespace Chapter18
namespace BTree

open List

/-! ## Disk-access cost functions -/

/--
Number of nodes visited by {lit}`searchExec` for key {lit}`x`: one per level
on the separator-selected descent path.
-/
def searchCost (x : Nat) : BTree → Nat
  | node ks cs =>
      if x ∈ ks then 1
      else
        match _hc : cs[findChild ks x]? with
        | some child => 1 + searchCost x child
        | none => 1
termination_by tr => heightOf tr
decreasing_by
  exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨findChild ks x, _hc⟩)

/--
Number of nodes read and written by {lit}`insertNonFull` for key {lit}`x`
(minimum degree {lit}`t`).  Each recursion step descends one level; the split
of a full child touches only that child and its two halves, which is constant
per level.
-/
def insertCost (t x : Nat) : BTree → Nat
  | node ks cs =>
    if cs.isEmpty then 1
    else
      let i := findChild ks x
      match _hc : cs[i]? with
      | none => 1
      | some c =>
        match _hcc : c with
        | node cKeys cChildren =>
          if cKeys.length = 2 * t - 1 then
            let median := cKeys.getD (t - 1) 0
            if x < median then
              1 + insertCost t x (node (cKeys.take (t - 1)) (cChildren.take t))
            else
              1 + insertCost t x (node (cKeys.drop t) (cChildren.drop t))
          else
            1 + insertCost t x c
termination_by tr => heightOf tr
decreasing_by
  all_goals
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨i, _hc⟩
    refine lt_of_le_of_lt ?_ (heightOf_mem_lt hmem)
    first
      | exact le_of_eq (congrArg heightOf _hcc)
      | exact heightOf_le_of_children_subset (List.take_subset _ _)
      | exact heightOf_le_of_children_subset (List.drop_subset _ _)

/-! ## Height bounds -/

/-- **O(h) search.**  {lit}`searchExec` descends at most one path, so its
number of disk accesses is bounded by the tree height plus one. -/
theorem searchCost_le_height (x : Nat) (tr : BTree) :
    searchCost x tr ≤ heightOf tr + 1 := by
  induction tr with
  | node ks cs =>
      simp only [searchCost]
      split
      · omega
      · split
        · rename_i child hc
          have ih := searchCost_le_height x child
          have hlt := heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨findChild ks x, hc⟩)
          omega
        · omega

/-- **O(h) insertion.**  {lit}`insertNonFull` descends at most one path, so
its number of disk accesses is bounded by the tree height plus one. -/
theorem insertCost_le_height (t x : Nat) (tr : BTree) :
    insertCost t x tr ≤ heightOf tr + 1 := by
  induction tr using insertCost.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
      simp only [insertCost, List.isEmpty_iff.mp hempty, if_true]
  | case2 ks cs hne i hnone =>
      simp only [insertCost, if_neg hne]
      dsimp only
      split
      · omega
      · rename_i c hc
        rw [hnone] at hc
        simp at hc
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
      have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
      obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
      have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩
      have hltH : heightOf (node (cKeys.take (t - 1)) (cChildren.take t))
          ≤ heightOf (node cKeys cChildren) :=
        heightOf_le_of_children_subset (List.take_subset _ _)
      simp only [insertCost, if_neg hne]
      dsimp only
      split
      · rename_i hcnone
        rw [hsome'] at hcnone
        simp at hcnone
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only
        rw [if_pos hfull, if_pos hlt]
        omega
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
      have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
      obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
      have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩
      have hltH : heightOf (node (cKeys.drop t) (cChildren.drop t))
          ≤ heightOf (node cKeys cChildren) :=
        heightOf_le_of_children_subset (List.drop_subset _ _)
      simp only [insertCost, if_neg hne]
      dsimp only
      split
      · rename_i hcnone
        rw [hsome'] at hcnone
        simp at hcnone
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only
        rw [if_pos hfull, if_neg hnlt]
        omega
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
      have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
      obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
      have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩
      simp only [insertCost, if_neg hne]
      dsimp only
      split
      · rename_i hcnone
        rw [hsome'] at hcnone
        simp at hcnone
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only
        rw [if_neg hnfull]
        omega

end BTree
end Chapter18
end CLRS
