import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.3 - B-tree deletion specification

This section adds a first-pass deletion specification over the mathematical
B-tree key-membership model.  It deliberately stays at the set-membership layer:
the operation filters the represented key list and later refinements can replace
it with the full CLRS node-level borrow/merge algorithm.

Main results:

- Theorem {lit}`BTree.delete_preserves_model`: specification deletion preserves
  the first-pass validity predicate.
- Theorem {lit}`BTree.delete_mem_iff`: after deletion, membership is exactly
  membership of a key different from the deleted key.
- Theorem {lit}`BTree.delete_search_iff`: searching after deletion succeeds
  exactly for old searchable keys different from the deleted key.
- Theorem {lit}`BTree.delete_search_false_iff`: searching after deletion fails
  exactly for the deleted key or keys that failed before.
- Theorem {lit}`BTree.delete_search_false_old`: old unsuccessful searches
  remain unsuccessful after deletion.
- Theorem {lit}`BTree.delete_not_mem_iff`: membership after deletion fails
  exactly for the deleted key or keys that were absent before.
- Theorems {lit}`BTree.delete_not_mem` and
  {lit}`BTree.delete_search_deleted_false`: the deleted key is absent and not
  searchable after deletion.
- Theorems {lit}`BTree.delete_mem_of_ne` and
  {lit}`BTree.delete_search_of_ne`: old keys different from the deleted key
  remain present and searchable after deletion.

Current gaps:

- Node-level underflow repair, sibling borrowing, merging, and disk-page
  semantics remain strengthening targets.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-- Specification-level B-tree deletion: remove all occurrences of a key. -/
def delete (x : Nat) (t : BTree) : BTree :=
  node ((keysOf t).filter (fun y => y != x)) []

/-- Specification deletion preserves the first-pass validity predicate. -/
theorem delete_preserves_model {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (delete x t) := by
  exact hvalid

/-- Specification deletion removes exactly the requested key from membership. -/
theorem delete_mem_iff (x y : Nat) (t : BTree) :
    mem y (delete x t) <-> y != x ∧ mem y t := by
  simp [delete, mem, keysOf]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-- The deleted key is absent after specification deletion. -/
theorem delete_not_mem (x : Nat) (t : BTree) :
    ¬ mem x (delete x t) := by
  rw [delete_mem_iff x x t]
  simp

/-- Old keys different from the deleted key remain present after deletion. -/
theorem delete_mem_of_ne (x y : Nat) (t : BTree)
    (hxy : (y != x) = true) (hy : mem y t) :
    mem y (delete x t) := by
  rw [delete_mem_iff]
  exact ⟨hxy, hy⟩

/-- Membership after deletion fails exactly for the deleted key or old absent keys. -/
theorem delete_not_mem_iff (x y : Nat) (t : BTree) :
    ¬ mem y (delete x t) <-> y = x ∨ ¬ mem y t := by
  rw [delete_mem_iff]
  constructor
  · intro hnot
    by_cases hyx : y = x
    · exact Or.inl hyx
    · right
      intro hy
      have hne : (y != x) = true := by
        simp [hyx]
      exact hnot ⟨hne, hy⟩
  · intro h hmem
    cases h with
    | inl hyx =>
        rw [hyx] at hmem
        simp at hmem
    | inr hyNot =>
        exact hyNot hmem.2

/-- Searching after deletion succeeds exactly for remaining old keys. -/
theorem delete_search_iff {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (delete x t) = true <-> (y != x) = true ∧ search y t = true := by
  have hdelete : Valid minDegree (delete x t) :=
    delete_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := y) (t := delete x t) hdelete]
  rw [delete_mem_iff]
  rw [← search_correct (minDegree := minDegree) (x := y) (t := t) hvalid]

/-- Searching for the deleted key fails after specification deletion. -/
theorem delete_search_deleted_false {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search x (delete x t) = false := by
  have hdelete : Valid minDegree (delete x t) :=
    delete_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  cases hsearch : search x (delete x t)
  · rfl
  · have hmem :
        mem x (delete x t) :=
        (search_correct (minDegree := minDegree) (x := x) (t := delete x t) hdelete).mp hsearch
    exact False.elim ((delete_not_mem x t) hmem)

/-- Old searchable keys different from the deleted key remain searchable after deletion. -/
theorem delete_search_of_ne {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : (y != x) = true)
    (hy : search y t = true) :
    search y (delete x t) = true := by
  rw [delete_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact ⟨hxy, hy⟩

/-- Searching after deletion fails exactly for the deleted key or an old failed search. -/
theorem delete_search_false_iff {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (delete x t) = false <-> y = x ∨ search y t = false := by
  constructor
  · intro hdeleteFalse
    by_cases hxy : y = x
    · exact Or.inl hxy
    · right
      cases hold : search y t
      · rfl
      · have hneq : (y != x) = true := by
          simp [hxy]
        have hdeleteTrue : search y (delete x t) = true :=
          (delete_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid).mpr
            ⟨hneq, hold⟩
        rw [hdeleteFalse] at hdeleteTrue
        contradiction
  · intro h
    cases h with
    | inl hyx =>
        rw [hyx]
        exact delete_search_deleted_false (minDegree := minDegree) (x := x) (t := t) hvalid
    | inr holdFalse =>
        cases hdelete : search y (delete x t)
        · rfl
        · have hcases : (y != x) = true ∧ search y t = true :=
            (delete_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid).mp
              hdelete
          rw [holdFalse] at hcases
          simp at hcases

/-- Old unsuccessful searches remain unsuccessful after specification deletion. -/
theorem delete_search_false_old {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hy : search y t = false) :
    search y (delete x t) = false := by
  rw [delete_search_false_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact Or.inr hy

end BTree
end Chapter18
end CLRS
