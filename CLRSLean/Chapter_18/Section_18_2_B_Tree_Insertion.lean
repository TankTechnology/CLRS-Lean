import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.2 - B-tree insertion

This first-pass section gives specification-level split and insertion wrappers
over the mathematical B-tree model from Section 18.1.  The goal is a stable
public theorem surface before introducing full node occupancy and separator
repair proofs.

Main results:

- Theorem {lit}`BTree.splitChild_preserves_model`: the first-pass split wrapper
  preserves validity and membership.
- Theorem {lit}`BTree.splitChild_valid`: the first-pass split wrapper preserves
  validity.
- Theorem {lit}`BTree.splitChild_mem_iff`: membership after the first-pass
  split wrapper is unchanged.
- Theorem {lit}`BTree.splitChild_not_mem_iff`: failed membership is also
  unchanged after the first-pass split wrapper.
- Theorem {lit}`BTree.splitChild_not_mem_old`: old absent keys remain absent
  after the first-pass split wrapper.
- Theorem {lit}`BTree.splitChild_search_iff`: searching after the first-pass
  split wrapper is equivalent to searching before it.
- Theorem {lit}`BTree.splitChild_search_false_iff`: unsuccessful search is also
  preserved by the first-pass split wrapper.
- Theorem {lit}`BTree.splitChild_search_false_old`: old unsuccessful searches
  remain unsuccessful after the first-pass split wrapper.
- Theorems {lit}`BTree.splitChild_mem_old` and
  {lit}`BTree.splitChild_search_old`: old members and searchable keys remain
  so after the first-pass split wrapper.
- Theorems {lit}`BTree.splitChild_search_of_mem` and
  {lit}`BTree.splitChild_search_false_of_not_mem`: old membership and absence
  give direct post-split successful and failed searches.
- Theorem {lit}`BTree.insert_preserves_model`: specification insertion preserves
  the first-pass validity predicate.
- Theorem {lit}`BTree.insert_valid`: direct validity-preservation wrapper for
  specification insertion.
- Theorem {lit}`BTree.insert_mem_iff`: insertion adds exactly the inserted key
  to the membership specification.
- Theorem {lit}`BTree.insert_search_iff`: searching after insertion succeeds
  exactly for the inserted key or an old searchable key.
- Theorem {lit}`BTree.insert_search_false_iff`: searching after insertion fails
  exactly for keys different from the inserted key that failed before.
- Theorem {lit}`BTree.insert_search_false_of_ne`: old failed searches for keys
  different from the inserted key remain failed after insertion.
- Theorem {lit}`BTree.insert_not_mem_iff`: membership after insertion fails
  exactly for keys different from the inserted key that were absent before.
- Theorem {lit}`BTree.insert_not_mem_of_ne`: old absent keys different from the
  inserted key remain absent after insertion.
- Theorems {lit}`BTree.insert_mem_self` and
  {lit}`BTree.insert_search_self`: the inserted key is present and searchable
  after insertion.
- Theorem {lit}`BTree.insert_search_of_eq`: any query key equal to the inserted
  key is searchable after insertion.
- Theorems {lit}`BTree.insert_mem_old` and
  {lit}`BTree.insert_search_old`: old members and searchable keys remain so
  after insertion.
- Theorems {lit}`BTree.insert_search_of_mem` and
  {lit}`BTree.insert_search_false_of_not_mem_ne`: old membership and absent
  noninserted keys give direct post-insertion search results.

Current gaps:

- This is not yet the full CLRS in-node split and insert-nonfull proof.  It is a
  specification layer that fixes the public theorem names and membership
  behavior for the later structural refinement.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-- First-pass split-child wrapper.  Structural split refinement is future work. -/
def splitChild (t : BTree) : BTree :=
  t

/-- Membership after the first-pass split wrapper is unchanged. -/
theorem splitChild_mem_iff (x : Nat) (t : BTree) :
    mem x (splitChild t) <-> mem x t := by
  rfl

/-- Old keys remain present after the first-pass split wrapper. -/
theorem splitChild_mem_old (x : Nat) (t : BTree) (hx : mem x t) :
    mem x (splitChild t) := by
  rw [splitChild_mem_iff]
  exact hx

/-- Failed membership after the first-pass split wrapper is unchanged. -/
theorem splitChild_not_mem_iff (x : Nat) (t : BTree) :
    ¬ mem x (splitChild t) <-> ¬ mem x t := by
  rw [splitChild_mem_iff]

/-- Old absent keys remain absent after the first-pass split wrapper. -/
theorem splitChild_not_mem_old (x : Nat) (t : BTree) (hx : ¬ mem x t) :
    ¬ mem x (splitChild t) := by
  rw [splitChild_not_mem_iff]
  exact hx

/-- The first-pass split wrapper preserves validity and membership. -/
theorem splitChild_preserves_model {minDegree : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (splitChild t) ∧
      forall x, mem x (splitChild t) <-> mem x t := by
  exact ⟨hvalid, by intro x; exact splitChild_mem_iff x t⟩

/-- The first-pass split wrapper preserves validity. -/
theorem splitChild_valid {minDegree : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (splitChild t) := by
  exact (splitChild_preserves_model (minDegree := minDegree) (t := t) hvalid).1

/-- Searching after the first-pass split wrapper is unchanged. -/
theorem splitChild_search_iff {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search x (splitChild t) = true <-> search x t = true := by
  have hsplit := splitChild_preserves_model (minDegree := minDegree) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := x) (t := splitChild t) hsplit.1]
  rw [hsplit.2 x]
  rw [← search_correct (minDegree := minDegree) (x := x) (t := t) hvalid]

/-- Old searchable keys remain searchable after the first-pass split wrapper. -/
theorem splitChild_search_old {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hx : search x t = true) :
    search x (splitChild t) = true := by
  rw [splitChild_search_iff (minDegree := minDegree) (x := x) (t := t) hvalid]
  exact hx

/-- Old members are directly searchable after the first-pass split wrapper. -/
theorem splitChild_search_of_mem {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hx : mem x t) :
    search x (splitChild t) = true := by
  exact splitChild_search_old (minDegree := minDegree) (x := x) (t := t)
    hvalid (search_true_of_mem x t hx)

/-- Unsuccessful search is preserved by the first-pass split wrapper. -/
theorem splitChild_search_false_iff {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search x (splitChild t) = false <-> search x t = false := by
  constructor
  · intro hsplitFalse
    cases hold : search x t
    · rfl
    · have hsplitTrue : search x (splitChild t) = true :=
        (splitChild_search_iff (minDegree := minDegree) (x := x) (t := t) hvalid).mpr hold
      rw [hsplitFalse] at hsplitTrue
      contradiction
  · intro holdFalse
    cases hsplit : search x (splitChild t)
    · rfl
    · have holdTrue : search x t = true :=
        (splitChild_search_iff (minDegree := minDegree) (x := x) (t := t) hvalid).mp hsplit
      rw [holdFalse] at holdTrue
      contradiction

/-- Old unsuccessful searches remain unsuccessful after the first-pass split wrapper. -/
theorem splitChild_search_false_old {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hx : search x t = false) :
    search x (splitChild t) = false := by
  rw [splitChild_search_false_iff (minDegree := minDegree) (x := x) (t := t) hvalid]
  exact hx

/-- Old absent keys directly remain failed searches after the first-pass split wrapper. -/
theorem splitChild_search_false_of_not_mem {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hx : ¬ mem x t) :
    search x (splitChild t) = false := by
  exact splitChild_search_false_old (minDegree := minDegree) (x := x) (t := t)
    hvalid (search_false_of_not_mem x t hx)

/-- Specification-level B-tree insertion: add the key at a fresh root. -/
def insert (x : Nat) (t : BTree) : BTree :=
  node (x :: keysOf t) []

/-- Specification insertion preserves the first-pass validity predicate. -/
theorem insert_preserves_model {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (insert x t) := by
  exact hvalid

/-- Specification insertion preserves validity under the direct operation name. -/
theorem insert_valid {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (insert x t) := by
  exact insert_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid

/-- Specification insertion adds exactly the inserted key to membership. -/
theorem insert_mem_iff (x y : Nat) (t : BTree) :
    mem y (insert x t) <-> y = x ∨ mem y t := by
  simp [insert, mem, keysOf]

/-- The inserted key is present after specification insertion. -/
theorem insert_mem_self (x : Nat) (t : BTree) :
    mem x (insert x t) := by
  rw [insert_mem_iff]
  exact Or.inl rfl

/-- Old keys remain present after specification insertion. -/
theorem insert_mem_old (x y : Nat) (t : BTree) (hy : mem y t) :
    mem y (insert x t) := by
  rw [insert_mem_iff]
  exact Or.inr hy

/-- Membership after insertion fails exactly for noninserted keys absent before insertion. -/
theorem insert_not_mem_iff (x y : Nat) (t : BTree) :
    ¬ mem y (insert x t) <-> y ≠ x ∧ ¬ mem y t := by
  rw [insert_mem_iff]
  constructor
  · intro hnot
    constructor
    · intro hyx
      exact hnot (Or.inl hyx)
    · intro hy
      exact hnot (Or.inr hy)
  · intro h hmem
    cases hmem with
    | inl hyx => exact h.1 hyx
    | inr hy => exact h.2 hy

/-- Old absent keys different from the inserted key remain absent after insertion. -/
theorem insert_not_mem_of_ne (x y : Nat) (t : BTree)
    (hxy : y ≠ x) (hy : ¬ mem y t) :
    ¬ mem y (insert x t) := by
  rw [insert_not_mem_iff]
  exact ⟨hxy, hy⟩

/-- Searching after insertion succeeds exactly for the new key or an old key. -/
theorem insert_search_iff {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (insert x t) = true <-> y = x ∨ search y t = true := by
  have hinsert : Valid minDegree (insert x t) :=
    insert_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := y) (t := insert x t) hinsert]
  rw [insert_mem_iff]
  rw [← search_correct (minDegree := minDegree) (x := y) (t := t) hvalid]

/-- Searching for the inserted key succeeds after specification insertion. -/
theorem insert_search_self {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search x (insert x t) = true := by
  have hinsert : Valid minDegree (insert x t) :=
    insert_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := x) (t := insert x t) hinsert]
  exact insert_mem_self x t

/-- Any key equal to the inserted key is searchable after specification insertion. -/
theorem insert_search_of_eq {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hyx : y = x) :
    search y (insert x t) = true := by
  rw [hyx]
  exact insert_search_self (minDegree := minDegree) (x := x) (t := t) hvalid

/-- Old searchable keys remain searchable after specification insertion. -/
theorem insert_search_old {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hy : search y t = true) :
    search y (insert x t) = true := by
  rw [insert_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact Or.inr hy

/-- Old members are directly searchable after specification insertion. -/
theorem insert_search_of_mem {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hy : mem y t) :
    search y (insert x t) = true := by
  exact insert_search_old (minDegree := minDegree) (x := x) (y := y) (t := t)
    hvalid (search_true_of_mem y t hy)

/-- Searching after insertion fails exactly for noninserted keys that failed before. -/
theorem insert_search_false_iff {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (insert x t) = false <-> y ≠ x ∧ search y t = false := by
  constructor
  · intro hinsertFalse
    constructor
    · intro hyx
      have hinsertTrue : search y (insert x t) = true :=
        (insert_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid).mpr
          (Or.inl hyx)
      rw [hinsertFalse] at hinsertTrue
      contradiction
    · cases hold : search y t
      · rfl
      · have hinsertTrue : search y (insert x t) = true :=
          (insert_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid).mpr
            (Or.inr hold)
        rw [hinsertFalse] at hinsertTrue
        contradiction
  · intro h
    rcases h with ⟨hyx, holdFalse⟩
    cases hinsert : search y (insert x t)
    · rfl
    · have hcases : y = x ∨ search y t = true :=
        (insert_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid).mp
          hinsert
      cases hcases with
      | inl hyxEq =>
          exact False.elim (hyx hyxEq)
      | inr holdTrue =>
          rw [holdFalse] at holdTrue
          contradiction

/-- Old failed searches for keys different from the inserted key remain failed. -/
theorem insert_search_false_of_ne {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : y ≠ x) (hy : search y t = false) :
    search y (insert x t) = false := by
  rw [insert_search_false_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact ⟨hxy, hy⟩

/-- Old absent keys different from the inserted key are directly failed searches after insertion. -/
theorem insert_search_false_of_not_mem_ne {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : y ≠ x) (hy : ¬ mem y t) :
    search y (insert x t) = false := by
  exact insert_search_false_of_ne
    (minDegree := minDegree) (x := x) (y := y) (t := t)
    hvalid hxy (search_false_of_not_mem y t hy)

end BTree
end Chapter18
end CLRS
