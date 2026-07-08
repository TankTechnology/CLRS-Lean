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

/-! ## Real recursive insertion (CLRS `B-TREE-INSERT-NONFULL`)

The specification `insert` above is a flat stub.  The following develops the
genuine CLRS recursive insertion.  `insertNonFull` descends into the child that
should hold `x`, splitting any full child on the way down (via the ordering of
`splitChild`), and terminates on the tree height `heightOf`.
-/

open List

/-- Insert `x` into a sorted `Nat` list, preserving sortedness. -/
def sortedInsert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | k :: ks => if x ≤ k then x :: k :: ks else k :: sortedInsert x ks

/-- Index of the child that key `x` descends into: the number of leading keys
`≤ x` (correct for a sorted key list). -/
def findChild : List Nat → Nat → Nat
  | [], _ => 0
  | k :: ks, x => if k ≤ x then findChild ks x + 1 else 0

/-! ### Height lemmas for the termination measure -/

/-- `foldl max` never drops below its accumulator. -/
lemma foldl_max_ge (b : Nat) (l : List Nat) : b ≤ l.foldl max b := by
  induction l generalizing b with
  | nil => simp
  | cons y ys ih =>
    simp only [List.foldl_cons]
    exact le_trans (le_max_left b y) (ih (max b y))

/-- Every element of `l` is `≤ l.foldl max b`. -/
lemma mem_le_foldl_max : ∀ {l : List Nat} {a b : Nat}, a ∈ l → a ≤ l.foldl max b := by
  intro l
  induction l with
  | nil => intro a b h; simp at h
  | cons y ys ih =>
    intro a b h
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right b a) (foldl_max_ge (max b a) ys)
    · exact ih h

/-- If every element of `l` is `≤ M` and `b ≤ M`, then `l.foldl max b ≤ M`. -/
lemma foldl_max_le' : ∀ {l : List Nat} {M b : Nat}, b ≤ M → (∀ a ∈ l, a ≤ M) → l.foldl max b ≤ M := by
  intro l
  induction l with
  | nil => intro M b hb _; simpa using hb
  | cons y ys ih =>
    intro M b hb h
    simp only [List.foldl_cons]
    exact ih (max_le hb (h y (by simp))) (fun a ha => h a (by simp [ha]))

/-- Folding `max` over the heights of a sub-multiset of children is `≤` folding
over the full children list. -/
lemma foldl_max_heightOf_subset {cs' cs : List BTree} (h : cs' ⊆ cs) :
    (cs'.map heightOf).foldl max 0 ≤ (cs.map heightOf).foldl max 0 := by
  apply foldl_max_le' (foldl_max_ge 0 _)
  intro a ha
  rw [List.mem_map] at ha
  obtain ⟨c, hc, rfl⟩ := ha
  exact mem_le_foldl_max (List.mem_map_of_mem (h hc))

/-- A child is strictly shorter than its parent. -/
lemma heightOf_mem_lt {ks : List Nat} {children : List BTree} {c : BTree}
    (hc : c ∈ children) : heightOf c < heightOf (node ks children) := by
  cases children with
  | nil => simp at hc
  | cons d ds =>
    have hle := mem_le_foldl_max (a := heightOf c) (b := 0) (List.mem_map_of_mem hc)
    simp only [heightOf]
    omega

/-- Replacing the children of a node by a sub-multiset cannot increase the height. -/
lemma heightOf_le_of_children_subset {a b : List Nat} {cs' cs : List BTree}
    (h : cs' ⊆ cs) : heightOf (node a cs') ≤ heightOf (node b cs) := by
  cases cs' with
  | nil => simp [heightOf]
  | cons d ds =>
    cases cs with
    | nil => exact absurd (h List.mem_cons_self) (by simp)
    | cons e es =>
      have hsub := foldl_max_heightOf_subset (cs' := d :: ds) (cs := e :: es) h
      simp only [heightOf]
      omega

/-! ### `insertNonFull` -/

/--
CLRS `B-TREE-INSERT-NONFULL`.  Assumes (for correctness) that the node is not
full.  On a leaf, `x` is inserted in sorted order.  On an internal node, we
find the child `i` that should hold `x`; if that child is full we split it (its
median rises into this node and it becomes two half-children), then recurse into
whichever half `x` belongs to.  Terminates on `heightOf` since every recursive
call is on a strictly shorter subtree.
-/
def insertNonFull (t x : Nat) : BTree → BTree
  | node ks cs =>
    if cs.isEmpty then
      node (sortedInsert x ks) []
    else
      let i := findChild ks x
      match hc : cs[i]? with
      | none => node ks cs
      | some c =>
        match hcc : c with
        | node cKeys cChildren =>
          if cKeys.length = 2 * t - 1 then
            let median := cKeys.getD (t - 1) 0
            if x < median then
              node (ks.take i ++ median :: ks.drop i)
                (cs.take i ++
                  [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
                   node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (i + 1))
            else
              node (ks.take i ++ median :: ks.drop i)
                (cs.take i ++
                  [node (cKeys.take (t - 1)) (cChildren.take t),
                   insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))] ++ cs.drop (i + 1))
          else
            node ks (cs.set i (insertNonFull t x c))
termination_by tr => heightOf tr
decreasing_by
  all_goals
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨i, hc⟩
    refine lt_of_le_of_lt ?_ (heightOf_mem_lt hmem)
    first
      | exact le_of_eq (congrArg heightOf hcc)
      | exact heightOf_le_of_children_subset (List.take_subset _ _)
      | exact heightOf_le_of_children_subset (List.drop_subset _ _)

end BTree
end Chapter18
end CLRS
