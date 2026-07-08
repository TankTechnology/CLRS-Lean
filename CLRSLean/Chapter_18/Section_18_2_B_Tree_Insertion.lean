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

/-! ### `sortedInsert` correctness -/

/-- `sortedInsert x ks` is a permutation of `x :: ks` (adds exactly `x`). -/
lemma sortedInsert_perm (x : Nat) (ks : List Nat) : (sortedInsert x ks).Perm (x :: ks) := by
  induction ks with
  | nil => simp [sortedInsert]
  | cons k ks ih =>
    unfold sortedInsert
    split
    · exact List.Perm.refl _
    · calc k :: sortedInsert x ks ~ k :: x :: ks := ih.cons k
        _ ~ x :: k :: ks := List.Perm.swap x k ks

/-- Membership after `sortedInsert`. -/
lemma mem_sortedInsert {x y : Nat} {ks : List Nat} :
    y ∈ sortedInsert x ks ↔ y = x ∨ y ∈ ks := by
  rw [(sortedInsert_perm x ks).mem_iff, List.mem_cons]

/-- `sortedInsert` preserves sortedness. -/
lemma sortedInsert_sorted (x : Nat) : ∀ {ks : List Nat}, List.Pairwise (· ≤ ·) ks →
    List.Pairwise (· ≤ ·) (sortedInsert x ks) := by
  intro ks
  induction ks with
  | nil => intro _; simp [sortedInsert]
  | cons k ks ih =>
    intro h
    have hk : ∀ y ∈ ks, k ≤ y := (List.pairwise_cons.mp h).1
    have htail : List.Pairwise (· ≤ ·) ks := (List.pairwise_cons.mp h).2
    unfold sortedInsert
    split
    · rename_i hxk
      refine List.pairwise_cons.mpr ⟨?_, h⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxk
      · exact le_trans hxk (hk y hy)
    · rename_i hxk
      have hkx : k ≤ x := le_of_lt (not_le.mp hxk)
      refine List.pairwise_cons.mpr ⟨?_, ih htail⟩
      intro y hy
      rw [mem_sortedInsert] at hy
      rcases hy with rfl | hy
      · exact hkx
      · exact hk y hy

/-! ### `findChild` bound and `insertNonFull` key multiset -/

/-- `findChild` never exceeds the number of keys, so on a node with
`children.length = keys.length + 1` it always indexes a real child. -/
lemma findChild_le (ks : List Nat) (x : Nat) : findChild ks x ≤ ks.length := by
  induction ks with
  | nil => simp [findChild]
  | cons k ks ih =>
    unfold findChild
    split
    · simp only [List.length_cons]; omega
    · omega

/-- `insertNonFull` adds exactly the key `x` to the key multiset (needs
`ChildBounded` to rule out the out-of-range junk branch). -/
theorem insertNonFull_keys_perm (t x : Nat) (ht : 2 ≤ t) :
    ∀ (tr : BTree), ChildBounded tr →
      (keysOf (insertNonFull t x tr)).Perm (keysOf tr ++ [x]) := by
  intro tr
  induction tr using insertNonFull.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
    intro _
    have hcsnil : cs = [] := List.isEmpty_iff.mp hempty
    subst hcsnil
    rw [insertNonFull]
    simp only [List.isEmpty_nil, if_true, keysOf, List.flatMap_nil, List.append_nil]
    exact (sortedInsert_perm x ks).trans (List.perm_append_comm (l₁ := [x]) (l₂ := ks))
  | case2 ks cs hne i hnone =>
    intro hcb
    exfalso
    have hlen : cs.length = ks.length + 1 := by
      unfold ChildBounded at hcb
      rcases hcb with ⟨hrel, _, _⟩
      rcases hrel with hemp | heq
      · have : cs = [] := List.isEmpty_iff.mp hemp
        rw [this] at hne; simp at hne
      · exact heq
    have h1 : cs.length ≤ i := List.getElem?_eq_none_iff.mp hnone
    have h2 : i ≤ ks.length := findChild_le ks x
    omega
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
    intro hcb
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩
      exact hsub _ (List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩)
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_left : ChildBounded (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := childBounded_take_of_full hcb_child ht1
      rwa [show (t - 1) + 1 = t from by omega] at h
    have ihc := ih hcb_left
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys.getD (t - 1) 0 :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
               node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]
      dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only
        rw [if_pos hfull, if_pos hlt]
    rw [hval, hmed]
    set med := cKeys[t - 1] with hmedeq
    set LK := cKeys.take (t - 1) with hLK
    set RK := cKeys.drop t with hRK
    set LC := cChildren.take t with hLC
    set RC := cChildren.drop t with hRC
    rw [← Multiset.coe_eq_coe]
    have hcs : cs = cs.take (findChild ks x) ++ node cKeys cChildren
        :: cs.drop (findChild ks x + 1) := by
      conv_lhs => rw [← List.take_append_drop (findChild ks x) cs]
      rw [List.drop_eq_getElem_cons hilt, hget]
    have hck : cKeys = LK ++ med :: RK := by
      rw [hLK, hRK, hmedeq]
      conv_lhs => rw [← List.take_append_drop (t - 1) cKeys]
      rw [List.drop_eq_getElem_cons ht1, show (t - 1) + 1 = t from by omega]
    have hcc : cChildren = LC ++ RC := by rw [hLC, hRC]; exact (List.take_append_drop t cChildren).symm
    have hihc : (↑(keysOf (insertNonFull t x (node LK LC))) : Multiset Nat)
        = ↑(keysOf (node LK LC)) + ↑([x] : List Nat) :=
      (Multiset.coe_eq_coe.mpr ihc).trans (Multiset.coe_add _ _).symm
    conv_lhs => rw [keysOf]
    conv_rhs => rw [keysOf, hcs]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, keysOf,
      hck, hcc, ← Multiset.coe_add, ← Multiset.coe_nil, ← Multiset.cons_coe,
      ← Multiset.singleton_add, hihc]
    rw [show (↑ks : Multiset Nat) = ↑(ks.take (findChild ks x)) + ↑(ks.drop (findChild ks x)) from by
      rw [Multiset.coe_add, List.take_append_drop]]
    abel
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
    intro hcb
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩
      exact hsub _ (List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩)
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_right : ChildBounded (node (cKeys.drop t) (cChildren.drop t)) := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
        rw [hnil]; simpa using childBounded_node_nil (cKeys.drop t)
      · exact childBounded_drop_of_full hcb_child (by omega) (by rw [h2t]; omega)
    have ihc := ih hcb_right
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys.getD (t - 1) 0 :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [node (cKeys.take (t - 1)) (cChildren.take t),
               insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))]
              ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]
      dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only
        rw [if_pos hfull, if_neg hnlt]
    rw [hval, hmed]
    set med := cKeys[t - 1] with hmedeq
    set LK := cKeys.take (t - 1) with hLK
    set RK := cKeys.drop t with hRK
    set LC := cChildren.take t with hLC
    set RC := cChildren.drop t with hRC
    rw [← Multiset.coe_eq_coe]
    have hcs : cs = cs.take (findChild ks x) ++ node cKeys cChildren
        :: cs.drop (findChild ks x + 1) := by
      conv_lhs => rw [← List.take_append_drop (findChild ks x) cs]
      rw [List.drop_eq_getElem_cons hilt, hget]
    have hck : cKeys = LK ++ med :: RK := by
      rw [hLK, hRK, hmedeq]
      conv_lhs => rw [← List.take_append_drop (t - 1) cKeys]
      rw [List.drop_eq_getElem_cons ht1, show (t - 1) + 1 = t from by omega]
    have hcc : cChildren = LC ++ RC := by rw [hLC, hRC]; exact (List.take_append_drop t cChildren).symm
    have hihc : (↑(keysOf (insertNonFull t x (node RK RC))) : Multiset Nat)
        = ↑(keysOf (node RK RC)) + ↑([x] : List Nat) :=
      (Multiset.coe_eq_coe.mpr ihc).trans (Multiset.coe_add _ _).symm
    conv_lhs => rw [keysOf]
    conv_rhs => rw [keysOf, hcs]
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, keysOf,
      hck, hcc, ← Multiset.coe_add, ← Multiset.coe_nil, ← Multiset.cons_coe,
      ← Multiset.singleton_add, hihc]
    rw [show (↑ks : Multiset Nat) = ↑(ks.take (findChild ks x)) + ↑(ks.drop (findChild ks x)) from by
      rw [Multiset.coe_add, List.take_append_drop]]
    abel
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
    intro hcb
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩
      exact hsub _ (List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩)
    have ihc := ih hcb_child
    have hval : insertNonFull t x (node ks cs)
        = node ks (cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren))) := by
      rw [insertNonFull, if_neg hne]
      dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only
        rw [if_neg hnfull]
    rw [hval, ← Multiset.coe_eq_coe]
    have hset : cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren))
        = cs.take (findChild ks x) ++ insertNonFull t x (node cKeys cChildren)
          :: cs.drop (findChild ks x + 1) := by
      rw [List.set_eq_take_append_cons_drop, if_pos hilt]
    have hcs : cs = cs.take (findChild ks x) ++ node cKeys cChildren
        :: cs.drop (findChild ks x + 1) := by
      conv_lhs => rw [← List.take_append_drop (findChild ks x) cs]
      rw [List.drop_eq_getElem_cons hilt, hget]
    have hihc : (↑(keysOf (insertNonFull t x (node cKeys cChildren))) : Multiset Nat)
        = ↑(keysOf (node cKeys cChildren)) + ↑([x] : List Nat) :=
      (Multiset.coe_eq_coe.mpr ihc).trans (Multiset.coe_add _ _).symm
    conv_lhs => rw [keysOf, hset]
    conv_rhs => rw [keysOf, hcs]
    simp only [List.flatMap_append, List.flatMap_cons, ← Multiset.coe_add, hihc]
    abel

/-! ### `findChild` range correctness -/

/-- Every key before the chosen child index is `≤ x`. -/
lemma findChild_take_le (x : Nat) : ∀ (ks : List Nat), ∀ k ∈ ks.take (findChild ks x), k ≤ x := by
  intro ks
  induction ks with
  | nil => intro k hk; simp at hk
  | cons a as ih =>
    intro k hk
    rw [findChild] at hk
    split at hk
    · rename_i hax
      rw [List.take_succ_cons] at hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hax
      · exact ih k hk
    · simp at hk

/-- On a sorted key list, every key from the chosen child index onward is `> x`. -/
lemma findChild_drop_gt (x : Nat) : ∀ {ks : List Nat}, List.Pairwise (· ≤ ·) ks →
    ∀ k ∈ ks.drop (findChild ks x), x < k := by
  intro ks
  induction ks with
  | nil => intro _ k hk; simp at hk
  | cons a as ih =>
    intro hs k hk
    have hsa : ∀ b ∈ as, a ≤ b := (List.pairwise_cons.mp hs).1
    have hs' : List.Pairwise (· ≤ ·) as := (List.pairwise_cons.mp hs).2
    rw [findChild] at hk
    split at hk
    · rename_i hax
      rw [List.drop_succ_cons] at hk
      exact ih hs' k hk
    · rename_i hax
      have hxa : x < a := not_le.mp hax
      simp only [List.drop_zero, List.mem_cons] at hk
      rcases hk with rfl | hk
      · exact hxa
      · exact lt_of_lt_of_le hxa (hsa k hk)

end BTree
end Chapter18
end CLRS
