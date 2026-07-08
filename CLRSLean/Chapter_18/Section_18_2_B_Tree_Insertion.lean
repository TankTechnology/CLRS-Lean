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

/-! ### `SameDepth` and height preservation -/

/-- Membership characterisation of `SameDepth`: all children are `SameDepth` and
share a common height.  Easier to construct/destruct than the inductive form. -/
lemma sameDepth_iff {ks : List Nat} {cs : List BTree} :
    SameDepth (node ks cs) ↔
      (∀ c ∈ cs, SameDepth c) ∧ ∀ c ∈ cs, ∀ d ∈ cs, heightOf c = heightOf d := by
  constructor
  · intro hsd
    refine ⟨?_, ?_⟩
    · intro c hc
      cases cs with
      | nil => simp at hc
      | cons c0 cs' =>
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact sameDepth_head_sd hsd
        · exact sameDepth_tail_sd hsd c hc'
    · cases cs with
      | nil => intro c hc; simp at hc
      | cons c0 cs' => exact sameDepth_children_eq_height hsd
  · rintro ⟨hsd_all, hheight⟩
    cases cs with
    | nil => exact SameDepth.leaf ks
    | cons c0 cs' =>
      refine SameDepth.internal ks c0 cs' ?_ ?_ ?_
      · intro c hc; exact hheight c (by simp [hc]) c0 (by simp)
      · exact hsd_all c0 (by simp)
      · intro c hc; exact hsd_all c (by simp [hc])

/-- For a `SameDepth` node, its height is one more than any child's height. -/
lemma heightOf_sameDepth_mem {ks : List Nat} {cs : List BTree} {c : BTree}
    (hsd : SameDepth (node ks cs)) (hc : c ∈ cs) : heightOf (node ks cs) = 1 + heightOf c := by
  cases cs with
  | nil => simp at hc
  | cons c0 cs' =>
    rw [heightOf_internal_of_sameDepth hsd]
    congr 1
    exact (sameDepth_iff.mp hsd).2 c0 (by simp) c hc

/-- `heightOf` depends only on the children, not the keys. -/
lemma heightOf_keys_irrel (a b : List Nat) (cs : List BTree) :
    heightOf (node a cs) = heightOf (node b cs) := by
  cases cs with
  | nil => simp [heightOf]
  | cons c cs' => simp only [heightOf]

/-- Height of the two split halves equals the height of the original full child. -/
lemma heightOf_halves_eq {t : Nat} {cKeys : List Nat} {cChildren : List BTree}
    (hsd : SameDepth (node cKeys cChildren)) (ht_pos : 0 < t)
    (h_children : cChildren = [] ∨ t < cChildren.length) :
    heightOf (node (cKeys.take (t - 1)) (cChildren.take t)) = heightOf (node cKeys cChildren) ∧
    heightOf (node (cKeys.drop t) (cChildren.drop t)) = heightOf (node cKeys cChildren) := by
  have h := heightOf_split_parts_eq cKeys cChildren t hsd ht_pos h_children
  simp only [List.splitAt_eq] at h
  refine ⟨h.1, ?_⟩
  rw [heightOf_keys_irrel (cKeys.drop t) ((cKeys.drop (t - 1)).drop 1) (cChildren.drop t)]
  exact h.2

/-- `insertNonFull` preserves `SameDepth` and the total height (given the tree is
`ChildBounded` and `SameDepth`). -/
lemma insertNonFull_sameDepth_height (t x : Nat) (ht : 2 ≤ t) :
    ∀ tr, ChildBounded tr → SameDepth tr →
      SameDepth (insertNonFull t x tr) ∧ heightOf (insertNonFull t x tr) = heightOf tr := by
  intro tr
  induction tr using insertNonFull.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
    intro _ _
    have hcsnil : cs = [] := List.isEmpty_iff.mp hempty
    subst hcsnil
    rw [insertNonFull]
    simp only [List.isEmpty_nil, if_true]
    exact ⟨SameDepth.leaf _, heightOf_keys_irrel _ _ _⟩
  | case2 ks cs hne i hnone =>
    intro _ hsd
    have hval : insertNonFull t x (node ks cs) = node ks cs := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rfl
      · rename_i c hcsome
        have hn : cs[findChild ks x]? = none := hnone
        rw [hcsome] at hn; simp at hn
    rw [hval]; exact ⟨hsd, rfl⟩
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
    intro hcb hsd
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hsd_child : SameDepth (node cKeys cChildren) := (sameDepth_iff.mp hsd).1 _ hmem
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have h_children : cChildren = [] ∨ t < cChildren.length := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · left; cases cChildren with | nil => rfl | cons a b => simp at h0
      · right; rw [h2t]; omega
    have hcb_LH : ChildBounded (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := childBounded_take_of_full hcb_child ht1
      rwa [show (t - 1) + 1 = t from by omega] at h
    have hsd_LH : SameDepth (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := sameDepth_take cKeys cChildren t hsd_child (by omega)
      simpa [List.splitAt_eq] using h
    have hsd_RH : SameDepth (node (cKeys.drop t) (cChildren.drop t)) := by
      have h := sameDepth_drop cKeys cChildren t hsd_child (by omega)
      simp only [List.splitAt_eq] at h
      rw [sameDepth_iff] at h ⊢; exact h
    obtain ⟨ihsd, ihht⟩ := ih hcb_LH hsd_LH
    have hheq := heightOf_halves_eq hsd_child (by omega) h_children
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys.getD (t - 1) 0 :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
               node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_pos hlt]
    rw [hval]
    have hHT : ∀ c'' ∈ cs.take (findChild ks x) ++
        [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
         node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1),
        heightOf c'' = heightOf (node cKeys cChildren) := by
      intro c'' hc''
      rcases List.mem_append.mp hc'' with h1 | h2
      · rcases List.mem_append.mp h1 with hta | hmid
        · exact (sameDepth_iff.mp hsd).2 c'' ((List.take_subset _ _) hta) _ hmem
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
          rcases hmid with rfl | rfl
          · rw [ihht]; exact hheq.1
          · exact hheq.2
      · exact (sameDepth_iff.mp hsd).2 c'' ((List.drop_subset _ _) h2) _ hmem
    have hSD : ∀ c'' ∈ cs.take (findChild ks x) ++
        [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
         node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1),
        SameDepth c'' := by
      intro c'' hc''
      rcases List.mem_append.mp hc'' with h1 | h2
      · rcases List.mem_append.mp h1 with hta | hmid
        · exact (sameDepth_iff.mp hsd).1 c'' ((List.take_subset _ _) hta)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
          rcases hmid with rfl | rfl
          · exact ihsd
          · exact hsd_RH
      · exact (sameDepth_iff.mp hsd).1 c'' ((List.drop_subset _ _) h2)
    refine ⟨sameDepth_iff.mpr ⟨hSD, fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩, ?_⟩
    have hmem_res : insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)) ∈
        cs.take (findChild ks x) ++
          [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
           node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1) := by
      apply List.mem_append_left; apply List.mem_append_right; simp
    rw [heightOf_sameDepth_mem (sameDepth_iff.mpr ⟨hSD, fun a ha b hb =>
          (hHT a ha).trans (hHT b hb).symm⟩) hmem_res, hHT _ hmem_res,
        heightOf_sameDepth_mem hsd hmem]
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
    intro hcb hsd
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hsd_child : SameDepth (node cKeys cChildren) := (sameDepth_iff.mp hsd).1 _ hmem
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have h_children : cChildren = [] ∨ t < cChildren.length := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · left; cases cChildren with | nil => rfl | cons a b => simp at h0
      · right; rw [h2t]; omega
    have hcb_RH : ChildBounded (node (cKeys.drop t) (cChildren.drop t)) := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
        rw [hnil]; simpa using childBounded_node_nil (cKeys.drop t)
      · exact childBounded_drop_of_full hcb_child (by omega) (by rw [h2t]; omega)
    have hsd_RH : SameDepth (node (cKeys.drop t) (cChildren.drop t)) := by
      have h := sameDepth_drop cKeys cChildren t hsd_child (by omega)
      simp only [List.splitAt_eq] at h
      rw [sameDepth_iff] at h ⊢; exact h
    have hsd_LH : SameDepth (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := sameDepth_take cKeys cChildren t hsd_child (by omega)
      simpa [List.splitAt_eq] using h
    obtain ⟨ihsd, ihht⟩ := ih hcb_RH hsd_RH
    have hheq := heightOf_halves_eq hsd_child (by omega) h_children
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys.getD (t - 1) 0 :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [node (cKeys.take (t - 1)) (cChildren.take t),
               insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))]
              ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_neg hnlt]
    rw [hval]
    have hHT : ∀ c'' ∈ cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t),
         insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))] ++ cs.drop (findChild ks x + 1),
        heightOf c'' = heightOf (node cKeys cChildren) := by
      intro c'' hc''
      rcases List.mem_append.mp hc'' with h1 | h2
      · rcases List.mem_append.mp h1 with hta | hmid
        · exact (sameDepth_iff.mp hsd).2 c'' ((List.take_subset _ _) hta) _ hmem
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
          rcases hmid with rfl | rfl
          · exact hheq.1
          · rw [ihht]; exact hheq.2
      · exact (sameDepth_iff.mp hsd).2 c'' ((List.drop_subset _ _) h2) _ hmem
    have hSD : ∀ c'' ∈ cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t),
         insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))] ++ cs.drop (findChild ks x + 1),
        SameDepth c'' := by
      intro c'' hc''
      rcases List.mem_append.mp hc'' with h1 | h2
      · rcases List.mem_append.mp h1 with hta | hmid
        · exact (sameDepth_iff.mp hsd).1 c'' ((List.take_subset _ _) hta)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
          rcases hmid with rfl | rfl
          · exact hsd_LH
          · exact ihsd
      · exact (sameDepth_iff.mp hsd).1 c'' ((List.drop_subset _ _) h2)
    refine ⟨sameDepth_iff.mpr ⟨hSD, fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩, ?_⟩
    have hmem_res : node (cKeys.take (t - 1)) (cChildren.take t) ∈
        cs.take (findChild ks x) ++
          [node (cKeys.take (t - 1)) (cChildren.take t),
           insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))] ++ cs.drop (findChild ks x + 1) := by
      apply List.mem_append_left; apply List.mem_append_right; simp
    rw [heightOf_sameDepth_mem (sameDepth_iff.mpr ⟨hSD, fun a ha b hb =>
          (hHT a ha).trans (hHT b hb).symm⟩) hmem_res, hHT _ hmem_res,
        heightOf_sameDepth_mem hsd hmem]
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
    intro hcb hsd
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hsd_child : SameDepth (node cKeys cChildren) := (sameDepth_iff.mp hsd).1 _ hmem
    obtain ⟨ihsd, ihht⟩ := ih hcb_child hsd_child
    have hval : insertNonFull t x (node ks cs)
        = node ks (cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren))) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_neg hnfull]
    rw [hval]
    have hHT : ∀ c'' ∈ cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren)),
        heightOf c'' = heightOf (node cKeys cChildren) := by
      intro c'' hc''
      rcases List.mem_or_eq_of_mem_set hc'' with hcs | rfl
      · exact (sameDepth_iff.mp hsd).2 c'' hcs _ hmem
      · exact ihht
    have hSD : ∀ c'' ∈ cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren)),
        SameDepth c'' := by
      intro c'' hc''
      rcases List.mem_or_eq_of_mem_set hc'' with hcs | rfl
      · exact (sameDepth_iff.mp hsd).1 c'' hcs
      · exact ihsd
    refine ⟨sameDepth_iff.mpr ⟨hSD, fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩, ?_⟩
    have hmem_res : insertNonFull t x (node cKeys cChildren) ∈
        cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren)) :=
      List.mem_set hilt _
    rw [heightOf_sameDepth_mem (sameDepth_iff.mpr ⟨hSD, fun a ha b hb =>
          (hHT a ha).trans (hHT b hb).symm⟩) hmem_res, hHT _ hmem_res,
        heightOf_sameDepth_mem hsd hmem]

/-- `insertNonFull` preserves `SameDepth`. -/
lemma insertNonFull_sameDepth (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr) (hsd : SameDepth tr) : SameDepth (insertNonFull t x tr) :=
  (insertNonFull_sameDepth_height t x ht tr hcb hsd).1

/-- `insertNonFull` preserves the total height. -/
lemma insertNonFull_height (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hcb : ChildBounded tr) (hsd : SameDepth tr) :
    heightOf (insertNonFull t x tr) = heightOf tr :=
  (insertNonFull_sameDepth_height t x ht tr hcb hsd).2

/-! ### Bridge to `splitChild` for the Sorted / ChildBounded proofs -/

/-- Explicit output of `splitChild` on a full child: it inserts the median
`cKeys[t-1]` into the parent keys and replaces the child by its two halves.
This lets the insertion proofs reuse `splitChild_preserves_sorted` /
`splitChild_preserves_childBounded`. -/
lemma splitChild_full_eq (t : Nat) (ht : 2 ≤ t) (ks : List Nat) (cs : List BTree) (i : Nat)
    (cKeys : List Nat) (cChildren : List BTree)
    (h_lt : i < cs.length) (hchild_eq : cs.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1) :
    splitChild t (node ks cs) i
      = node (ks.take i ++ cKeys[t - 1]'(by omega) :: ks.drop i)
          (cs.take i ++
            [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
            ++ cs.drop (i + 1)) := by
  have ht1 : t - 1 < cKeys.length := by omega
  have h_keys_snd_nonempty : (cKeys.splitAt (t - 1)).2 ≠ [] := by
    have hlen : (cKeys.splitAt (t - 1)).2.length = t := by simp [hchild_full]; omega
    intro h; rw [h] at hlen; simp at hlen; omega
  dsimp [splitChild]; rw [dif_pos h_lt]
  have h_get : cs[i] = node cKeys cChildren := by simpa using hchild_eq
  rw [h_get]; dsimp; rw [if_pos hchild_full]
  cases hk : cKeys.splitAt (t - 1) with
  | mk leftKeys keysRest =>
    have hkr_ne : keysRest ≠ [] := by
      have : (cKeys.splitAt (t - 1)).2 = keysRest := by rw [hk]
      rw [← this]; exact h_keys_snd_nonempty
    cases hkr : keysRest with
    | nil => exact (hkr_ne hkr).elim
    | cons medianKey rightKeys =>
      cases hc : cChildren.splitAt t with
      | mk leftCh rightCh =>
        have h_lk : leftKeys = cKeys.take (t - 1) := by
          calc leftKeys = (cKeys.splitAt (t - 1)).1 := by rw [hk]
            _ = cKeys.take (t - 1) := by simp
        have h_keysRest_eq : keysRest = cKeys.drop (t - 1) := by
          calc keysRest = (cKeys.splitAt (t - 1)).2 := by rw [hk]
            _ = cKeys.drop (t - 1) := by simp
        have h_rk : rightKeys = cKeys.drop t := by
          calc rightKeys = keysRest.drop 1 := by rw [hkr]; simp
            _ = (cKeys.drop (t - 1)).drop 1 := by rw [h_keysRest_eq]
            _ = cKeys.drop ((t - 1) + 1) := by rw [← List.drop_drop]
            _ = cKeys.drop t := by rw [show (t - 1) + 1 = t from by omega]
        have h_lc : leftCh = cChildren.take t := by
          calc leftCh = (cChildren.splitAt t).1 := by rw [hc]
            _ = cChildren.take t := by simp
        have h_rc : rightCh = cChildren.drop t := by
          calc rightCh = (cChildren.splitAt t).2 := by rw [hc]
            _ = cChildren.drop t := by simp
        have h_med : medianKey = cKeys[t - 1] := by
          have hh : (cKeys.drop (t - 1))[0]? = some medianKey := by
            rw [← h_keysRest_eq, hkr]; rfl
          rw [List.getElem?_drop] at hh
          simp only [Nat.add_zero, List.getElem?_eq_getElem ht1] at hh
          injection hh with hh; exact hh.symm
        subst h_lk h_rk h_lc h_rc h_med
        rfl

/-- `Sorted` restricts to a prefix of the keys/children. -/
lemma sorted_take {ks : List Nat} {cs : List BTree} (a b : Nat)
    (hs : Sorted (node ks cs)) : Sorted (node (ks.take a) (cs.take b)) := by
  unfold Sorted at hs ⊢
  exact ⟨List.Pairwise.take hs.1, fun c hc => hs.2 c ((List.take_subset _ _) hc)⟩

/-- `Sorted` restricts to a suffix of the keys/children. -/
lemma sorted_drop {ks : List Nat} {cs : List BTree} (a b : Nat)
    (hs : Sorted (node ks cs)) : Sorted (node (ks.drop a) (cs.drop b)) := by
  unfold Sorted at hs ⊢
  exact ⟨List.Pairwise.drop hs.1, fun c hc => hs.2 c ((List.drop_subset _ _) hc)⟩

/-- `insertNonFull` preserves `Sorted` (given the tree is `ChildBounded` and
`Sorted`).  The split cases reuse `splitChild_preserves_sorted` via
`splitChild_full_eq`. -/
lemma insertNonFull_sorted (t x : Nat) (ht : 2 ≤ t) :
    ∀ tr, ChildBounded tr → Sorted tr → Sorted (insertNonFull t x tr) := by
  intro tr
  induction tr using insertNonFull.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
    intro _ hs
    have hcsnil : cs = [] := List.isEmpty_iff.mp hempty
    subst hcsnil
    rw [insertNonFull]; simp only [List.isEmpty_nil, if_true]
    unfold Sorted at hs ⊢
    exact ⟨sortedInsert_sorted x hs.1, fun c hc => by simp at hc⟩
  | case2 ks cs hne i hnone =>
    intro _ hs
    have hval : insertNonFull t x (node ks cs) = node ks cs := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rfl
      · rename_i c hcsome
        have hn : cs[findChild ks x]? = none := hnone; rw [hcsome] at hn; simp at hn
    rw [hval]; exact hs
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
    intro hcb hs
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hs_child : Sorted (node cKeys cChildren) := by unfold Sorted at hs; exact hs.2 _ hmem
    have ihc := ih hcb_child hs_child
    have hval : insertNonFull t x (node ks cs)
        = node ks (cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren))) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_neg hnfull]
    rw [hval]
    unfold Sorted at hs ⊢
    refine ⟨hs.1, fun c hc => ?_⟩
    rcases List.mem_or_eq_of_mem_set hc with hcs | rfl
    · exact hs.2 c hcs
    · exact ihc
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
    intro hcb hs
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hget' : cs.get ⟨findChild ks x, hilt⟩ = node cKeys cChildren := by
      rw [List.get_eq_getElem]; exact hget
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hs_child : Sorted (node cKeys cChildren) := by unfold Sorted at hs; exact hs.2 _ hmem
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_LH : ChildBounded (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := childBounded_take_of_full hcb_child ht1
      rwa [show (t - 1) + 1 = t from by omega] at h
    have ihc := ih hcb_LH (sorted_take (t - 1) t hs_child)
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys.getD (t - 1) 0 :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
               node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_pos hlt]
    have hsplit := splitChild_preserves_sorted t ht ks cs cKeys cChildren (findChild ks x)
      hilt hget' hfull hs hcb
    rw [splitChild_full_eq t ht ks cs (findChild ks x) cKeys cChildren hilt hget' hfull] at hsplit
    rw [hval, hmed]
    unfold Sorted at hsplit ⊢
    refine ⟨hsplit.1, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with h1 | h2
    · rcases List.mem_append.mp h1 with hta | hmid
      · exact hsplit.2 c (List.mem_append_left _ (List.mem_append_left _ hta))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
        rcases hmid with rfl | rfl
        · exact ihc
        · exact hsplit.2 _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
    · exact hsplit.2 c (List.mem_append_right _ h2)
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
    intro hcb hs
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hget' : cs.get ⟨findChild ks x, hilt⟩ = node cKeys cChildren := by
      rw [List.get_eq_getElem]; exact hget
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hs_child : Sorted (node cKeys cChildren) := by unfold Sorted at hs; exact hs.2 _ hmem
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_RH : ChildBounded (node (cKeys.drop t) (cChildren.drop t)) := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
        rw [hnil]; simpa using childBounded_node_nil (cKeys.drop t)
      · exact childBounded_drop_of_full hcb_child (by omega) (by rw [h2t]; omega)
    have ihc := ih hcb_RH (sorted_drop t t hs_child)
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys.getD (t - 1) 0 :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [node (cKeys.take (t - 1)) (cChildren.take t),
               insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))]
              ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_neg hnlt]
    have hsplit := splitChild_preserves_sorted t ht ks cs cKeys cChildren (findChild ks x)
      hilt hget' hfull hs hcb
    rw [splitChild_full_eq t ht ks cs (findChild ks x) cKeys cChildren hilt hget' hfull] at hsplit
    rw [hval, hmed]
    unfold Sorted at hsplit ⊢
    refine ⟨hsplit.1, fun c hc => ?_⟩
    rcases List.mem_append.mp hc with h1 | h2
    · rcases List.mem_append.mp h1 with hta | hmid
      · exact hsplit.2 c (List.mem_append_left _ (List.mem_append_left _ hta))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
        rcases hmid with rfl | rfl
        · exact hsplit.2 _ (List.mem_append_left _ (List.mem_append_right _ (by simp)))
        · exact ihc
    · exact hsplit.2 c (List.mem_append_right _ h2)

/-! ### ChildBounded preservation -/

/-- Membership after `insertNonFull` (from `insertNonFull_keys_perm`). -/
lemma mem_insertNonFull {t x : Nat} (ht : 2 ≤ t) {tr : BTree} (hcb : ChildBounded tr) {y : Nat} :
    y ∈ keysOf (insertNonFull t x tr) ↔ y = x ∨ y ∈ keysOf tr := by
  rw [(insertNonFull_keys_perm t x ht tr hcb).mem_iff, List.mem_append, List.mem_singleton]
  tauto

/-- Replacing child `j` of a `ChildBounded` node with `c'` preserves `ChildBounded`,
provided `c'` is itself `ChildBounded` and its keys satisfy the separator bounds at
position `j`. -/
lemma childBounded_set {ks : List Nat} {cs : List BTree} {j : Nat} {c' : BTree}
    (hcb : ChildBounded (node ks cs)) (hj : j < cs.length) (hc' : ChildBounded c')
    (h_lo : j = 0 ∨ (match ks[j - 1]? with | some lo => ∀ k ∈ keysOf c', lo ≤ k | none => True))
    (h_hi : match ks[j]? with | some hi => ∀ k ∈ keysOf c', k ≤ hi | none => True) :
    ChildBounded (node ks (cs.set j c')) := by
  unfold ChildBounded at hcb ⊢
  obtain ⟨h_rel, h_bounds, h_sub⟩ := hcb
  refine ⟨?_, ?_, ?_⟩
  · have hne0 : cs.length ≠ 0 := by omega
    rcases h_rel with he | he
    · rw [List.isEmpty_iff] at he; rw [he] at hne0; simp at hne0
    · right; rw [List.length_set]; exact he
  · intro m hm
    have hm_cs : m < cs.length := by rw [List.length_set] at hm; exact hm
    by_cases hmj : m = j
    · subst hmj
      have hchild : (cs.set m c').get ⟨m, hm⟩ = c' := by
        rw [List.get_eq_getElem, List.getElem_set_self]
      rw [hchild]; exact ⟨h_lo, h_hi⟩
    · have hchild : (cs.set j c').get ⟨m, hm⟩ = cs.get ⟨m, hm_cs⟩ := by
        rw [List.get_eq_getElem, List.getElem_set_ne (Ne.symm hmj), List.get_eq_getElem]
      rw [hchild]; exact h_bounds m hm_cs
  · intro c hc
    rcases List.mem_or_eq_of_mem_set hc with hcs | rfl
    · exact h_sub c hcs
    · exact hc'

/-- Replacing child `j` by `insertNonFull t x (child j)` preserves `ChildBounded`,
provided `x` lies within the separator bounds at position `j`. -/
lemma childBounded_set_insertNonFull (t x : Nat) (ht : 2 ≤ t)
    {ks : List Nat} {cs : List BTree} {j : Nat}
    (hcb : ChildBounded (node ks cs)) (hj : j < cs.length)
    (hc' : ChildBounded (insertNonFull t x (cs.get ⟨j, hj⟩)))
    (hx_lo : j = 0 ∨ ∀ lo, ks[j - 1]? = some lo → lo ≤ x)
    (hx_hi : ∀ hi, ks[j]? = some hi → x ≤ hi) :
    ChildBounded (node ks (cs.set j (insertNonFull t x (cs.get ⟨j, hj⟩)))) := by
  have hcbb := hcb
  unfold ChildBounded at hcbb
  obtain ⟨_, h_bounds, h_sub⟩ := hcbb
  have hcb_child : ChildBounded (cs.get ⟨j, hj⟩) := h_sub _ (List.get_mem _ _)
  have hbounds := h_bounds j hj
  apply childBounded_set hcb hj hc'
  · by_cases hj0 : j = 0
    · exact Or.inl hj0
    · right
      rcases hx_lo with h0 | hxlo
      · exact absurd h0 hj0
      · cases hks : ks[j - 1]? with
        | none => trivial
        | some lo =>
          intro k hk
          rw [mem_insertNonFull ht hcb_child] at hk
          rcases hk with rfl | hk
          · exact hxlo lo hks
          · rcases hbounds.1 with hj0' | hlo_match
            · exact absurd hj0' hj0
            · rw [hks] at hlo_match; exact hlo_match k hk
  · cases hks : ks[j]? with
    | none => trivial
    | some hi =>
      intro k hk
      rw [mem_insertNonFull ht hcb_child] at hk
      rcases hk with rfl | hk
      · exact hx_hi hi hks
      · have hb2 := hbounds.2; rw [hks] at hb2; exact hb2 k hk

/-- The right separator at the chosen child bounds `x` from above (sorted keys). -/
lemma findChild_x_hi {ks : List Nat} (hs : List.Pairwise (· ≤ ·) ks) (x : Nat) :
    ∀ hi, ks[findChild ks x]? = some hi → x ≤ hi := by
  intro hi hhi
  have hmem : hi ∈ ks.drop (findChild ks x) := by
    rw [List.mem_iff_getElem?]
    exact ⟨0, by rw [List.getElem?_drop, Nat.add_zero]; exact hhi⟩
  exact le_of_lt (findChild_drop_gt x hs hi hmem)

/-- The left separator at the chosen child bounds `x` from below. -/
lemma findChild_x_lo (ks : List Nat) (x : Nat) :
    findChild ks x = 0 ∨ ∀ lo, ks[findChild ks x - 1]? = some lo → lo ≤ x := by
  rcases Nat.eq_zero_or_pos (findChild ks x) with h0 | hpos
  · exact Or.inl h0
  · right
    intro lo hlo
    have hmem : lo ∈ ks.take (findChild ks x) := by
      rw [List.mem_iff_getElem?]
      exact ⟨findChild ks x - 1, by rw [List.getElem?_take_of_lt (by omega)]; exact hlo⟩
    exact findChild_take_le x ks lo hmem

/-- `insertNonFull` preserves `ChildBounded` (given `ChildBounded` + `Sorted`). -/
lemma insertNonFull_childBounded (t x : Nat) (ht : 2 ≤ t) :
    ∀ tr, ChildBounded tr → Sorted tr → ChildBounded (insertNonFull t x tr) := by
  intro tr
  induction tr using insertNonFull.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
    intro _ _
    have hcsnil : cs = [] := List.isEmpty_iff.mp hempty
    subst hcsnil
    rw [insertNonFull]; simp only [List.isEmpty_nil, if_true]
    exact childBounded_node_nil (sortedInsert x ks)
  | case2 ks cs hne i hnone =>
    intro hcb _
    have hval : insertNonFull t x (node ks cs) = node ks cs := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rfl
      · rename_i c hcsome
        have hn : cs[findChild ks x]? = none := hnone; rw [hcsome] at hn; simp at hn
    rw [hval]; exact hcb
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
    intro hcb hs
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hget' : cs.get ⟨findChild ks x, hilt⟩ = node cKeys cChildren := by
      rw [List.get_eq_getElem]; exact hget
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hs_child : Sorted (node cKeys cChildren) := by unfold Sorted at hs; exact hs.2 _ hmem
    have hpw : List.Pairwise (· ≤ ·) ks := by unfold Sorted at hs; exact hs.1
    have ihc := ih hcb_child hs_child
    have hval : insertNonFull t x (node ks cs)
        = node ks (cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren))) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_neg hnfull]
    rw [hval, ← hget']
    exact childBounded_set_insertNonFull t x ht hcb hilt (by rw [hget']; exact ihc)
      (findChild_x_lo ks x) (findChild_x_hi hpw x)
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
    intro hcb hs
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hget' : cs.get ⟨findChild ks x, hilt⟩ = node cKeys cChildren := by
      rw [List.get_eq_getElem]; exact hget
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hs_child : Sorted (node cKeys cChildren) := by unfold Sorted at hs; exact hs.2 _ hmem
    have hpw : List.Pairwise (· ≤ ·) ks := by unfold Sorted at hs; exact hs.1
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_LH : ChildBounded (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := childBounded_take_of_full hcb_child ht1
      rwa [show (t - 1) + 1 = t from by omega] at h
    have ihc := ih hcb_LH (sorted_take (t - 1) t hs_child)
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hie : findChild ks x ≤ ks.length := findChild_le ks x
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
               node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_pos hlt, hmed]
    have hsplit := splitChild_preserves_childBounded t ht ks cs cKeys cChildren
      (findChild ks x) hilt hget' hfull hcb hs
    rw [splitChild_full_eq t ht ks cs (findChild ks x) cKeys cChildren hilt hget' hfull] at hsplit
    have hj : findChild ks x < (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
        ++ cs.drop (findChild ks x + 1)).length := by
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil,
        List.length_drop]; omega
    have hAlen : (cs.take (findChild ks x)).length = findChild ks x := by
      rw [List.length_take]; omega
    have hlt_AB : findChild ks x < (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]).length := by
      rw [List.length_append, hAlen]; simp
    have hget_LH : (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
        ++ cs.drop (findChild ks x + 1)).get ⟨findChild ks x, hj⟩
        = node (cKeys.take (t - 1)) (cChildren.take t) := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left hlt_AB, List.getElem_append_right (le_of_eq hAlen)]
      simp [hAlen]
    have hx_hi : ∀ hi, (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))[findChild ks x]? = some hi → x ≤ hi := by
      intro hi hhi
      rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
          Nat.min_eq_left hie, Nat.sub_self] at hhi
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hhi
      subst hhi; rw [← hmed]; exact le_of_lt hlt
    have hx_lo : findChild ks x = 0 ∨ ∀ lo,
        (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))[findChild ks x - 1]? = some lo → lo ≤ x := by
      rcases Nat.eq_zero_or_pos (findChild ks x) with h0 | hpos
      · exact Or.inl h0
      · right; intro lo hlo
        rw [List.getElem?_append_left (by rw [List.length_take, Nat.min_eq_left hie]; omega),
            List.getElem?_take_of_lt (by omega)] at hlo
        have hmem2 : lo ∈ ks.take (findChild ks x) := by
          rw [List.mem_iff_getElem?]
          exact ⟨findChild ks x - 1, by rw [List.getElem?_take_of_lt (by omega)]; exact hlo⟩
        exact findChild_take_le x ks lo hmem2
    have hres := childBounded_set_insertNonFull t x ht hsplit hj
      (by rw [hget_LH]; exact ihc) hx_lo hx_hi
    rw [hget_LH] at hres
    rw [hval]
    rw [show cs.take (findChild ks x) ++
          [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
           node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)
        = (cs.take (findChild ks x) ++
          [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
          ++ cs.drop (findChild ks x + 1)).set (findChild ks x)
            (insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t))) from by
        rw [List.set_append_left _ _ (by rw [List.length_append, hAlen]; simp),
            List.set_append_right _ _ (by rw [hAlen]), hAlen, Nat.sub_self]; rfl]
    exact hres
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
    intro hcb hs
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hget' : cs.get ⟨findChild ks x, hilt⟩ = node cKeys cChildren := by
      rw [List.get_eq_getElem]; exact hget
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hs_child : Sorted (node cKeys cChildren) := by unfold Sorted at hs; exact hs.2 _ hmem
    have hpw : List.Pairwise (· ≤ ·) ks := by unfold Sorted at hs; exact hs.1
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_RH : ChildBounded (node (cKeys.drop t) (cChildren.drop t)) := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
        rw [hnil]; simpa using childBounded_node_nil (cKeys.drop t)
      · exact childBounded_drop_of_full hcb_child (by omega) (by rw [h2t]; omega)
    have ihc := ih hcb_RH (sorted_drop t t hs_child)
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hie : findChild ks x ≤ ks.length := findChild_le ks x
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [node (cKeys.take (t - 1)) (cChildren.take t),
               insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))]
              ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_neg hnlt, hmed]
    have hsplit := splitChild_preserves_childBounded t ht ks cs cKeys cChildren
      (findChild ks x) hilt hget' hfull hcb hs
    rw [splitChild_full_eq t ht ks cs (findChild ks x) cKeys cChildren hilt hget' hfull] at hsplit
    have hj : findChild ks x + 1 < (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
        ++ cs.drop (findChild ks x + 1)).length := by
      simp only [List.length_append, List.length_take, List.length_cons, List.length_nil,
        List.length_drop]; omega
    have hAlen : (cs.take (findChild ks x)).length = findChild ks x := by
      rw [List.length_take]; omega
    have hlt_AB : findChild ks x + 1 < (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]).length := by
      rw [List.length_append, hAlen]; simp
    have hget_RH : (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
        ++ cs.drop (findChild ks x + 1)).get ⟨findChild ks x + 1, hj⟩
        = node (cKeys.drop t) (cChildren.drop t) := by
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left hlt_AB,
          List.getElem_append_right (by rw [hAlen]; omega)]
      simp [hAlen, show findChild ks x + 1 - findChild ks x = 1 from by omega]
    have hx_hi : ∀ hi, (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))[findChild ks x + 1]? = some hi → x ≤ hi := by
      intro hi hhi
      rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
          Nat.min_eq_left hie] at hhi
      rw [show findChild ks x + 1 - findChild ks x = 0 + 1 from by omega,
          List.getElem?_cons_succ, List.getElem?_drop] at hhi
      have hkeq : findChild ks x + (0) = findChild ks x := by omega
      rw [hkeq] at hhi
      exact findChild_x_hi hpw x hi hhi
    have hx_lo : findChild ks x + 1 = 0 ∨ ∀ lo,
        (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))[findChild ks x + 1 - 1]? = some lo → lo ≤ x := by
      right; intro lo hlo
      rw [show findChild ks x + 1 - 1 = findChild ks x from by omega,
          List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
          Nat.min_eq_left hie, Nat.sub_self] at hlo
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hlo
      subst hlo; rw [← hmed]; exact not_lt.mp hnlt
    have hres := childBounded_set_insertNonFull t x ht hsplit hj
      (by rw [hget_RH]; exact ihc) hx_lo hx_hi
    rw [hget_RH] at hres
    rw [hval]
    rw [show cs.take (findChild ks x) ++
          [node (cKeys.take (t - 1)) (cChildren.take t),
           insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))] ++ cs.drop (findChild ks x + 1)
        = (cs.take (findChild ks x) ++
          [node (cKeys.take (t - 1)) (cChildren.take t), node (cKeys.drop t) (cChildren.drop t)]
          ++ cs.drop (findChild ks x + 1)).set (findChild ks x + 1)
            (insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))) from by
        rw [List.set_append_left _ _ (by rw [List.length_append, hAlen]; simp),
            List.set_append_right _ _ (by rw [hAlen]; omega), hAlen,
            show findChild ks x + 1 - findChild ks x = 1 from by omega]; rfl]
    exact hres

/-! ### Occupancy preservation -/

/-- The left split half is `Occupancy`-valid as a non-root node. -/
lemma occupancy_left_half (t : Nat) (ht : 2 ≤ t) {cKeys : List Nat} {cChildren : List BTree}
    (hocc : Occupancy t false (node cKeys cChildren)) (hcb : ChildBounded (node cKeys cChildren))
    (hfull : cKeys.length = 2 * t - 1) :
    Occupancy t false (node (cKeys.take (t - 1)) (cChildren.take t)) := by
  have hlen := child_children_len_of_full_cb ht hcb hfull
  have hkl : (cKeys.take (t - 1)).length = t - 1 := by rw [List.length_take, hfull]; omega
  unfold Occupancy at hocc ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t - 1 ≤ (cKeys.take (t - 1)).length; omega
  · show (cKeys.take (t - 1)).length ≤ 2 * t - 1; omega
  · rcases hlen with h0 | h2t
    · left
      have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
      rw [hnil]; simp
    · right; rw [List.length_take, h2t]; constructor <;> omega
  · intro child hchild
    exact hocc.2.2.2 child ((List.take_subset t cChildren) hchild)

/-- The right split half is `Occupancy`-valid as a non-root node. -/
lemma occupancy_right_half (t : Nat) (ht : 2 ≤ t) {cKeys : List Nat} {cChildren : List BTree}
    (hocc : Occupancy t false (node cKeys cChildren)) (hcb : ChildBounded (node cKeys cChildren))
    (hfull : cKeys.length = 2 * t - 1) :
    Occupancy t false (node (cKeys.drop t) (cChildren.drop t)) := by
  have hlen := child_children_len_of_full_cb ht hcb hfull
  have hkl : (cKeys.drop t).length = t - 1 := by rw [List.length_drop, hfull]; omega
  unfold Occupancy at hocc ⊢
  refine ⟨?_, ?_, ?_, ?_⟩
  · show t - 1 ≤ (cKeys.drop t).length; omega
  · show (cKeys.drop t).length ≤ 2 * t - 1; omega
  · rcases hlen with h0 | h2t
    · left
      have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
      rw [hnil]; simp
    · right; rw [List.length_drop, h2t]; constructor <;> omega
  · intro child hchild
    exact hocc.2.2.2 child ((List.drop_subset t cChildren) hchild)

/-- The number of keys at the root node (used for the non-full precondition). -/
def rootKeyCount : BTree → Nat
  | node ks _ => ks.length

/-- Replacing child `j` with an `Occupancy`-valid (non-root) subtree preserves `Occupancy`. -/
lemma occupancy_set {t : Nat} {b : Bool} {ks : List Nat} {cs : List BTree} {j : Nat} {c' : BTree}
    (hocc : Occupancy t b (node ks cs)) (hj : j < cs.length) (hc' : Occupancy t false c') :
    Occupancy t b (node ks (cs.set j c')) := by
  have hemp : (cs.set j c').isEmpty = cs.isEmpty := by
    cases cs with
    | nil => simp at hj
    | cons a as => cases j <;> simp
  have hlen : (cs.set j c').length = cs.length := List.length_set
  unfold Occupancy at hocc ⊢
  rw [hemp, hlen]
  refine ⟨hocc.1, hocc.2.1, hocc.2.2.1, ?_⟩
  intro c hc
  rcases List.mem_or_eq_of_mem_set hc with hcs | rfl
  · exact hocc.2.2.2 c hcs
  · exact hc'

/-- `insertNonFull` preserves `Occupancy` (given the node is `ChildBounded` and
non-full).  Works for both the root and non-root occupancy flags. -/
lemma insertNonFull_occupancy (t x : Nat) (ht : 2 ≤ t) :
    ∀ tr (b : Bool), ChildBounded tr → Occupancy t b tr → rootKeyCount tr < 2 * t - 1 →
      Occupancy t b (insertNonFull t x tr) := by
  intro tr
  induction tr using insertNonFull.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
    intro b hcb hocc hnf
    have hcsnil : cs = [] := List.isEmpty_iff.mp hempty
    subst hcsnil
    have hnf' : ks.length < 2 * t - 1 := hnf
    rw [insertNonFull]; simp only [List.isEmpty_nil, if_true]
    have hlen : (sortedInsert x ks).length = ks.length + 1 := by
      rw [(sortedInsert_perm x ks).length_eq]; simp
    unfold Occupancy at hocc ⊢
    refine ⟨?_, ?_, Or.inl (by simp), by intro c hc; simp at hc⟩
    · cases b
      · simp only [Bool.false_eq_true, if_false] at hocc ⊢; omega
      · simp only [if_true]; rw [hlen]; split <;> omega
    · rw [hlen]; omega
  | case2 ks cs hne i hnone =>
    intro b hcb hocc _
    have hval : insertNonFull t x (node ks cs) = node ks cs := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rfl
      · rename_i c hcsome
        have hn : cs[findChild ks x]? = none := hnone; rw [hcsome] at hn; simp at hn
    rw [hval]; exact hocc
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
    intro b hcb hocc hnf
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_child : ChildBounded (node cKeys cChildren) := by
      unfold ChildBounded at hcb; rcases hcb with ⟨_, _, hsub⟩; exact hsub _ hmem
    have hocc_child : Occupancy t false (node cKeys cChildren) := by
      unfold Occupancy at hocc; exact hocc.2.2.2 _ hmem
    have hnf_child : rootKeyCount (node cKeys cChildren) < 2 * t - 1 := by
      show cKeys.length < 2 * t - 1
      have : cKeys.length ≤ 2 * t - 1 := by unfold Occupancy at hocc_child; exact hocc_child.2.1
      omega
    have ihc := ih false hcb_child hocc_child hnf_child
    have hval : insertNonFull t x (node ks cs)
        = node ks (cs.set (findChild ks x) (insertNonFull t x (node cKeys cChildren))) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_neg hnfull]
    rw [hval]
    exact occupancy_set hocc hilt ihc
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
    intro b hcb hocc hnf
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_u := hcb; unfold ChildBounded at hcb_u
    have hocc_u := hocc; unfold Occupancy at hocc_u
    obtain ⟨hocc_lo, hocc_up, hocc_ch, hocc_rec⟩ := hocc_u
    have hcb_child : ChildBounded (node cKeys cChildren) := hcb_u.2.2 _ hmem
    have hocc_child : Occupancy t false (node cKeys cChildren) := hocc_rec _ hmem
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_LH : ChildBounded (node (cKeys.take (t - 1)) (cChildren.take t)) := by
      have h := childBounded_take_of_full hcb_child ht1
      rwa [show (t - 1) + 1 = t from by omega] at h
    have hocc_RH := occupancy_right_half t ht hocc_child hcb_child hfull
    have hnf_LH : rootKeyCount (node (cKeys.take (t - 1)) (cChildren.take t)) < 2 * t - 1 := by
      show (cKeys.take (t - 1)).length < 2 * t - 1; rw [List.length_take]; omega
    have ihc := ih false hcb_LH (occupancy_left_half t ht hocc_child hcb_child hfull) hnf_LH
    have hnf' : ks.length < 2 * t - 1 := hnf
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hcs_eq : cs.length = ks.length + 1 := by
      rcases hcb_u.1 with he | heq
      · rw [List.isEmpty_iff] at he; rw [he] at hilt; simp at hilt
      · exact heq
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
               node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_pos hlt, hmed]
    rw [hval]
    have hNKlen : (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x)).length
        = ks.length + 1 := by
      rw [List.length_append, List.length_cons, List.length_take, List.length_drop]
      have := findChild_le ks x; omega
    have hMYlen : (cs.take (findChild ks x) ++
        [insertNonFull t x (node (cKeys.take (t - 1)) (cChildren.take t)),
         node (cKeys.drop t) (cChildren.drop t)] ++ cs.drop (findChild ks x + 1)).length
        = cs.length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_take,
        List.length_drop]; omega
    unfold Occupancy
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases b
      · simp only [Bool.false_eq_true, if_false] at hocc_lo ⊢
        rw [hNKlen]; omega
      · simp only [if_true]; rw [hNKlen]; split <;> omega
    · rw [hNKlen]; omega
    · right; rw [hMYlen]
      rcases hocc_ch with he | hb
      · rw [List.isEmpty_iff] at he; rw [he] at hilt; simp at hilt
      · omega
    · intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · rcases List.mem_append.mp h1 with hta | hmid
        · exact hocc_rec c ((List.take_subset _ _) hta)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
          rcases hmid with rfl | rfl
          · exact ihc
          · exact hocc_RH
      · exact hocc_rec c ((List.drop_subset _ _) h2)
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
    intro b hcb hocc hnf
    have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
    obtain ⟨hilt, hget⟩ := List.getElem?_eq_some_iff.mp hsome'
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨_, hsome'⟩
    have hcb_u := hcb; unfold ChildBounded at hcb_u
    have hocc_u := hocc; unfold Occupancy at hocc_u
    obtain ⟨hocc_lo, hocc_up, hocc_ch, hocc_rec⟩ := hocc_u
    have hcb_child : ChildBounded (node cKeys cChildren) := hcb_u.2.2 _ hmem
    have hocc_child : Occupancy t false (node cKeys cChildren) := hocc_rec _ hmem
    have ht1 : t - 1 < cKeys.length := by rw [hfull]; omega
    have hcb_RH : ChildBounded (node (cKeys.drop t) (cChildren.drop t)) := by
      rcases child_children_len_of_full_cb ht hcb_child hfull with h0 | h2t
      · have hnil : cChildren = [] := by cases cChildren with | nil => rfl | cons a b => simp at h0
        rw [hnil]; simpa using childBounded_node_nil (cKeys.drop t)
      · exact childBounded_drop_of_full hcb_child (by omega) (by rw [h2t]; omega)
    have hocc_LH := occupancy_left_half t ht hocc_child hcb_child hfull
    have hnf_RH : rootKeyCount (node (cKeys.drop t) (cChildren.drop t)) < 2 * t - 1 := by
      show (cKeys.drop t).length < 2 * t - 1; rw [List.length_drop]; omega
    have ihc := ih false hcb_RH (occupancy_right_half t ht hocc_child hcb_child hfull) hnf_RH
    have hnf' : ks.length < 2 * t - 1 := hnf
    have hmed : cKeys.getD (t - 1) 0 = cKeys[t - 1] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht1, Option.getD_some]
    have hcs_eq : cs.length = ks.length + 1 := by
      rcases hcb_u.1 with he | heq
      · rw [List.isEmpty_iff] at he; rw [he] at hilt; simp at hilt
      · exact heq
    have hval : insertNonFull t x (node ks cs)
        = node (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x))
            (cs.take (findChild ks x) ++
              [node (cKeys.take (t - 1)) (cChildren.take t),
               insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))]
              ++ cs.drop (findChild ks x + 1)) := by
      rw [insertNonFull, if_neg hne]; dsimp only
      split
      · rename_i hcnone; rw [hsome'] at hcnone; exact absurd hcnone (by simp)
      · rename_i c hcsome
        obtain rfl : c = node cKeys cChildren := by
          rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
        dsimp only; rw [if_pos hfull, if_neg hnlt, hmed]
    rw [hval]
    have hNKlen : (ks.take (findChild ks x) ++ cKeys[t - 1] :: ks.drop (findChild ks x)).length
        = ks.length + 1 := by
      rw [List.length_append, List.length_cons, List.length_take, List.length_drop]
      have := findChild_le ks x; omega
    have hMYlen : (cs.take (findChild ks x) ++
        [node (cKeys.take (t - 1)) (cChildren.take t),
         insertNonFull t x (node (cKeys.drop t) (cChildren.drop t))] ++ cs.drop (findChild ks x + 1)).length
        = cs.length + 1 := by
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_take,
        List.length_drop]; omega
    unfold Occupancy
    refine ⟨?_, ?_, ?_, ?_⟩
    · cases b
      · simp only [Bool.false_eq_true, if_false] at hocc_lo ⊢
        rw [hNKlen]; omega
      · simp only [if_true]; rw [hNKlen]; split <;> omega
    · rw [hNKlen]; omega
    · right; rw [hMYlen]
      rcases hocc_ch with he | hb
      · rw [List.isEmpty_iff] at he; rw [he] at hilt; simp at hilt
      · omega
    · intro c hc
      rcases List.mem_append.mp hc with h1 | h2
      · rcases List.mem_append.mp h1 with hta | hmid
        · exact hocc_rec c ((List.take_subset _ _) hta)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmid
          rcases hmid with rfl | rfl
          · exact hocc_LH
          · exact ihc
      · exact hocc_rec c ((List.drop_subset _ _) h2)

end BTree
end Chapter18
end CLRS
