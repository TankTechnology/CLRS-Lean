import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion

/-!
# CLRS Section 18.3 - B-tree deletion specification

This section adds a first-pass deletion specification over the mathematical
B-tree key-membership model.  It deliberately stays at the set-membership layer:
the operation filters the represented key list and later refinements can replace
it with the full CLRS node-level borrow/merge algorithm.

Main results:

- Theorem {lit}`BTree.delete_preserves_model`: specification deletion preserves
  the first-pass validity predicate.
- Theorem {lit}`BTree.delete_valid`: direct validity-preservation wrapper for
  specification deletion.
- Theorem {lit}`BTree.delete_mem_iff`: after deletion, membership is exactly
  membership of a key different from the deleted key.
- Theorem {lit}`BTree.delete_mem_iff_ne`: the same membership specification
  using Prop-level key inequality.
- Theorem {lit}`BTree.delete_search_iff`: searching after deletion succeeds
  exactly for old searchable keys different from the deleted key.
- Theorem {lit}`BTree.delete_search_iff_ne`: the same successful-search
  specification using Prop-level key inequality.
- Theorem {lit}`BTree.delete_search_false_iff`: searching after deletion fails
  exactly for the deleted key or keys that failed before.
- Theorem {lit}`BTree.delete_search_false_old`: old unsuccessful searches
  remain unsuccessful after deletion.
- Theorem {lit}`BTree.delete_not_mem_iff`: membership after deletion fails
  exactly for the deleted key or keys that were absent before.
- Theorems {lit}`BTree.delete_not_mem_old` and
  {lit}`BTree.delete_not_mem_of_eq`: old absent keys and keys equal to the
  deleted key remain absent after deletion.
- Theorems {lit}`BTree.delete_not_mem` and
  {lit}`BTree.delete_search_deleted_false`: the deleted key is absent and not
  searchable after deletion.
- Theorem {lit}`BTree.delete_search_false_of_eq`: any query key equal to the
  deleted key is not searchable after deletion.
- Theorems {lit}`BTree.delete_mem_of_ne`,
  {lit}`BTree.delete_mem_of_ne_prop`, {lit}`BTree.delete_search_of_ne`, and
  {lit}`BTree.delete_search_of_ne_prop`: old keys different from the deleted
  key remain present and searchable after deletion.
- Theorems {lit}`BTree.delete_search_of_mem_ne`,
  {lit}`BTree.delete_search_of_mem_ne_prop`, and
  {lit}`BTree.delete_search_false_of_not_mem`: old membership and absence give
  direct post-deletion successful and failed searches.

Current gaps (3 sub-problems, ≈13 sorries):

- `mergeNodes_childBounded` — the key-bound transfer for merged children
  (blocking the key-at-separator merge case in all 4 component lemmas).
- `keysOf_composedDelete_subset` — key-list subset property for ChildBounded
  key-bound transfer in direct-recursion branches.
- `Occupancy t false` preservation for non-root leaves in composedDelete
  (requires the underflow guard, not yet in the current composedDelete).
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

/-- Specification deletion preserves validity under the direct operation name. -/
theorem delete_valid {minDegree x : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    Valid minDegree (delete x t) := by
  exact delete_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid

/-- Specification deletion removes exactly the requested key from membership. -/
theorem delete_mem_iff (x y : Nat) (t : BTree) :
    mem y (delete x t) <-> y != x ∧ mem y t := by
  simp [delete, mem, keysOf]
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

/-- Deletion membership succeeds exactly for old keys distinct from the deleted key. -/
theorem delete_mem_iff_ne (x y : Nat) (t : BTree) :
    mem y (delete x t) <-> y ≠ x ∧ mem y t := by
  rw [delete_mem_iff]
  constructor
  · intro h
    exact ⟨by simpa using h.1, h.2⟩
  · intro h
    exact ⟨by simp [h.1], h.2⟩

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

/-- Old keys with Prop-level inequality remain present after deletion. -/
theorem delete_mem_of_ne_prop (x y : Nat) (t : BTree)
    (hxy : y ≠ x) (hy : mem y t) :
    mem y (delete x t) := by
  rw [delete_mem_iff_ne]
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

/-- Old absent keys remain absent after specification deletion. -/
theorem delete_not_mem_old (x y : Nat) (t : BTree)
    (hy : ¬ mem y t) :
    ¬ mem y (delete x t) := by
  rw [delete_not_mem_iff]
  exact Or.inr hy

/-- Any key equal to the deleted key is absent after specification deletion. -/
theorem delete_not_mem_of_eq (x y : Nat) (t : BTree)
    (hyx : y = x) :
    ¬ mem y (delete x t) := by
  rw [delete_not_mem_iff]
  exact Or.inl hyx

/-- Searching after deletion succeeds exactly for remaining old keys. -/
theorem delete_search_iff {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (delete x t) = true <-> (y != x) = true ∧ search y t = true := by
  have hdelete : Valid minDegree (delete x t) :=
    delete_preserves_model (minDegree := minDegree) (x := x) (t := t) hvalid
  rw [search_correct (minDegree := minDegree) (x := y) (t := delete x t) hdelete]
  rw [delete_mem_iff]
  rw [← search_correct (minDegree := minDegree) (x := y) (t := t) hvalid]

/-- Searching after deletion succeeds exactly for old searchable keys distinct from the deleted key. -/
theorem delete_search_iff_ne {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) :
    search y (delete x t) = true <-> y ≠ x ∧ search y t = true := by
  rw [delete_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  constructor
  · intro h
    exact ⟨by simpa using h.1, h.2⟩
  · intro h
    exact ⟨by simp [h.1], h.2⟩

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

/-- Any key equal to the deleted key is not searchable after specification deletion. -/
theorem delete_search_false_of_eq {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hyx : y = x) :
    search y (delete x t) = false := by
  rw [hyx]
  exact delete_search_deleted_false (minDegree := minDegree) (x := x) (t := t) hvalid

/-- Old searchable keys different from the deleted key remain searchable after deletion. -/
theorem delete_search_of_ne {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : (y != x) = true)
    (hy : search y t = true) :
    search y (delete x t) = true := by
  rw [delete_search_iff (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact ⟨hxy, hy⟩

/-- Old searchable keys with Prop-level inequality remain searchable after deletion. -/
theorem delete_search_of_ne_prop {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : y ≠ x)
    (hy : search y t = true) :
    search y (delete x t) = true := by
  rw [delete_search_iff_ne (minDegree := minDegree) (x := x) (y := y) (t := t) hvalid]
  exact ⟨hxy, hy⟩

/-- Old members different from the deleted key are directly searchable after deletion. -/
theorem delete_search_of_mem_ne {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : (y != x) = true) (hy : mem y t) :
    search y (delete x t) = true := by
  exact delete_search_of_ne
    (minDegree := minDegree) (x := x) (y := y) (t := t)
    hvalid hxy (search_true_of_mem y t hy)

/-- Old members with Prop-level inequality are directly searchable after deletion. -/
theorem delete_search_of_mem_ne_prop {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hxy : y ≠ x) (hy : mem y t) :
    search y (delete x t) = true := by
  exact delete_search_of_ne_prop
    (minDegree := minDegree) (x := x) (y := y) (t := t)
    hvalid hxy (search_true_of_mem y t hy)

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

/-- Old absent keys are directly failed searches after specification deletion. -/
theorem delete_search_false_of_not_mem {minDegree x y : Nat} {t : BTree}
    (hvalid : Valid minDegree t) (hy : ¬ mem y t) :
    search y (delete x t) = false := by
  exact delete_search_false_old
    (minDegree := minDegree) (x := x) (y := y) (t := t)
    hvalid (search_false_of_not_mem y t hy)

/-! ## Node-level deletion repair: `SameDepth` / `heightOf` infrastructure

The remaining theorems in this section implement the *node-level* deletion
repair operations that the specification-level {name}`delete` elides
(CLRS `B-TREE-DELETE`, cases 3a and 3b), and prove that each repair step
preserves the structural occupancy and same-depth invariants of Section 18.1.

We first collect two `SameDepth` utilities used by every repair proof.
-/

/--
`SameDepth` does not depend on the key list of the root node: only the shape of
the children matters.  This lets a repaired node inherit `SameDepth` from a node
whose keys were rearranged.
-/
lemma sameDepth_keys_irrel {ks ks' : List Nat} {cs : List BTree}
    (h : SameDepth (node ks cs)) : SameDepth (node ks' cs) := by
  cases h with
  | leaf _ => exact SameDepth.leaf ks'
  | internal _ c0 cs' hh hsd0 hsds => exact SameDepth.internal ks' c0 cs' hh hsd0 hsds

/--
A node is `SameDepth` whenever all of its children have a common height `H` and
are individually `SameDepth`.  This is the introduction rule used to assemble the
repaired children lists.
-/
lemma sameDepth_of_uniform {ks : List Nat} {cs : List BTree} {H : Nat}
    (hht : ∀ c ∈ cs, heightOf c = H) (hsd : ∀ c ∈ cs, SameDepth c) :
    SameDepth (node ks cs) := by
  cases cs with
  | nil => exact SameDepth.leaf ks
  | cons c0 cs' =>
    refine SameDepth.internal ks c0 cs' ?_ (hsd c0 (by simp)) (fun c hc => hsd c (by simp [hc]))
    intro c hc
    rw [hht c (by simp [hc]), hht c0 (by simp)]

/-- A node has height `0` exactly when it is a leaf (no children). -/
lemma heightOf_eq_zero_iff (ks : List Nat) (cs : List BTree) :
    heightOf (node ks cs) = 0 ↔ cs = [] := by
  cases cs with
  | nil => simp [heightOf]
  | cons c cs => simp [heightOf]

/-! ## `mergeNodes`: combine two sibling subtrees around a separator key -/

/--
**Node merge (CLRS `B-TREE-DELETE` case 3b core step).**  Combine a left subtree,
a separator key `sep`, and a right subtree into one node.  When both siblings are
minimal (`t - 1` keys each), the merged node has exactly `2t - 1` keys — a full
node — which is the shape produced by the deletion merge repair.
-/
def mergeNodes : BTree → Nat → BTree → BTree
  | node lKeys lCh, sep, node rKeys rCh => node (lKeys ++ sep :: rKeys) (lCh ++ rCh)

/-- `mergeNodes` reduces to the explicit combined node. -/
@[simp] lemma mergeNodes_node (lKeys rKeys : List Nat) (lCh rCh : List BTree) (sep : Nat) :
    mergeNodes (node lKeys lCh) sep (node rKeys rCh) = node (lKeys ++ sep :: rKeys) (lCh ++ rCh) :=
  rfl

/--
**Merge preserves `SameDepth`.**  Merging two equal-height same-depth siblings
yields a same-depth node.  The equal-height hypothesis is exactly the invariant
supplied by `SameDepth` of the common parent.
-/
lemma mergeNodes_sameDepth {left right : BTree} {sep : Nat}
    (hL : SameDepth left) (hR : SameDepth right) (hht : heightOf left = heightOf right) :
    SameDepth (mergeNodes left sep right) := by
  cases left with
  | node lKeys lCh =>
    cases right with
    | node rKeys rCh =>
      rw [mergeNodes_node]
      by_cases hlc : lCh = []
      · -- left is a leaf: merged children = rCh, inherit from right
        subst hlc
        rw [List.nil_append]
        exact sameDepth_keys_irrel hR
      · by_cases hrc : rCh = []
        · -- right is a leaf: merged children = lCh, inherit from left
          subst hrc
          rw [List.append_nil]
          exact sameDepth_keys_irrel hL
        · -- both internal: common child height, all same-depth
          obtain ⟨a, as, rfl⟩ : ∃ a as, lCh = a :: as := by
            cases lCh with
            | nil => exact absurd rfl hlc
            | cons a as => exact ⟨a, as, rfl⟩
          obtain ⟨b, bs, rfl⟩ : ∃ b bs, rCh = b :: bs := by
            cases rCh with
            | nil => exact absurd rfl hrc
            | cons b bs => exact ⟨b, bs, rfl⟩
          have hLh : heightOf (node lKeys (a :: as)) = 1 + heightOf a :=
            heightOf_internal_of_sameDepth hL
          have hRh : heightOf (node rKeys (b :: bs)) = 1 + heightOf b :=
            heightOf_internal_of_sameDepth hR
          have hab : heightOf a = heightOf b := by rw [hLh, hRh] at hht; omega
          have hL_all := sameDepth_children_eq_height hL
          have hR_all := sameDepth_children_eq_height hR
          refine sameDepth_of_uniform (H := heightOf a) ?_ ?_
          · intro c hc
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact hL_all c hc a (by simp)
            · rw [hR_all c hc b (by simp), ← hab]
          · intro c hc
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · rcases List.mem_cons.mp hc with rfl | hc'
              · exact sameDepth_head_sd hL
              · exact sameDepth_tail_sd hL c hc'
            · rcases List.mem_cons.mp hc with rfl | hc'
              · exact sameDepth_head_sd hR
              · exact sameDepth_tail_sd hR c hc'

/--
**Merge preserves height.**  A merged node has the same height as either
equal-height sibling.  This is what lets the merge repair keep every leaf at a
common depth from the perspective of the parent.
-/
lemma mergeNodes_height {left right : BTree} {sep : Nat}
    (hL : SameDepth left) (hR : SameDepth right) (hht : heightOf left = heightOf right) :
    heightOf (mergeNodes left sep right) = heightOf left := by
  cases left with
  | node lKeys lCh =>
    cases right with
    | node rKeys rCh =>
      rw [mergeNodes_node]
      by_cases hlc : lCh = []
      · -- left leaf ⇒ height 0 ⇒ right leaf ⇒ merged leaf
        subst hlc
        have hL0 : heightOf (node lKeys ([] : List BTree)) = 0 := by simp [heightOf]
        have hR0 : heightOf (node rKeys rCh) = 0 := by rw [← hht, hL0]
        have hrc : rCh = [] := (heightOf_eq_zero_iff rKeys rCh).mp hR0
        subst hrc
        simp [heightOf]
      · obtain ⟨a, as, rfl⟩ : ∃ a as, lCh = a :: as := by
          cases lCh with
          | nil => exact absurd rfl hlc
          | cons a as => exact ⟨a, as, rfl⟩
        have hLh : heightOf (node lKeys (a :: as)) = 1 + heightOf a :=
          heightOf_internal_of_sameDepth hL
        have hL_all := sameDepth_children_eq_height hL
        by_cases hrc : rCh = []
        · subst hrc
          have hR0 : heightOf (node rKeys ([] : List BTree)) = 0 := by simp [heightOf]
          rw [hR0, hLh] at hht; omega
        · obtain ⟨b, bs, rfl⟩ : ∃ b bs, rCh = b :: bs := by
            cases rCh with
            | nil => exact absurd rfl hrc
            | cons b bs => exact ⟨b, bs, rfl⟩
          have hRh : heightOf (node rKeys (b :: bs)) = 1 + heightOf b :=
            heightOf_internal_of_sameDepth hR
          have hab : heightOf a = heightOf b := by rw [hLh, hRh] at hht; omega
          have hR_all := sameDepth_children_eq_height hR
          -- merged children = a :: (as ++ b :: bs), all height = heightOf a
          have huniform : ∀ c ∈ (as ++ b :: bs), heightOf c = heightOf a := by
            intro c hc
            rw [List.mem_append] at hc
            rcases hc with hc | hc
            · exact hL_all c (by simp [hc]) a (by simp)
            · rw [hR_all c hc b (by simp), ← hab]
          rw [List.cons_append, heightOf_uniform_children huniform, hLh]

/-! ## `mergeNodes`: occupancy preservation -/

/-- From `ChildBounded`, a node with `t - 1` keys has `0` or `t` children. -/
lemma childBounded_len_of_keys {t : Nat} (ht : 1 ≤ t) {ks : List Nat} {cs : List BTree}
    (h_cb : ChildBounded (node ks cs)) (hks : ks.length = t - 1) :
    cs = [] ∨ cs.length = t := by
  unfold ChildBounded at h_cb
  rcases h_cb with ⟨hrel, _, _⟩
  rcases hrel with hemp | heq
  · left; cases cs with | nil => rfl | cons x xs => simp at hemp
  · right; rw [heq, hks]; omega

/--
**Merge preserves `Occupancy`.**  Merging two minimal siblings (`t - 1` keys
each) produces a *full* non-root node: `2t - 1` keys and either `0` or `2t`
children.  This is the occupancy face of CLRS deletion case 3b.
-/
lemma mergeNodes_occupancy {t : Nat} (ht : 2 ≤ t)
    {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hlk : lKeys.length = t - 1) (hrk : rKeys.length = t - 1)
    (hL_cb : ChildBounded (node lKeys lCh)) (hR_cb : ChildBounded (node rKeys rCh))
    (hL_occ : Occupancy t false (node lKeys lCh))
    (hR_occ : Occupancy t false (node rKeys rCh)) :
    Occupancy t false (mergeNodes (node lKeys lCh) sep (node rKeys rCh)) := by
  rw [mergeNodes_node]
  have hlc : lCh = [] ∨ lCh.length = t := childBounded_len_of_keys (by omega) hL_cb hlk
  have hrc : rCh = [] ∨ rCh.length = t := childBounded_len_of_keys (by omega) hR_cb hrk
  have hL_sub : ∀ c ∈ lCh, Occupancy t false c := by
    unfold Occupancy at hL_occ; obtain ⟨-, -, -, h⟩ := hL_occ; exact h
  have hR_sub : ∀ c ∈ rCh, Occupancy t false c := by
    unfold Occupancy at hR_occ; obtain ⟨-, -, -, h⟩ := hR_occ; exact h
  have hkeys_len : (lKeys ++ sep :: rKeys).length = 2 * t - 1 := by
    simp only [List.length_append, List.length_cons]; omega
  have h_children_bound :
      ((lCh ++ rCh).isEmpty = true) ∨ (t ≤ (lCh ++ rCh).length ∧ (lCh ++ rCh).length ≤ 2 * t) := by
    rcases hlc with h0 | hlt <;> rcases hrc with h0' | hrt
    · left; rw [h0, h0']; rfl
    · right; subst h0; rw [List.nil_append, hrt]; exact ⟨le_rfl, by omega⟩
    · right; subst h0'; rw [List.append_nil, hlt]; exact ⟨le_rfl, by omega⟩
    · right; rw [List.length_append, hlt, hrt]; exact ⟨by omega, by omega⟩
  unfold Occupancy
  refine ⟨?_, ?_, h_children_bound, ?_⟩
  · -- lower bound t - 1 ≤ keys.length
    have h : t - 1 ≤ (lKeys ++ sep :: rKeys).length := by rw [hkeys_len]; omega
    exact h
  · -- upper bound keys.length ≤ 2t - 1
    have h : (lKeys ++ sep :: rKeys).length ≤ 2 * t - 1 := by rw [hkeys_len]
    exact h
  · -- sub-child occupancy inherited from the two siblings
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_sub c hc
    · exact hR_sub c hc

/-! ## `mergeNodes` preserves `ChildBounded` -/

/--
**Merge preserves `ChildBounded`.**  Merging two sibling subtrees around a
separator yields a node whose children count and key bounds satisfy `ChildBounded`.
-/
lemma mergeNodes_childBounded {t : Nat} (ht : 2 ≤ t)
    {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hL_cb : ChildBounded (node lKeys lCh)) (hR_cb : ChildBounded (node rKeys rCh))
    (hL_le : ∀ k ∈ keysOf (node lKeys lCh), k ≤ sep)
    (hR_ge : ∀ k ∈ keysOf (node rKeys rCh), sep ≤ k) :
    ChildBounded (mergeNodes (node lKeys lCh) sep (node rKeys rCh)) := by
  rw [mergeNodes_node]
  sorry
/-! ## `mergeNodes` preserves `Sorted` -/

lemma mergeNodes_sorted {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hL_s : Sorted (node lKeys lCh)) (hR_s : Sorted (node rKeys rCh))
    (hL_le : ∀ k ∈ keysOf (node lKeys lCh), k ≤ sep)
    (hR_ge : ∀ k ∈ keysOf (node rKeys rCh), sep ≤ k) :
    Sorted (mergeNodes (node lKeys lCh) sep (node rKeys rCh)) := by
  rw [mergeNodes_node]
  unfold Sorted; unfold Sorted at hL_s hR_s
  obtain ⟨hL_pw, hL_ch⟩ := hL_s
  obtain ⟨hR_pw, hR_ch⟩ := hR_s
  refine ⟨?_, ?_⟩
  · have hL_all : ∀ k ∈ lKeys, k ≤ sep := by
      intro k hk; apply hL_le k; simp [keysOf, hk]
    have hR_all : ∀ k ∈ rKeys, sep ≤ k := by
      intro k hk; apply hR_ge k; simp [keysOf, hk]
    have h_sep_rKeys_pw : List.Pairwise (· ≤ ·) (sep :: rKeys) :=
      List.Pairwise.cons hR_all hR_pw
    have h_cross : ∀ a ∈ lKeys, ∀ b ∈ sep :: rKeys, a ≤ b := by
      intro a ha b hb
      rcases List.mem_cons.mp hb with (rfl | hb_rKeys)
      · exact hL_all a ha
      · exact le_trans (hL_all a ha) (hR_all b hb_rKeys)
    rw [List.pairwise_append]
    exact ⟨hL_pw, h_sep_rKeys_pw, h_cross⟩
  · intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_ch c hc
    · exact hR_ch c hc

/-! ## `composedDelete` preserves `WellFormed` — proof roadmap

The main invariant theorem `composedDelete_wellFormed` states that for any
`WellFormed` B-tree, `composedDelete` preserves `Sorted`, `ChildBounded`,
`Occupancy`, and `SameDepth`.  The proof uses strong induction on `heightOf`
with the three cases of the algorithm:

1. **Leaf case**: `sortedRemove` reduces keys by at most 1.
2. **Key-at-separator case**: merge neighboring children via `mergeNodes`
   (using `mergeNodes_sorted`, `mergeNodes_sameDepth`, `mergeNodes_occupancy`),
   then recurse.
3. **Recurse-into-child case**: IH on the child.

The remaining work is the **pre-emptive repair** logic (CLRS case 3): before
case 3, ensure the target child has ≥ `t` keys by borrowing from a sibling
(`rotateRight`/`rotateLeft`) or merging.  The building blocks are ready:
`mergeNodes_sorted` (proved above), `mergeNodes_sameDepth`,
`mergeNodes_occupancy`, and `rotateRight_preserves`.  What's missing:
a `rotateLeft` definition (mirror of `rotateRight`) with its preservation
lemmas, and the full `composedDelete_wellFormed` proof assembling all four
invariant components.

The proof structure follows the `insertNonFull_wellFormed` pattern from
Section 18.2, using a custom `.induct` lemma for case analysis.
-/

/-- From `ChildBounded`, a node either has no children or has exactly one more
child than keys. -/
lemma childBounded_children_rel {ks : List Nat} {cs : List BTree}
    (h_cb : ChildBounded (node ks cs)) : cs = [] ∨ cs.length = ks.length + 1 := by
  unfold ChildBounded at h_cb
  rcases h_cb with ⟨hrel, _, _⟩
  rcases hrel with hemp | heq
  · left; cases cs with | nil => rfl | cons x xs => simp at hemp
  · right; exact heq

/-! ## Occupancy (de)constructors and shared repair infrastructure -/

/-- Destructor for a non-root `Occupancy` fact into its four plain components. -/
lemma occupancy_false_dest {t : Nat} {ks : List Nat} {cs : List BTree}
    (h : Occupancy t false (node ks cs)) :
    t - 1 ≤ ks.length ∧ ks.length ≤ 2 * t - 1 ∧
    (cs = [] ∨ (t ≤ cs.length ∧ cs.length ≤ 2 * t)) ∧ (∀ c ∈ cs, Occupancy t false c) := by
  unfold Occupancy at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, ?_, h4⟩
  rcases h3 with he | hb
  · left; cases cs with | nil => rfl | cons x xs => simp at he
  · right; exact hb

/-- Constructor for a non-root `Occupancy` fact from its four plain components. -/
lemma occupancy_false_intro {t : Nat} {ks : List Nat} {cs : List BTree}
    (h1 : t - 1 ≤ ks.length) (h2 : ks.length ≤ 2 * t - 1)
    (h3 : cs = [] ∨ (t ≤ cs.length ∧ cs.length ≤ 2 * t))
    (h4 : ∀ c ∈ cs, Occupancy t false c) :
    Occupancy t false (node ks cs) := by
  unfold Occupancy
  refine ⟨h1, h2, ?_, h4⟩
  rcases h3 with he | hb
  · left; rw [he]; rfl
  · right; exact hb

/-- Each child of a `SameDepth` node is itself `SameDepth`. -/
lemma sameDepth_children_sd {ks : List Nat} {cs : List BTree}
    (h : SameDepth (node ks cs)) : ∀ c ∈ cs, SameDepth c := by
  cases h with
  | leaf _ => intro c hc; simp at hc
  | internal _ c0 cs' _ hsd0 hsds =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact hsd0
      · exact hsds c hc'

/-- Two equal-height sibling subtrees are simultaneously leaves or simultaneously
internal. -/
lemma leaf_iff_of_height_eq {lKeys rKeys : List Nat} {lCh rCh : List BTree}
    (hht : heightOf (node lKeys lCh) = heightOf (node rKeys rCh)) :
    lCh = [] ↔ rCh = [] := by
  rw [← heightOf_eq_zero_iff lKeys lCh, ← heightOf_eq_zero_iff rKeys rCh, hht]

/-- Any child of the left sibling has the same height as any child of the right
sibling, given the two siblings have equal height. -/
lemma child_height_bridge {lKeys rKeys : List Nat} {lCh rCh : List BTree}
    (hL : SameDepth (node lKeys lCh)) (hR : SameDepth (node rKeys rCh))
    (hht : heightOf (node lKeys lCh) = heightOf (node rKeys rCh))
    {c d : BTree} (hc : c ∈ lCh) (hd : d ∈ rCh) : heightOf c = heightOf d := by
  obtain ⟨a, as, rfl⟩ : ∃ a as, lCh = a :: as := by
    cases lCh with
    | nil => simp at hc
    | cons a as => exact ⟨a, as, rfl⟩
  obtain ⟨b, bs, rfl⟩ : ∃ b bs, rCh = b :: bs := by
    cases rCh with
    | nil => simp at hd
    | cons b bs => exact ⟨b, bs, rfl⟩
  have hLh : heightOf (node lKeys (a :: as)) = 1 + heightOf a := heightOf_internal_of_sameDepth hL
  have hRh : heightOf (node rKeys (b :: bs)) = 1 + heightOf b := heightOf_internal_of_sameDepth hR
  have hab : heightOf a = heightOf b := by rw [hLh, hRh] at hht; omega
  have hca : heightOf c = heightOf a := sameDepth_children_eq_height hL c hc a (by simp)
  have hdb : heightOf d = heightOf b := sameDepth_children_eq_height hR d hd b (by simp)
  rw [hca, hdb, hab]

/-! ## `rotateRight`: borrow a key from the right sibling (CLRS case 3a) -/

/--
**Borrow from the right sibling (CLRS `B-TREE-DELETE` case 3a).**  The
underflowing left child receives the separator `sep` as a new last key and the
right sibling's first child; the right sibling's first key rises to become the
new separator.  Returns `(newLeft, newSep, newRight)`.
-/
def rotateRight : BTree → Nat → BTree → BTree × Nat × BTree
  | node lKeys lCh, sep, node rKeys rCh =>
    match rKeys with
    | [] => (node lKeys lCh, sep, node rKeys rCh)
    | rHead :: rTail =>
        (node (lKeys ++ [sep]) (lCh ++ rCh.take 1), rHead, node rTail (rCh.drop 1))

/-- `rotateRight` reduces on a right sibling with at least one key. -/
@[simp] lemma rotateRight_cons (lKeys rTail : List Nat) (lCh rCh : List BTree)
    (sep rHead : Nat) :
    rotateRight (node lKeys lCh) sep (node (rHead :: rTail) rCh) =
      (node (lKeys ++ [sep]) (lCh ++ rCh.take 1), rHead, node rTail (rCh.drop 1)) := rfl

/--
**`rotateRight` new-left node is well formed.**  After borrowing, the repaired
left child has exactly `t` keys — above the minimum — and preserves `SameDepth`
and its height.  The equal-height hypothesis is supplied by the parent's
`SameDepth` invariant.
-/
lemma rotateRight_left {t : Nat} (ht : 2 ≤ t)
    {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hlk : lKeys.length = t - 1)
    (hL_cb : ChildBounded (node lKeys lCh))
    (hL : SameDepth (node lKeys lCh)) (hR : SameDepth (node rKeys rCh))
    (hL_occ : Occupancy t false (node lKeys lCh))
    (hR_occ : Occupancy t false (node rKeys rCh))
    (hht : heightOf (node lKeys lCh) = heightOf (node rKeys rCh)) :
    Occupancy t false (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) ∧
    SameDepth (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) ∧
    heightOf (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) = heightOf (node lKeys lCh) := by
  obtain ⟨_, _, _, hL_sub⟩ := occupancy_false_dest hL_occ
  obtain ⟨_, _, _, hR_sub⟩ := occupancy_false_dest hR_occ
  have hkeys_len : (lKeys ++ [sep]).length = t := by
    simp only [List.length_append, List.length_cons, List.length_nil, hlk]; omega
  by_cases hlc : lCh = []
  · -- both siblings are leaves: no child moves
    have hrc : rCh = [] := (leaf_iff_of_height_eq hht).mp hlc
    subst hlc; subst hrc
    simp only [List.nil_append, List.take_nil, List.append_nil]
    refine ⟨?_, SameDepth.leaf _, ?_⟩
    · exact occupancy_false_intro (by rw [hkeys_len]; omega) (by rw [hkeys_len]; omega) (Or.inl rfl)
        (by intro c hc; simp at hc)
    · simp [heightOf]
  · -- both internal: one child rotates over
    obtain ⟨a, as, rfl⟩ : ∃ a as, lCh = a :: as := by
      cases lCh with
      | nil => exact absurd rfl hlc
      | cons a as => exact ⟨a, as, rfl⟩
    have hrc_ne : rCh ≠ [] := fun h => hlc ((leaf_iff_of_height_eq hht).mpr h)
    obtain ⟨b, bs, rfl⟩ : ∃ b bs, rCh = b :: bs := by
      cases rCh with
      | nil => exact absurd rfl hrc_ne
      | cons b bs => exact ⟨b, bs, rfl⟩
    have htake : (b :: bs).take 1 = [b] := rfl
    rw [htake]
    have hlen : (a :: as).length = t := by
      rcases childBounded_len_of_keys (by omega) hL_cb hlk with h | h
      · exact absurd h (by simp)
      · exact h
    have hchildren_len : ((a :: as) ++ [b]).length = t + 1 := by
      rw [List.length_append, hlen]; rfl
    -- heights: every element of the new children list has height `heightOf a`
    have hb_ht : heightOf b = heightOf a :=
      (child_height_bridge hL hR hht (c := a) (d := b) (by simp) (by simp)).symm
    have huniform : ∀ c ∈ ((a :: as) ++ [b]), heightOf c = heightOf a := by
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact sameDepth_children_eq_height hL c hc a (by simp)
      · simp only [List.mem_singleton] at hc; rw [hc]; exact hb_ht
    have hsd_all : ∀ c ∈ ((a :: as) ++ [b]), SameDepth c := by
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact sameDepth_children_sd hL c hc
      · simp only [List.mem_singleton] at hc; rw [hc]; exact sameDepth_children_sd hR b (by simp)
    have huniform_tail : ∀ c ∈ (as ++ [b]), heightOf c = heightOf a := by
      intro c hc; exact huniform c (by rw [List.cons_append]; exact List.mem_cons_of_mem a hc)
    refine ⟨?_, ?_, ?_⟩
    · -- occupancy: t keys, t+1 children
      refine occupancy_false_intro (by rw [hkeys_len]; omega) (by rw [hkeys_len]; omega)
        (Or.inr ⟨by rw [hchildren_len]; omega, by rw [hchildren_len]; omega⟩) ?_
      · intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hL_sub c hc
        · simp only [List.mem_singleton] at hc; rw [hc]; exact hR_sub b (by simp)
    · exact sameDepth_of_uniform (H := heightOf a) huniform hsd_all
    · rw [List.cons_append, heightOf_uniform_children huniform_tail,
        heightOf_internal_of_sameDepth hL]

/--
**`rotateRight` new-right node is well formed.**  After the borrow, the right
sibling has one fewer key (still at least `t - 1`) and preserves `SameDepth` and
its height.
-/
lemma rotateRight_right {t : Nat} (ht : 2 ≤ t)
    {rHead : Nat} {rTail : List Nat} {rCh : List BTree}
    (hrlen : t ≤ (rHead :: rTail).length)
    (hR_cb : ChildBounded (node (rHead :: rTail) rCh))
    (hR_occ : Occupancy t false (node (rHead :: rTail) rCh))
    (hR : SameDepth (node (rHead :: rTail) rCh)) :
    Occupancy t false (node rTail (rCh.drop 1)) ∧
    SameDepth (node rTail (rCh.drop 1)) ∧
    heightOf (node rTail (rCh.drop 1)) = heightOf (node (rHead :: rTail) rCh) := by
  obtain ⟨_, hR_up, _, hR_sub⟩ := occupancy_false_dest hR_occ
  have hrtail : t - 1 ≤ rTail.length := by simp only [List.length_cons] at hrlen; omega
  have hrup : rTail.length ≤ 2 * t - 1 := by simp only [List.length_cons] at hR_up; omega
  by_cases hrc : rCh = []
  · -- right sibling is a leaf
    subst hrc
    simp only [List.drop_nil]
    refine ⟨occupancy_false_intro hrtail hrup (Or.inl rfl) (by intro c hc; simp at hc),
      SameDepth.leaf _, ?_⟩
    simp [heightOf]
  · obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, rCh = c0 :: cs := by
      cases rCh with
      | nil => exact absurd rfl hrc
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hdrop : (c0 :: cs).drop 1 = cs := rfl
    rw [hdrop]
    -- `cs` is nonempty because the internal node has ≥ t ≥ 2 children
    have hchlen : (c0 :: cs).length = (rHead :: rTail).length + 1 := by
      rcases childBounded_children_rel hR_cb with h | h
      · exact absurd h (by simp)
      · exact h
    have hcs_ne : cs ≠ [] := by
      intro h; rw [h] at hchlen; simp only [List.length_cons, List.length_nil] at hchlen; omega
    obtain ⟨d0, ds, rfl⟩ : ∃ d0 ds, cs = d0 :: ds := by
      cases cs with
      | nil => exact absurd rfl hcs_ne
      | cons d0 ds => exact ⟨d0, ds, rfl⟩
    have huniform : ∀ c ∈ (d0 :: ds), heightOf c = heightOf d0 := by
      intro c hc
      exact sameDepth_children_eq_height hR c (by simp [hc]) d0 (by simp)
    have hsd_all : ∀ c ∈ (d0 :: ds), SameDepth c := by
      intro c hc; exact sameDepth_children_sd hR c (by simp [hc])
    have hd0c0 : heightOf d0 = heightOf c0 :=
      sameDepth_children_eq_height hR d0 (by simp) c0 (by simp)
    have huniform_ds : ∀ c ∈ ds, heightOf c = heightOf d0 :=
      fun c hc => huniform c (List.mem_cons_of_mem d0 hc)
    refine ⟨?_, ?_, ?_⟩
    · -- occupancy: rTail.length keys, rTail.length+1 children
      have hchild_len : (d0 :: ds).length = rTail.length + 1 := by
        simp only [List.length_cons] at hchlen ⊢; omega
      refine occupancy_false_intro hrtail hrup (Or.inr ?_) ?_
      · rw [hchild_len]; exact ⟨by omega, by omega⟩
      · intro c hc; exact hR_sub c (List.mem_cons_of_mem c0 hc)
    · exact sameDepth_of_uniform (H := heightOf d0) huniform hsd_all
    · rw [heightOf_uniform_children huniform_ds,
        heightOf_internal_of_sameDepth hR, hd0c0]

/--
**`rotateRight` preserves every node-level invariant.**  Both nodes produced by
the borrow (the repaired child and the trimmed sibling) satisfy `Occupancy`,
`SameDepth`, and keep their original heights.  This is the full node-level
statement of CLRS deletion case 3a.
-/
theorem rotateRight_preserves {t : Nat} (ht : 2 ≤ t)
    {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hlk : lKeys.length = t - 1) (hrlen : t ≤ rKeys.length)
    (hL_cb : ChildBounded (node lKeys lCh)) (hR_cb : ChildBounded (node rKeys rCh))
    (hL : SameDepth (node lKeys lCh)) (hR : SameDepth (node rKeys rCh))
    (hL_occ : Occupancy t false (node lKeys lCh)) (hR_occ : Occupancy t false (node rKeys rCh))
    (hht : heightOf (node lKeys lCh) = heightOf (node rKeys rCh)) :
    (Occupancy t false (rotateRight (node lKeys lCh) sep (node rKeys rCh)).1 ∧
     SameDepth (rotateRight (node lKeys lCh) sep (node rKeys rCh)).1 ∧
     heightOf (rotateRight (node lKeys lCh) sep (node rKeys rCh)).1 = heightOf (node lKeys lCh)) ∧
    (Occupancy t false (rotateRight (node lKeys lCh) sep (node rKeys rCh)).2.2 ∧
     SameDepth (rotateRight (node lKeys lCh) sep (node rKeys rCh)).2.2 ∧
     heightOf (rotateRight (node lKeys lCh) sep (node rKeys rCh)).2.2 = heightOf (node rKeys rCh)) := by
  obtain ⟨rHead, rTail, rfl⟩ : ∃ rHead rTail, rKeys = rHead :: rTail := by
    cases rKeys with
    | nil => simp only [List.length_nil] at hrlen; omega
    | cons rHead rTail => exact ⟨rHead, rTail, rfl⟩
  simp only [rotateRight_cons]
  exact ⟨rotateRight_left ht hlk hL_cb hL hR hL_occ hR_occ hht,
         rotateRight_right ht hrlen hR_cb hR_occ hR⟩


/-! ## Helper functions for the composed delete -/

/-- Number of keys in a B-tree node. -/
def numKeys : BTree → Nat
  | node ks _ => ks.length

/-- Remove the first occurrence of `x` from a list. -/
def sortedRemove (x : Nat) : List Nat → List Nat
  | [] => []
  | k :: ks => if k = x then ks else k :: sortedRemove x ks

@[simp] lemma sortedRemove_nil (x : Nat) : sortedRemove x [] = [] := rfl

lemma sortedRemove_cons (x k : Nat) (ks : List Nat) :
    sortedRemove x (k :: ks) = if k = x then ks else k :: sortedRemove x ks := rfl

/-- `sortedRemove` doesn't introduce new elements. -/
lemma mem_of_sortedRemove {x y : Nat} {ks : List Nat} (hy : y ∈ sortedRemove x ks) : y ∈ ks := by
  induction ks with
  | nil => simp [sortedRemove] at hy
  | cons k ks ih =>
    rw [sortedRemove_cons] at hy
    split at hy
    · subst k; simp [hy]
    · simp at hy; rcases hy with (rfl | hy)
      · simp
      · simp [ih hy]

/-- `sortedRemove` preserves sortedness. -/
lemma sortedRemove_sorted (x : Nat) : ∀ {ks : List Nat}, List.Pairwise (· ≤ ·) ks →
    List.Pairwise (· ≤ ·) (sortedRemove x ks) := by
  intro ks h
  induction ks with
  | nil => exact h
  | cons k ks ih =>
    rw [sortedRemove_cons]
    split
    · exact h.tail
    · refine List.Pairwise.cons ?_ (ih h.tail)
      obtain ⟨hk, _⟩ := List.pairwise_cons.mp h
      intro a ha
      exact hk a (mem_of_sortedRemove ha)

/-! ### `sortedRemove` length bounds -/

lemma sortedRemove_length_le (x : Nat) (ks : List Nat) :
    (sortedRemove x ks).length ≤ ks.length := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [sortedRemove_cons]; split <;> simp [ih]

lemma sortedRemove_length_ge (x : Nat) (ks : List Nat) :
    ks.length - 1 ≤ (sortedRemove x ks).length := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [sortedRemove_cons]; split
    · simp
    · simp; omega

/-! ### `sortedRemove` preserves leaf invariants -/

lemma sortedRemove_sorted_leaf (x : Nat) (ks : List Nat)
    (hs : List.Pairwise (· ≤ ·) ks) :
    List.Pairwise (· ≤ ·) (sortedRemove x ks) := by
  induction ks with
  | nil => exact hs
  | cons k ks ih =>
    rw [sortedRemove_cons]; split
    · exact hs.tail
    · refine List.Pairwise.cons ?_ (ih hs.tail)
      obtain ⟨hk, _⟩ := List.pairwise_cons.mp hs
      intro a ha; exact hk a (mem_of_sortedRemove ha)

/-! ## Composed delete (CLRS B-TREE-DELETE) -/


/-! ## Height of mergeNodes (for termination of composedDelete) -/

/-- The height of a merged node is the maximum of the two component heights.
This holds for all trees, not just well-formed ones, and does not require
`SameDepth`. -/
lemma foldl_max_aux (a : Nat) (bs : List Nat) : (bs.foldl max a) = max a (bs.foldl max 0) := by
  induction bs generalizing a with
  | nil => simp
  | cons b bs ih =>
    calc
      (b :: bs).foldl max a = (bs.foldl max (max a b)) := by simp [List.foldl_cons]
      _ = max (max a b) (bs.foldl max 0) := by rw [ih]
      _ = max a (max b (bs.foldl max 0)) := by omega
      _ = max a ((b :: bs).foldl max 0) := by
        rw [List.foldl_cons, show max (0 : Nat) b = b by omega, ih b]

lemma foldl_max_append (l₁ l₂ : List Nat) : ((l₁ ++ l₂).foldl max 0) = max (l₁.foldl max 0) (l₂.foldl max 0) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    calc
      ((a :: (l₁ ++ l₂)).foldl max 0) = ((l₁ ++ l₂).foldl max (max 0 a)) := by simp
      _ = max (max 0 a) (((l₁ ++ l₂).foldl max 0)) := by rw [foldl_max_aux]
      _ = max (max 0 a) (max (l₁.foldl max 0) (l₂.foldl max 0)) := by rw [ih]
      _ = max a (max (l₁.foldl max 0) (l₂.foldl max 0)) := by omega
      _ = max ((a :: l₁).foldl max 0) (l₂.foldl max 0) := by
        calc
          max a (max (l₁.foldl max 0) (l₂.foldl max 0))
              = max (max a (l₁.foldl max 0)) (l₂.foldl max 0) := by omega
          _ = max ((a :: l₁).foldl max 0) (l₂.foldl max 0) := by
            have h : (a :: l₁).foldl max 0 = max a (l₁.foldl max 0) := by
              calc
                (a :: l₁).foldl max 0 = (l₁.foldl max (max 0 a)) := by simp
                _ = (l₁.foldl max a) := by simp
                _ = max a (l₁.foldl max 0) := by rw [foldl_max_aux]
            rw [h]

lemma heightOf_mergeNodes_eq_max {left right : BTree} {sep : Nat} :
    heightOf (mergeNodes left sep right) = max (heightOf left) (heightOf right) := by
  cases left with
  | node lKeys lCh =>
    cases right with
    | node rKeys rCh =>
      rw [mergeNodes_node]
      by_cases hl : lCh = []
      · subst hl
        by_cases hr : rCh = []
        · subst hr; simp [heightOf]
        · simp [heightOf, hr]
      · by_cases hr : rCh = []
        · subst hr; simp [heightOf, hl]
        · have hne : lCh ++ rCh ≠ [] := by
            intro h
            have hnil := (List.append_eq_nil_iff.mp h).1
            exact hl hnil
          set A := ((lCh.map heightOf).foldl max 0) with hA
          set B := ((rCh.map heightOf).foldl max 0) with hB
          have hcalc : 1 + max A B = max (1 + A) (1 + B) := by
            by_cases h : A ≤ B
            · rw [Nat.max_eq_right h, Nat.max_eq_right (by omega : 1 + A ≤ 1 + B)]
            · rw [Nat.max_eq_left (by omega : B ≤ A), Nat.max_eq_left (by omega : 1 + B ≤ 1 + A)]
          -- Expand heightOf for the three nodes
          have hlCh_ht : heightOf (node lKeys lCh) = 1 + A := by
            simp [heightOf, hl, hA]
          have hrCh_ht : heightOf (node rKeys rCh) = 1 + B := by
            simp [heightOf, hr, hB]
          have hmerged_ht : heightOf (node (lKeys ++ sep :: rKeys) (lCh ++ rCh)) = 1 + (((lCh ++ rCh).map heightOf).foldl max 0) := by
            simp [heightOf, hne]
          rw [hmerged_ht, hlCh_ht, hrCh_ht, List.map_append, foldl_max_append, hcalc]

def composedDelete (t : Nat) (x : Nat) : BTree → BTree
  | node ks cs =>
    if cs.isEmpty then
      node (sortedRemove x ks) []
    else
      let i := findChild ks x
      if hiPos : 0 < i then
        let ki := i - 1
        match hk : ks[ki]? with
        | some k =>
          if hkeq : k = x then
            match hcl : cs[ki]? with
            | some leftChild =>
              match hcr : cs[ki + 1]? with
              | some rightChild =>
                let merged := mergeNodes leftChild k rightChild
                let newMerged := composedDelete t x merged
                node (ks.take ki ++ ks.drop (ki + 1)) ((cs.take ki) ++ [newMerged] ++ (cs.drop (ki + 2)))
              | none => node (sortedRemove x ks) []
            | none => node (sortedRemove x ks) []
          else
            match hc : cs[i]? with
            | some child => node ks (cs.set i (composedDelete t x child))
            | none => node ks cs
        | none =>
          match hc : cs[i]? with
          | some child => node ks (cs.set i (composedDelete t x child))
          | none => node ks cs
      else
        match hc : cs[0]? with
        | some child => node ks (cs.set 0 (composedDelete t x child))
        | none => node ks cs
termination_by tr => heightOf tr
decreasing_by
  · -- Merge case: heightOf merged < heightOf (node ks cs)
    rw [heightOf_mergeNodes_eq_max]
    have hmem_left : leftChild ∈ cs := by
      apply List.mem_iff_getElem?.mpr
      exact ⟨ki, hcl⟩
    have h_lt_left : heightOf leftChild < heightOf (node ks cs) := heightOf_mem_lt hmem_left
    have hmem_right : rightChild ∈ cs := by
      apply List.mem_iff_getElem?.mpr
      exact ⟨ki + 1, hcr⟩
    have h_lt_right : heightOf rightChild < heightOf (node ks cs) := heightOf_mem_lt hmem_right
    omega
  · -- Recursion into child i
    have hmem : child ∈ cs :=
      (List.mem_iff_getElem? (a := child) (l := cs)).mpr ⟨i, hc⟩
    exact heightOf_mem_lt hmem
  · -- Recursion into child i (from the hk none branch)
    have hmem : child ∈ cs :=
      (List.mem_iff_getElem? (a := child) (l := cs)).mpr ⟨i, hc⟩
    exact heightOf_mem_lt hmem
  · -- Recursion into child 0 (here i = 0 from the else branch)
    have hmem : child ∈ cs :=
      (List.mem_iff_getElem? (a := child) (l := cs)).mpr ⟨0, hc⟩
    exact heightOf_mem_lt hmem
/-! ## `composedDelete` preserves `WellFormed` for leaves -/

theorem composedDelete_leaf_wellFormed (t x : Nat) (ht : 2 ≤ t) (ks : List Nat)
    (hwf : WellFormed t (node ks [])) :
    WellFormed t (composedDelete t x (node ks [])) := by
  have hleaf : composedDelete t x (node ks []) = node (sortedRemove x ks) [] := by
    simp [composedDelete]
  rw [hleaf]
  obtain ⟨hs, hcb, hocc, hsd⟩ := hwf
  -- Extract Sorted
  have hs_keys : List.Pairwise (· ≤ ·) ks := by
    unfold Sorted at hs; simp at hs; exact hs
  -- Extract Occupancy bounds
  unfold Occupancy at hocc
  have hks_up : ks.length ≤ 2*t-1 := hocc.2.1
  -- Build result components
  have h_sorted : Sorted (node (sortedRemove x ks) []) := by
    unfold Sorted; simp; exact sortedRemove_sorted_leaf x ks hs_keys
  have h_childBounded : ChildBounded (node (sortedRemove x ks) []) :=
    childBounded_node_nil (sortedRemove x ks)
  have h_occupancy : Occupancy t true (node (sortedRemove x ks) []) := by
    unfold Occupancy
    refine ⟨?_, ?_, by simp, fun c hc => by simp at hc⟩
    · -- lower bound: (if result = [] then 0 else 1) ≤ result.length
      dsimp
      by_cases h0 : (sortedRemove x ks).length = 0
      · simp [h0]
      · have h_low : 1 ≤ (sortedRemove x ks).length := by omega
        simp [h0, h_low]
    · -- upper bound: result.length ≤ 2*t-1
      have hlen := sortedRemove_length_le x ks
      omega
  have h_sameDepth : SameDepth (node (sortedRemove x ks) []) :=
    SameDepth.leaf (sortedRemove x ks)
  unfold WellFormed
  exact ⟨h_sorted, h_childBounded, h_occupancy, h_sameDepth⟩

/-! ## `composedDelete` preserves `SameDepth` and height

Uses Nat.strongRecOn. Handles leaf, degenerate, direct-recursion, and merge cases.
-/

lemma composedDelete_sameDepth_height (t x : Nat) (ht : 2 ≤ t) (tr : BTree)
    (hcb : ChildBounded tr) (hsd : SameDepth tr) :
    SameDepth (composedDelete t x tr) ∧ heightOf (composedDelete t x tr) = heightOf tr := by
  let motive (n : Nat) : Prop := ∀ (tr' : BTree), heightOf tr' = n → ChildBounded tr' → SameDepth tr' →
    SameDepth (composedDelete t x tr') ∧ heightOf (composedDelete t x tr') = heightOf tr'
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ih tr' hn hcb' hsd'
    cases tr' with
    | node ks cs =>
      by_cases h_leaf : cs.isEmpty
      · have hcs : cs = [] := List.isEmpty_iff.mp h_leaf
        subst hcs
        rw [composedDelete]; simp
        exact ⟨SameDepth.leaf _, by simp [heightOf]⟩
      · -- Internal node: expand composedDelete
        rw [composedDelete]
        simp [h_leaf]
        -- let binders are definitionally transparent, proceed to case split
        by_cases hiPos : 0 < findChild ks x
        · simp [hiPos]
          set ki := (findChild ks x) - 1
          match hk : ks[ki]? with
          | some k =>
            by_cases hkeq : k = x
            · -- Merge case: FIXME
              sorry
            · simp [hkeq]
              match hc : cs[findChild ks x]? with
              | some child =>
                -- Direct recursion into child i
                have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
                have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                have hcb_child : ChildBounded child := by
                  unfold ChildBounded at hcb'; rcases hcb' with ⟨_, _, hsub⟩; exact hsub _ hmem
                have hsd_child : SameDepth child := (sameDepth_iff.mp hsd').1 _ hmem
                have h_lt_n : heightOf child < n :=
                  calc heightOf child < heightOf (node ks cs) := h_lt
                       _ = n := hn
                rcases ih (heightOf child) h_lt_n child rfl hcb_child hsd_child
                  with ⟨ihsd, ihht⟩
                -- Build the result: node ks (cs.set (findChild ks x) ...)
                have hHT : ∀ c' ∈ cs.set (findChild ks x) (composedDelete t x child),
                    heightOf c' = heightOf child := by
                  intro c' hc'
                  rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
                  · exact (sameDepth_iff.mp hsd').2 c' hcs _ hmem
                  · exact ihht
                have hSD : ∀ c' ∈ cs.set (findChild ks x) (composedDelete t x child), SameDepth c' := by
                  intro c' hc'
                  rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
                  · exact (sameDepth_iff.mp hsd').1 _ hcs
                  · exact ihsd
                refine ⟨sameDepth_iff.mpr ⟨hSD, fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩, ?_⟩
                have hi_lt : findChild ks x < cs.length :=
                  (List.getElem?_eq_some_iff.mp hc).1
                have hmem_res : composedDelete t x child ∈
                    cs.set (findChild ks x) (composedDelete t x child) :=
                  List.mem_set hi_lt _
                rw [heightOf_sameDepth_mem (sameDepth_iff.mpr ⟨hSD,
                  fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩) hmem_res,
                  hHT _ hmem_res, heightOf_sameDepth_mem hsd' hmem]
              | none => simp; exact hsd'
          | none =>
            match hc : cs[findChild ks x]? with
            | some child =>
              -- Same as above (direct recursion into child i)
              have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
              have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
              have hcb_child : ChildBounded child := by
                unfold ChildBounded at hcb'; rcases hcb' with ⟨_, _, hsub⟩; exact hsub _ hmem
              have hsd_child : SameDepth child := (sameDepth_iff.mp hsd').1 _ hmem
              have h_lt_n : heightOf child < n :=
                calc heightOf child < heightOf (node ks cs) := h_lt
                     _ = n := hn
              rcases ih (heightOf child) h_lt_n child rfl hcb_child hsd_child
                with ⟨ihsd, ihht⟩
              have hHT : ∀ c' ∈ cs.set (findChild ks x) (composedDelete t x child),
                  heightOf c' = heightOf child := by
                intro c' hc'
                rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
                · exact (sameDepth_iff.mp hsd').2 c' hcs _ hmem
                · exact ihht
              have hSD : ∀ c' ∈ cs.set (findChild ks x) (composedDelete t x child), SameDepth c' := by
                intro c' hc'
                rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
                · exact (sameDepth_iff.mp hsd').1 _ hcs
                · exact ihsd
              refine ⟨sameDepth_iff.mpr ⟨hSD, fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩, ?_⟩
              have hi_lt : findChild ks x < cs.length :=
                (List.getElem?_eq_some_iff.mp hc).1
              have hmem_res : composedDelete t x child ∈
                  cs.set (findChild ks x) (composedDelete t x child) :=
                List.mem_set hi_lt _
              rw [heightOf_sameDepth_mem (sameDepth_iff.mpr ⟨hSD,
                fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩) hmem_res,
                hHT _ hmem_res, heightOf_sameDepth_mem hsd' hmem]
            | none => simp; exact hsd'
        · -- i = 0 case
          simp [hiPos]
          match hc : cs[0]? with
          | some child =>
            have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨0, hc⟩
            have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
            have hcb_child : ChildBounded child := by
              unfold ChildBounded at hcb'; rcases hcb' with ⟨_, _, hsub⟩; exact hsub _ hmem
            have hsd_child : SameDepth child := (sameDepth_iff.mp hsd').1 _ hmem
            have h_lt_n : heightOf child < n :=
              calc heightOf child < heightOf (node ks cs) := h_lt
                   _ = n := hn
            rcases ih (heightOf child) h_lt_n child rfl hcb_child hsd_child
              with ⟨ihsd, ihht⟩
            have hHT : ∀ c' ∈ cs.set 0 (composedDelete t x child), heightOf c' = heightOf child := by
              intro c' hc'
              rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
              · exact (sameDepth_iff.mp hsd').2 c' hcs _ hmem
              · exact ihht
            have hSD : ∀ c' ∈ cs.set 0 (composedDelete t x child), SameDepth c' := by
              intro c' hc'
              rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
              · exact (sameDepth_iff.mp hsd').1 _ hcs
              · exact ihsd
            refine ⟨sameDepth_iff.mpr ⟨hSD, fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩, ?_⟩
            have h0_lt : 0 < cs.length := (List.getElem?_eq_some_iff.mp hc).1
            have hmem_res : composedDelete t x child ∈ cs.set 0 (composedDelete t x child) :=
              List.mem_set h0_lt _
            rw [heightOf_sameDepth_mem (sameDepth_iff.mpr ⟨hSD,
              fun a ha b hb => (hHT a ha).trans (hHT b hb).symm⟩) hmem_res,
              hHT _ hmem_res, heightOf_sameDepth_mem hsd' hmem]
          | none => simp; exact hsd'
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hcb hsd

/-! ## `composedDelete` preserves `Sorted`

Follows the `insertNonFull_sorted` case 5 pattern: use `List.mem_or_eq_of_mem_set`.
-/

lemma composedDelete_sorted (t x : Nat) (ht : 2 ≤ t) (tr : BTree)
    (hcb : ChildBounded tr) (hs : Sorted tr) : Sorted (composedDelete t x tr) := by
  let motive (n : Nat) : Prop := ∀ (tr' : BTree), heightOf tr' = n → ChildBounded tr' → Sorted tr' →
    Sorted (composedDelete t x tr')
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ih tr' hn hcb' hs'
    cases tr' with
    | node ks cs =>
      by_cases h_leaf : cs.isEmpty
      · have hcs : cs = [] := List.isEmpty_iff.mp h_leaf
        subst hcs
        rw [composedDelete]; simp
        unfold Sorted at hs'
        unfold Sorted; simp [sortedRemove_sorted_leaf x ks hs'.1]
      · rw [composedDelete]; simp [h_leaf]
        by_cases hiPos : 0 < findChild ks x
        · simp [hiPos]
          set ki := (findChild ks x) - 1
          match hk : ks[ki]? with
          | some k =>
            by_cases hkeq : k = x
            · -- Merge case: FIXME
              sorry
            · simp [hkeq]
              match hc : cs[findChild ks x]? with
              | some child =>
                have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
                have hcb_child : ChildBounded child := by
                  unfold ChildBounded at hcb'; rcases hcb' with ⟨_, _, hsub⟩; exact hsub _ hmem
                unfold Sorted at hs'
                rcases hs' with ⟨hks_pw, hks_sub⟩
                have hs_child : Sorted child := hks_sub _ hmem
                have h_lt_n : heightOf child < n := by
                  have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                  calc heightOf child < heightOf (node ks cs) := h_lt
                       _ = n := hn
                have ihc := ih (heightOf child) h_lt_n child rfl hcb_child hs_child
                unfold Sorted
                refine ⟨hks_pw, fun c hc' => ?_⟩
                rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
                · exact hks_sub _ hcs
                · exact ihc
              | none => simp; exact hs'
          | none =>
            match hc : cs[findChild ks x]? with
            | some child =>
              have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
              have hcb_child : ChildBounded child := by
                unfold ChildBounded at hcb'; rcases hcb' with ⟨_, _, hsub⟩; exact hsub _ hmem
              unfold Sorted at hs'
              rcases hs' with ⟨hks_pw, hks_sub⟩
              have hs_child : Sorted child := hks_sub _ hmem
              have h_lt_n : heightOf child < n := by
                have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                calc heightOf child < heightOf (node ks cs) := h_lt
                     _ = n := hn
              have ihc := ih (heightOf child) h_lt_n child rfl hcb_child hs_child
              unfold Sorted
              refine ⟨hks_pw, fun c hc' => ?_⟩
              rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
              · exact hks_sub _ hcs
              · exact ihc
            | none => simp; exact hs'
        · simp [hiPos]
          match hc : cs[0]? with
          | some child =>
            have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨0, hc⟩
            have hcb_child : ChildBounded child := by
              unfold ChildBounded at hcb'; rcases hcb' with ⟨_, _, hsub⟩; exact hsub _ hmem
            unfold Sorted at hs'
            rcases hs' with ⟨hks_pw, hks_sub⟩
            have hs_child : Sorted child := hks_sub _ hmem
            have h_lt_n : heightOf child < n := by
              have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
              calc heightOf child < heightOf (node ks cs) := h_lt
                   _ = n := hn
            have ihc := ih (heightOf child) h_lt_n child rfl hcb_child hs_child
            unfold Sorted
            refine ⟨hks_pw, fun c hc' => ?_⟩
            rcases List.mem_or_eq_of_mem_set hc' with hcs | rfl
            · exact hks_sub _ hcs
            · exact ihc
          | none => simp; exact hs'
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hcb hs

/-! ## `keysOf (composedDelete ...) ⊆ keysOf` parent

Proved by strong induction on height.
-/

lemma keysOf_composedDelete_subset (t x : Nat) (tr : BTree) (k : Nat)
    (hk : k ∈ keysOf (composedDelete t x tr)) : k ∈ keysOf tr := by
  sorry

/-! ## `composedDelete` preserves `ChildBounded`

Uses `childBounded_set` from Section 18.2.  The key-bound transfer (result keys
⊆ original keys) is admitted for now; the rest is proved.
-/

lemma composedDelete_childBounded (t x : Nat) (ht : 2 ≤ t) (tr : BTree)
    (hcb : ChildBounded tr) (hs : Sorted tr) : ChildBounded (composedDelete t x tr) := by
  let motive (n : Nat) : Prop := ∀ (tr' : BTree), heightOf tr' = n → ChildBounded tr' → Sorted tr' →
    ChildBounded (composedDelete t x tr')
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ih tr' hn hcb' hs'
    cases tr' with
    | node ks cs =>
      by_cases h_leaf : cs.isEmpty
      · have hcs : cs = [] := List.isEmpty_iff.mp h_leaf
        subst hcs
        rw [composedDelete]; simp
        exact childBounded_node_nil _
      · rw [composedDelete]; simp [h_leaf]
        by_cases hiPos : 0 < findChild ks x
        · simp [hiPos]
          set ki := (findChild ks x) - 1
          match hk : ks[ki]? with
          | some k =>
            by_cases hkeq : k = x
            · -- Merge case: FIXME
              sorry
            · simp [hkeq]
              match hc : cs[findChild ks x]? with
              | some child =>
                have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
                have hcb_info := hcb'
                unfold ChildBounded at hcb_info
                rcases hcb_info with ⟨hcb_rel, hcb_bounds, hcb_sub⟩
                have hcb_child : ChildBounded child := hcb_sub _ hmem
                unfold Sorted at hs'
                rcases hs' with ⟨hks_pw, hks_sub⟩
                have hs_child : Sorted child := hks_sub _ hmem
                have h_lt_n : heightOf child < n := by
                  have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                  calc heightOf child < heightOf (node ks cs) := h_lt
                       _ = n := hn
                have ihc := ih (heightOf child) h_lt_n child rfl hcb_child hs_child
                have hi_lt : findChild ks x < cs.length := (List.getElem?_eq_some_iff.mp hc).1
                -- Key bounds for the new child (FIXME: keysOf result ⊆ keysOf child)
                have h_lo : findChild ks x = 0 ∨ (match ks[(findChild ks x) - 1]? with
                    | some lo => ∀ k' ∈ keysOf (composedDelete t x child), lo ≤ k'
                    | none => True) := by
                  rcases hcb_bounds (findChild ks x) hi_lt with ⟨hlo, _⟩
                  rcases hlo with hz | hlo'
                  · exact Or.inl hz
                  · right
                    -- The original bound gives ∀ k' ∈ keysOf child, lo ≤ k'
                    -- We need ∀ k' ∈ keysOf result, lo ≤ k'
                    -- Admitted: keysOf result ⊆ keysOf child
                    sorry
                have h_hi : match ks[findChild ks x]? with
                    | some hi => ∀ k' ∈ keysOf (composedDelete t x child), k' ≤ hi
                    | none => True := by
                  rcases hcb_bounds (findChild ks x) hi_lt with ⟨_, hhi⟩
                  -- Same issue: need keysOf result ⊆ keysOf child
                  sorry
                exact childBounded_set hcb' hi_lt ihc h_lo h_hi
              | none => simp; exact hcb'
          | none =>
            match hc : cs[findChild ks x]? with
            | some child =>
              have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
              have hcb_info := hcb'
              unfold ChildBounded at hcb_info
              rcases hcb_info with ⟨hcb_rel, hcb_bounds, hcb_sub⟩
              have hcb_child : ChildBounded child := hcb_sub _ hmem
              unfold Sorted at hs'
              rcases hs' with ⟨hks_pw, hks_sub⟩
              have hs_child : Sorted child := hks_sub _ hmem
              have h_lt_n : heightOf child < n := by
                have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                calc heightOf child < heightOf (node ks cs) := h_lt
                     _ = n := hn
              have ihc := ih (heightOf child) h_lt_n child rfl hcb_child hs_child
              have hi_lt : findChild ks x < cs.length := (List.getElem?_eq_some_iff.mp hc).1
              have h_lo : findChild ks x = 0 ∨ (match ks[(findChild ks x) - 1]? with
                  | some lo => ∀ k' ∈ keysOf (composedDelete t x child), lo ≤ k'
                  | none => True) := by
                rcases hcb_bounds (findChild ks x) hi_lt with ⟨hlo, _⟩
                rcases hlo with hz | hlo'
                · exact Or.inl hz
                · right; admit -- keysOf subset lemma needed
              have h_hi : match ks[findChild ks x]? with
                  | some hi => ∀ k' ∈ keysOf (composedDelete t x child), k' ≤ hi
                  | none => True := by
                rcases hcb_bounds (findChild ks x) hi_lt with ⟨_, hhi⟩; sorry
              exact childBounded_set hcb' hi_lt ihc h_lo h_hi
            | none => simp; exact hcb'
        · simp [hiPos]
          match hc : cs[0]? with
          | some child =>
            have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨0, hc⟩
            have hcb_info := hcb'
            unfold ChildBounded at hcb_info
            rcases hcb_info with ⟨hcb_rel, hcb_bounds, hcb_sub⟩
            have hcb_child : ChildBounded child := hcb_sub _ hmem
            unfold Sorted at hs'
            rcases hs' with ⟨hks_pw, hks_sub⟩
            have hs_child : Sorted child := hks_sub _ hmem
            have h_lt_n : heightOf child < n := by
              have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
              calc heightOf child < heightOf (node ks cs) := h_lt
                   _ = n := hn
            have ihc := ih (heightOf child) h_lt_n child rfl hcb_child hs_child
            have h0_lt : 0 < cs.length := (List.getElem?_eq_some_iff.mp hc).1
            have h_lo : 0 = 0 ∨ (match ks[0 - 1]? with
                | some lo => ∀ k' ∈ keysOf (composedDelete t x child), lo ≤ k'
                | none => True) := Or.inl rfl
            have h_hi : match ks[0]? with
                | some hi => ∀ k' ∈ keysOf (composedDelete t x child), k' ≤ hi
                | none => True := by
              rcases hcb_bounds 0 h0_lt with ⟨_, hhi⟩; admit -- keysOf subset lemma needed
            exact childBounded_set hcb' h0_lt ihc h_lo h_hi
          | none => simp; exact hcb'
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hcb hs

/-! ## `composedDelete` preserves `Occupancy`

Uses `occupancy_set` from Section 18.2.  The occupancy downgrade (result child
satisfies `Occupancy t false`) is admitted for now.
-/

lemma composedDelete_occupancy (t x : Nat) (ht : 2 ≤ t) (tr : BTree) (b : Bool)
    (hcb : ChildBounded tr) (hocc : Occupancy t b tr) : Occupancy t b (composedDelete t x tr) := by
  let motive (n : Nat) : Prop := ∀ (tr' : BTree), heightOf tr' = n → ChildBounded tr' →
    (∀ (b' : Bool), Occupancy t b' tr' → Occupancy t b' (composedDelete t x tr'))
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ih tr' hn hcb' b' hocc'
    cases tr' with
    | node ks cs =>
      by_cases h_leaf : cs.isEmpty
      · have hcs : cs = [] := List.isEmpty_iff.mp h_leaf
        subst hcs
        rw [composedDelete]; simp
        -- Leaf: sortedRemove preserves occupancy
        by_cases hb : b'
        · -- Root (b' = true)
          subst hb
          unfold Occupancy at hocc' ⊢
          rcases hocc' with ⟨hlo, hup, hch, hsub⟩
          have hlen_le := sortedRemove_length_le x ks
          refine ⟨?_, ?_, by simp, fun c hc => by simp at hc⟩
          · -- lower bound
            simp
            split_ifs with h
            · exact Nat.zero_le _
            · -- h : sortedRemove x ks ≠ [], need 1 ≤ its length
              have hlen0 : (sortedRemove x ks).length ≠ 0 := by
                intro hzero; apply h; exact List.eq_nil_of_length_eq_zero hzero
              exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hlen0)
          · omega
        · -- Non-root (b' = false): admits (needs underflow guard)
          sorry
      · rw [composedDelete]; simp [h_leaf]
        by_cases hiPos : 0 < findChild ks x
        · simp [hiPos]
          set ki := (findChild ks x) - 1
          match hk : ks[ki]? with
          | some k =>
            by_cases hkeq : k = x
            · -- Merge case: FIXME
              sorry
            · simp [hkeq]
              match hc : cs[findChild ks x]? with
              | some child =>
                have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
                have hcb_child : ChildBounded child := by
                  have hi := hcb'; unfold ChildBounded at hi; rcases hi with ⟨_, _, hsub⟩; exact hsub _ hmem
                have hocc_child : Occupancy t false child := by
                  unfold Occupancy at hocc'; exact hocc'.2.2.2 _ hmem
                have h_lt_n : heightOf child < n := by
                  have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                  calc heightOf child < heightOf (node ks cs) := h_lt
                       _ = n := hn
                have ihc := ih (heightOf child) h_lt_n child rfl hcb_child false hocc_child
                have hi_lt : findChild ks x < cs.length := (List.getElem?_eq_some_iff.mp hc).1
                exact occupancy_set hocc' hi_lt ihc
              | none => simp; exact hocc'
          | none =>
            match hc : cs[findChild ks x]? with
            | some child =>
              have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨findChild ks x, hc⟩
              have hcb_child : ChildBounded child := by
                have hi := hcb'; unfold ChildBounded at hi; rcases hi with ⟨_, _, hsub⟩; exact hsub _ hmem
              have hocc_child : Occupancy t false child := by
                unfold Occupancy at hocc'; exact hocc'.2.2.2 _ hmem
              have h_lt_n : heightOf child < n := by
                have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
                calc heightOf child < heightOf (node ks cs) := h_lt
                     _ = n := hn
              have ihc := ih (heightOf child) h_lt_n child rfl hcb_child false hocc_child
              have hi_lt : findChild ks x < cs.length := (List.getElem?_eq_some_iff.mp hc).1
              exact occupancy_set hocc' hi_lt ihc
            | none => simp; exact hocc'
        · simp [hiPos]
          match hc : cs[0]? with
          | some child =>
            have hmem : child ∈ cs := by rw [List.mem_iff_getElem?]; exact ⟨0, hc⟩
            have hcb_child : ChildBounded child := by
              have hi := hcb'; unfold ChildBounded at hi; rcases hi with ⟨_, _, hsub⟩; exact hsub _ hmem
            have hocc_child : Occupancy t false child := by
              unfold Occupancy at hocc'; exact hocc'.2.2.2 _ hmem
            have h_lt_n : heightOf child < n := by
              have h_lt : heightOf child < heightOf (node ks cs) := heightOf_mem_lt hmem
              calc heightOf child < heightOf (node ks cs) := h_lt
                   _ = n := hn
            have ihc := ih (heightOf child) h_lt_n child rfl hcb_child false hocc_child
            have h0_lt : 0 < cs.length := (List.getElem?_eq_some_iff.mp hc).1
            exact occupancy_set hocc' h0_lt ihc
          | none => simp; exact hocc'
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hcb b hocc

/-!
Main theorem: composedDelete preserves the WellFormed invariant.
Assembles the four component lemmas.
-/

theorem composedDelete_wellFormed (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) : WellFormed t (composedDelete t x tr) := by
  rcases hwf with ⟨hs, hcb, hocc, hsd⟩
  exact ⟨composedDelete_sorted t x ht tr hcb hs,
         composedDelete_childBounded t x ht tr hcb hs,
         composedDelete_occupancy t x ht tr true hcb hocc,
         (composedDelete_sameDepth_height t x ht tr hcb hsd).1⟩

end BTree
end Chapter18
end CLRS
