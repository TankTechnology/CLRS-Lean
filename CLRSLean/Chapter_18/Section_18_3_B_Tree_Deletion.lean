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
end BTree
end Chapter18
end CLRS
