import CLRSLean.FourthEdition.Chapter_18.Section_18_1_B_Tree_Model
import CLRSLean.FourthEdition.Chapter_18.Section_18_2_B_Tree_Insertion

/-!
# CLRS Section 18.3 - B-tree deletion

This section contains both the first-pass key-membership specification and the
raw CLRS node algorithm with predecessor/successor replacement, sibling
rotation, and sibling merge.  The structural preservation proof is assembled
in the deletion submodules; root callers use a one-step normalization after
the raw operation.

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

The remaining semantic refinement first proves, without uniqueness assumptions,
that executable normalized deletion erases one occurrence from the
{lit}`keysOf` multiset; every different key is therefore preserved.  Because
specification-level {lit}`delete` filters every occurrence, bridging erase-one
to its exact membership equation and deriving requested-key absence require a
{lit}`UniqueKeys` invariant.  Structural preservation itself has no proof
placeholders.

## Implementation details

The deletion proof layers remain available outside the main sidebar:

* [Deletion invariants and root normalization](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Invariant/)
* [Rotation preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Rotation/)
* [Bundled local repair invariants](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Repair/)
* [Leaf and raw-result preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Preservation/)
* [Parent reassembly](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Reassembly/)
* [Parent reassembly after merging](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/MergeReassembly/)
* [Separator bounds after rotation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/RotationBounds/)
* [Parent reassembly after rotation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/RotationReassembly/)
* [Complete raw deletion preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/ComposedPreservation/)
* [Exact key multisets](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/KeyMultiset/)
* [Exact parent reassembly](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/ExactReassembly/)
* [Exact raw-deletion semantics](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Exact/)
* [Key subset and bounds](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Subset/)
* [Same-depth and height preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/SameDepthHeight/)
* [Sortedness preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Sorted/)
* [Child-bound preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/ChildBounded/)
* [Occupancy preservation](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/Occupancy/)
* [Root-normalized deletion](CLRSLean/FourthEdition/Chapter_18/Section_18_3_B_Tree_Deletion/WellFormed/)
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
**Membership in a merged node.**  The keys of `mergeNodes l sep r` are exactly
the keys of `l`, the separator `sep`, and the keys of `r`.
-/
lemma mem_keysOf_mergeNodes (l : BTree) (sep : Nat) (r : BTree) (k : Nat) :
    k ∈ keysOf (mergeNodes l sep r) ↔ k ∈ keysOf l ∨ k = sep ∨ k ∈ keysOf r := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      simp only [mergeNodes_node, keysOf, List.mem_append, List.mem_cons,
        List.flatMap_append]
      tauto

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
separator yields a node whose children count and key bounds satisfy
`ChildBounded`.  The shape-compatibility hypothesis `hshape` (both siblings are
leaves, or both are internal) is necessary: merging a leaf with an internal
node cannot satisfy the children-count invariant.
-/
lemma mergeNodes_childBounded
    {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hL_cb : ChildBounded (node lKeys lCh)) (hR_cb : ChildBounded (node rKeys rCh))
    (hshape : (lCh = []) ↔ (rCh = []))
    (hL_le : ∀ k ∈ keysOf (node lKeys lCh), k ≤ sep)
    (hR_ge : ∀ k ∈ keysOf (node rKeys rCh), sep ≤ k) :
    ChildBounded (mergeNodes (node lKeys lCh) sep (node rKeys rCh)) := by
  rw [mergeNodes_node]
  unfold ChildBounded at hL_cb hR_cb ⊢
  obtain ⟨hL_rel, hL_bounds, hL_sub⟩ := hL_cb
  obtain ⟨hR_rel, hR_bounds, hR_sub⟩ := hR_cb
  have hL_len : lCh = [] ∨ lCh.length = lKeys.length + 1 := by
    rcases hL_rel with hLe | hLlen
    · left; cases lCh with | nil => rfl | cons x xs => simp at hLe
    · right; exact hLlen
  have hR_len : rCh = [] ∨ rCh.length = rKeys.length + 1 := by
    rcases hR_rel with hRe | hRlen
    · left; cases rCh with | nil => rfl | cons x xs => simp at hRe
    · right; exact hRlen
  refine ⟨?_, ?_, ?_⟩
  · -- component 1: children count
    rcases hL_len with hl | hLlen
    · rcases hR_len with hr | hRlen
      · left; subst hl; subst hr; rfl
      · -- lCh empty, rCh internal: contradicts hshape
        have hr0 : rCh = [] := hshape.mp hl
        subst hl; rw [hr0] at hRlen; simp at hRlen
    · rcases hR_len with hr | hRlen
      · -- lCh internal, rCh empty: contradicts hshape
        have hl0 : lCh = [] := hshape.mpr hr
        subst hr; rw [hl0] at hLlen; simp at hLlen
      · right
        rw [List.length_append, List.length_append, List.length_cons, hLlen, hRlen]
        omega
  · -- component 2: per-child key bounds
    intro i hi
    by_cases hlCh : lCh = []
    · have hrCh : rCh = [] := hshape.mp hlCh
      subst hlCh; subst hrCh; simp at hi
    · have hrCh : rCh ≠ [] := fun h => hlCh (hshape.mpr h)
      have hLlen : lCh.length = lKeys.length + 1 := by
        rcases hL_len with h | h
        · exact absurd h hlCh
        · exact h
      have hRlen : rCh.length = rKeys.length + 1 := by
        rcases hR_len with h | h
        · exact absurd h hrCh
        · exact h
      refine ⟨?_, ?_⟩
      · -- lower bound: mergedKeys[i-1]? bounds child i from below
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · exact Or.inl hi0
        · right
          by_cases hiL : i < lCh.length
          · -- child in the left segment
            have hi1 : i - 1 < lKeys.length := by omega
            have hchild : (lCh ++ rCh).get ⟨i, hi⟩ = lCh.get ⟨i, hiL⟩ :=
              List.getElem_append_left hiL
            have heq : (lKeys ++ sep :: rKeys)[i-1]? = lKeys[i-1]? :=
              List.getElem?_append_left (by omega)
            rw [heq, List.getElem?_eq_getElem hi1]
            have hb := (hL_bounds i hiL).1
            rcases hb with h0 | hb
            · omega
            · simp only [List.getElem?_eq_getElem hi1] at hb
              intro k hk
              rw [hchild] at hk
              exact hb k hk
          · -- child in the right segment
            have hiL' : lCh.length ≤ i := Nat.le_of_not_lt hiL
            have hjlt : i - lCh.length < rCh.length := by
              rw [List.length_append] at hi; omega
            have hchild : (lCh ++ rCh).get ⟨i, hi⟩ = rCh.get ⟨i - lCh.length, hjlt⟩ :=
              List.getElem_append_right hiL'
            have heq : (lKeys ++ sep :: rKeys)[i-1]? = (sep :: rKeys)[i - lCh.length]? := by
              rw [List.getElem?_append_right (by omega : lKeys.length ≤ i - 1)]
              have e : i - 1 - lKeys.length = i - lCh.length := by omega
              rw [e]
            rw [heq]
            rcases Nat.eq_zero_or_pos (i - lCh.length) with hj0 | hjpos
            · -- child is rCh[0]: lower key is the separator
              have h0 : (sep :: rKeys)[i - lCh.length]? = some sep := by simp [hj0]
              rw [h0]
              intro k hk
              rw [hchild] at hk
              have hmem : k ∈ keysOf (node rKeys rCh) := by
                simp only [keysOf, List.mem_append, List.mem_flatMap]
                exact Or.inr ⟨rCh.get ⟨i - lCh.length, hjlt⟩, List.getElem_mem _, hk⟩
              exact hR_ge k hmem
            · -- child is rCh[j], j ≥ 1: lower key is rKeys[j-1]
              have hj1 : i - lCh.length - 1 < rKeys.length := by omega
              have hcons : (sep :: rKeys)[i - lCh.length]? = rKeys[i - lCh.length - 1]? := by
                conv_lhs =>
                  rw [show i - lCh.length = (i - lCh.length - 1) + 1 from by omega]
                exact List.getElem?_cons_succ
              rw [hcons, List.getElem?_eq_getElem hj1]
              have hb := (hR_bounds (i - lCh.length) hjlt).1
              rcases hb with h0 | hb
              · omega
              · simp only [List.getElem?_eq_getElem hj1] at hb
                intro k hk
                rw [hchild] at hk
                exact hb k hk
      · -- upper bound: mergedKeys[i]? bounds child i from above
        by_cases hiL : i < lCh.length
        · -- child in the left segment
          have hchild : (lCh ++ rCh).get ⟨i, hi⟩ = lCh.get ⟨i, hiL⟩ :=
            List.getElem_append_left hiL
          by_cases hiK : i < lKeys.length
          · -- upper key is lKeys[i]
            have heq : (lKeys ++ sep :: rKeys)[i]? = lKeys[i]? :=
              List.getElem?_append_left hiK
            rw [heq, List.getElem?_eq_getElem hiK]
            have hub := (hL_bounds i hiL).2
            simp only [List.getElem?_eq_getElem hiK] at hub
            intro k hk
            rw [hchild] at hk
            exact hub k hk
          · -- child is lCh[lKeys.length]: upper key is the separator
            have hieq : i = lKeys.length := by omega
            have heq : (lKeys ++ sep :: rKeys)[i]? = some sep := by
              rw [hieq, List.getElem?_append_right (Nat.le_refl _)]
              simp
            rw [heq]
            intro k hk
            rw [hchild] at hk
            have hmem : k ∈ keysOf (node lKeys lCh) := by
              simp only [keysOf, List.mem_append, List.mem_flatMap]
              exact Or.inr ⟨lCh.get ⟨i, hiL⟩, List.getElem_mem _, hk⟩
            exact hL_le k hmem
        · -- child in the right segment
          have hiL' : lCh.length ≤ i := Nat.le_of_not_lt hiL
          have hjlt : i - lCh.length < rCh.length := by
            rw [List.length_append] at hi; omega
          have hchild : (lCh ++ rCh).get ⟨i, hi⟩ = rCh.get ⟨i - lCh.length, hjlt⟩ :=
            List.getElem_append_right hiL'
          have heq : (lKeys ++ sep :: rKeys)[i]? = rKeys[i - lCh.length]? := by
            rw [List.getElem?_append_right (by omega : lKeys.length ≤ i)]
            conv_lhs =>
              rw [show i - lKeys.length = (i - lCh.length) + 1 from by omega]
            exact List.getElem?_cons_succ
          rw [heq]
          by_cases hjK : i - lCh.length < rKeys.length
          · -- upper key is rKeys[j]
            rw [List.getElem?_eq_getElem hjK]
            have hub := (hR_bounds (i - lCh.length) hjlt).2
            simp only [List.getElem?_eq_getElem hjK] at hub
            intro k hk
            rw [hchild] at hk
            exact hub k hk
          · -- child is rCh[rKeys.length]: no upper key
            have hnone : rKeys[i - lCh.length]? = none :=
              List.getElem?_eq_none (by omega)
            rw [hnone]
            exact trivial
  · -- component 3: recursive ChildBounded on children
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_sub c hc
    · exact hR_sub c hc
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

/-! ## Structural preservation architecture

The raw operation may leave an empty root containing one child, so the
mathematically correct root postcondition is {lit}`RootDeleteResult`, not raw
{lit}`WellFormed`.  Local rotation and merge facts are packaged in
{lit}`Repair`, then lifted through parent contexts by the reassembly modules.
{lit}`ComposedPreservation` performs one induction over every executable
branch and exposes non-root and raw-root results.  Finally,
{lit}`WellFormed` proves that {lit}`composedDeleteRoot` contracts the permitted
transient and restores genuine root well-formedness.
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

/-! ## `rotateLeft`: borrow a key from the left sibling (CLRS case 3a, symmetric) -/

/--
**Borrow from the left sibling (CLRS `B-TREE-DELETE` case 3a, symmetric to
`rotateRight`).**  The underflowing right child receives the separator `sep`
as a new first key and the left sibling's last child; the left sibling's last
key rises to become the new separator.  Returns `(newLeft, newSep, newRight)`.
-/
def rotateLeft : BTree → Nat → BTree → BTree × Nat × BTree
  | node lKeys lCh, sep, node rKeys rCh =>
    match lKeys with
    | [] => (node lKeys lCh, sep, node rKeys rCh)
    | lHead :: lTail =>
        (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1)),
         (lHead :: lTail).getLast (List.cons_ne_nil _ _),
         node (sep :: rKeys) ((lCh.drop (lCh.length - 1)) ++ rCh))

/-- `rotateLeft` reduces on a left sibling with no keys (identity case). -/
@[simp] lemma rotateLeft_nil (rKeys : List Nat) (lCh rCh : List BTree) (sep : Nat) :
    rotateLeft (node [] lCh) sep (node rKeys rCh) = (node [] lCh, sep, node rKeys rCh) := rfl

/-- `rotateLeft` reduces on a left sibling with at least one key. -/
@[simp] lemma rotateLeft_cons (lHead : Nat) (lTail rKeys : List Nat)
    (lCh rCh : List BTree) (sep : Nat) :
    rotateLeft (node (lHead :: lTail) lCh) sep (node rKeys rCh) =
      (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1)),
       (lHead :: lTail).getLast (List.cons_ne_nil _ _),
       node (sep :: rKeys) ((lCh.drop (lCh.length - 1)) ++ rCh)) := rfl

/--
**`rotateLeft` new-left node is well formed.**  After the borrow, the left
sibling has one fewer key (still at least `t - 1`) and preserves `SameDepth`
and its height.  Mirrors `rotateRight_right`.
-/
lemma rotateLeft_left {t : Nat} (ht : 2 ≤ t)
    {lHead : Nat} {lTail : List Nat} {lCh : List BTree}
    (hllen : t ≤ (lHead :: lTail).length)
    (hL_cb : ChildBounded (node (lHead :: lTail) lCh))
    (hL_occ : Occupancy t false (node (lHead :: lTail) lCh))
    (hL : SameDepth (node (lHead :: lTail) lCh)) :
    Occupancy t false (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) ∧
    SameDepth (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) ∧
    heightOf (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) =
      heightOf (node (lHead :: lTail) lCh) := by
  obtain ⟨_, hL_up, _, hL_sub⟩ := occupancy_false_dest hL_occ
  have hkeys_len : (lHead :: lTail).dropLast.length = lTail.length := by
    rw [List.length_dropLast, List.length_cons]; omega
  have hltail_lo : t - 1 ≤ lTail.length := by
    simp only [List.length_cons] at hllen; omega
  have hltail_up : lTail.length ≤ 2 * t - 1 := by
    simp only [List.length_cons] at hL_up; omega
  by_cases hlc : lCh = []
  · -- left sibling is a leaf: no child moves
    subst hlc
    simp only [List.take_nil]
    refine ⟨occupancy_false_intro (by rw [hkeys_len]; omega) (by rw [hkeys_len]; omega)
        (Or.inl rfl) (by intro c hc; simp at hc), SameDepth.leaf _, ?_⟩
    simp [heightOf]
  · -- internal: the last child rotates over
    obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, lCh = c0 :: cs := by
      cases lCh with
      | nil => exact absurd rfl hlc
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hchlen : (c0 :: cs).length = (lHead :: lTail).length + 1 := by
      rcases childBounded_children_rel hL_cb with h | h
      · exact absurd h (by simp)
      · exact h
    have htake_len : ((c0 :: cs).take ((c0 :: cs).length - 1)).length =
        (c0 :: cs).length - 1 := by
      rw [List.length_take]; omega
    have htake_ne : (c0 :: cs).take ((c0 :: cs).length - 1) ≠ [] := by
      intro h
      rw [h] at htake_len
      simp only [List.length_nil] at htake_len
      omega
    obtain ⟨d0, ds, htd⟩ : ∃ d0 ds, (c0 :: cs).take ((c0 :: cs).length - 1) =
        d0 :: ds := by
      cases h : (c0 :: cs).take ((c0 :: cs).length - 1) with
      | nil => exact absurd h htake_ne
      | cons d0 ds => exact ⟨d0, ds, rfl⟩
    have hmem_take : ∀ c ∈ (c0 :: cs).take ((c0 :: cs).length - 1), c ∈ (c0 :: cs) :=
      fun c hc => List.mem_of_mem_take hc
    have htake_len' : ((c0 :: cs).take ((c0 :: cs).length - 1)).length =
        lTail.length + 1 := by
      rw [htake_len, hchlen]; simp only [List.length_cons]; omega
    rw [htd]
    have hd0_mem : d0 ∈ (c0 :: cs) := hmem_take d0 (by rw [htd]; simp)
    have huniform : ∀ c ∈ (d0 :: ds), heightOf c = heightOf d0 := by
      intro c hc
      have hc' : c ∈ (c0 :: cs) := hmem_take c (by rw [htd]; exact hc)
      exact sameDepth_children_eq_height hL c hc' d0 hd0_mem
    have hsd_all : ∀ c ∈ (d0 :: ds), SameDepth c := by
      intro c hc
      exact sameDepth_children_sd hL c (hmem_take c (by rw [htd]; exact hc))
    have huniform_ds : ∀ c ∈ ds, heightOf c = heightOf d0 :=
      fun c hc => huniform c (List.mem_cons_of_mem d0 hc)
    have hd0c0 : heightOf d0 = heightOf c0 :=
      sameDepth_children_eq_height hL d0 hd0_mem c0 (by simp)
    have hchild_len : (d0 :: ds).length = lTail.length + 1 := by
      rw [← htd]; exact htake_len'
    refine ⟨?_, ?_, ?_⟩
    · -- occupancy: lTail.length keys, lTail.length + 1 children
      refine occupancy_false_intro (by rw [hkeys_len]; omega) (by rw [hkeys_len]; omega)
        (Or.inr ?_) ?_
      · rw [hchild_len]; exact ⟨by omega, by omega⟩
      · intro c hc
        exact hL_sub c (hmem_take c (by rw [htd]; exact hc))
    · exact sameDepth_of_uniform (H := heightOf d0) huniform hsd_all
    · rw [heightOf_uniform_children huniform_ds, heightOf_internal_of_sameDepth hL, hd0c0]

/--
**`rotateLeft` new-right node is well formed.**  After borrowing, the repaired
right child has exactly `t` keys — above the minimum — and preserves
`SameDepth` and its height.  The equal-height hypothesis is supplied by the
parent's `SameDepth` invariant.  Mirrors `rotateRight_left`.
-/
lemma rotateLeft_right {t : Nat} (ht : 2 ≤ t)
    {lKeys rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hrk : rKeys.length = t - 1)
    (hR_cb : ChildBounded (node rKeys rCh))
    (hL : SameDepth (node lKeys lCh)) (hR : SameDepth (node rKeys rCh))
    (hL_occ : Occupancy t false (node lKeys lCh))
    (hR_occ : Occupancy t false (node rKeys rCh))
    (hht : heightOf (node lKeys lCh) = heightOf (node rKeys rCh)) :
    Occupancy t false (node (sep :: rKeys) ((lCh.drop (lCh.length - 1)) ++ rCh)) ∧
    SameDepth (node (sep :: rKeys) ((lCh.drop (lCh.length - 1)) ++ rCh)) ∧
    heightOf (node (sep :: rKeys) ((lCh.drop (lCh.length - 1)) ++ rCh)) =
      heightOf (node rKeys rCh) := by
  obtain ⟨_, _, _, hL_sub⟩ := occupancy_false_dest hL_occ
  obtain ⟨_, _, _, hR_sub⟩ := occupancy_false_dest hR_occ
  have hkeys_len : (sep :: rKeys).length = t := by
    simp only [List.length_cons, hrk]; omega
  by_cases hrc : rCh = []
  · -- both siblings are leaves: no child moves
    have hlc : lCh = [] := (leaf_iff_of_height_eq hht).mpr hrc
    subst hlc; subst hrc
    simp only [List.drop_nil, List.nil_append]
    refine ⟨?_, SameDepth.leaf _, ?_⟩
    · exact occupancy_false_intro (by rw [hkeys_len]; omega) (by rw [hkeys_len]; omega)
        (Or.inl rfl) (by intro c hc; simp at hc)
    · simp [heightOf]
  · -- both internal: one child rotates over
    obtain ⟨b, bs, rfl⟩ : ∃ b bs, rCh = b :: bs := by
      cases rCh with
      | nil => exact absurd rfl hrc
      | cons b bs => exact ⟨b, bs, rfl⟩
    have hlc_ne : lCh ≠ [] := fun h => hrc ((leaf_iff_of_height_eq hht).mp h)
    obtain ⟨a, as, rfl⟩ : ∃ a as, lCh = a :: as := by
      cases lCh with
      | nil => exact absurd rfl hlc_ne
      | cons a as => exact ⟨a, as, rfl⟩
    have hdrop_len : ((a :: as).drop ((a :: as).length - 1)).length = 1 := by
      rw [List.length_drop]
      have hpos : 0 < (a :: as).length := Nat.zero_lt_succ _
      omega
    have hdrop_ne : (a :: as).drop ((a :: as).length - 1) ≠ [] := by
      intro h; rw [h] at hdrop_len; simp at hdrop_len
    obtain ⟨d0, ds, hdd⟩ : ∃ d0 ds, (a :: as).drop ((a :: as).length - 1) =
        d0 :: ds := by
      cases h : (a :: as).drop ((a :: as).length - 1) with
      | nil => exact absurd h hdrop_ne
      | cons d0 ds => exact ⟨d0, ds, rfl⟩
    have hrlen : (b :: bs).length = t := by
      rcases childBounded_len_of_keys (by omega) hR_cb hrk with h | h
      · exact absurd h (by simp)
      · exact h
    have hchildren_len : (((a :: as).drop ((a :: as).length - 1)) ++ (b :: bs)).length =
        t + 1 := by
      rw [List.length_append, hdrop_len, hrlen]; omega
    have hmem_drop : ∀ c ∈ (a :: as).drop ((a :: as).length - 1), c ∈ (a :: as) :=
      fun c hc => List.mem_of_mem_drop hc
    have hd0_mem : d0 ∈ (a :: as) := hmem_drop d0 (by rw [hdd]; simp)
    have hab : heightOf a = heightOf b :=
      child_height_bridge hL hR hht (c := a) (d := b) (by simp) (by simp)
    have hd0b : heightOf d0 = heightOf b :=
      (sameDepth_children_eq_height hL d0 hd0_mem a (by simp)).trans hab
    have huniform : ∀ c ∈ ((a :: as).drop ((a :: as).length - 1) ++ (b :: bs)),
        heightOf c = heightOf b := by
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact (sameDepth_children_eq_height hL c (hmem_drop c hc) a (by simp)).trans hab
      · exact sameDepth_children_eq_height hR c hc b (by simp)
    have hsd_all : ∀ c ∈ ((a :: as).drop ((a :: as).length - 1) ++ (b :: bs)),
        SameDepth c := by
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc
      · exact sameDepth_children_sd hL c (hmem_drop c hc)
      · exact sameDepth_children_sd hR c hc
    have hcons : (a :: as).drop ((a :: as).length - 1) ++ (b :: bs) =
        d0 :: (ds ++ (b :: bs)) := by
      rw [hdd, List.cons_append]
    rw [hcons]
    -- heights: every element of the new children list has height `heightOf b`
    have huniform_tail : ∀ c ∈ (ds ++ (b :: bs)), heightOf c = heightOf d0 := by
      intro c hc
      have hb2 : heightOf c = heightOf b :=
        huniform c (by rw [hcons]; exact List.mem_cons_of_mem d0 hc)
      rw [hb2, ← hd0b]
    refine ⟨?_, ?_, ?_⟩
    · -- occupancy: t keys, t + 1 children
      refine occupancy_false_intro (by rw [hkeys_len]; omega) (by rw [hkeys_len]; omega)
        (Or.inr ?_) ?_
      · have hcl : (d0 :: (ds ++ (b :: bs))).length = t + 1 := by
          rw [← hcons]; exact hchildren_len
        rw [hcl]; exact ⟨by omega, by omega⟩
      · intro c hc
        rw [← hcons] at hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hL_sub c (hmem_drop c hc)
        · exact hR_sub c hc
    · exact sameDepth_of_uniform (H := heightOf b) (by rw [← hcons]; exact huniform)
        (by rw [← hcons]; exact hsd_all)
    · rw [heightOf_uniform_children huniform_tail, heightOf_internal_of_sameDepth hR, hd0b]

/-! ## `keysOf` membership across rotations -/

/-- `rotateRight` reduces on a right sibling with no keys (identity case). -/
@[simp] lemma rotateRight_nil (lKeys : List Nat) (lCh rCh : List BTree) (sep : Nat) :
    rotateRight (node lKeys lCh) sep (node [] rCh) = (node lKeys lCh, sep, node [] rCh) := rfl

/--
**Membership across `rotateRight`.**  Borrowing from the right sibling neither
creates nor destroys keys: the keys of the two produced nodes plus the new
separator are exactly the keys of the original nodes plus the old separator.
-/
lemma mem_keysOf_rotateRight (l : BTree) (sep : Nat) (r : BTree) (k : Nat) :
    k ∈ keysOf (rotateRight l sep r).1 ∨ k = (rotateRight l sep r).2.1 ∨
      k ∈ keysOf (rotateRight l sep r).2.2 ↔
    k ∈ keysOf l ∨ k = sep ∨ k ∈ keysOf r := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases rKeys with
      | nil =>
        rw [rotateRight_nil]
      | cons rHead rTail =>
        have hbridge : k ∈ rCh.flatMap keysOf ↔
            k ∈ (rCh.take 1).flatMap keysOf ∨ k ∈ (rCh.drop 1).flatMap keysOf := by
          conv_lhs => rw [← List.take_append_drop 1 rCh]
          rw [List.flatMap_append, List.mem_append]
        rw [rotateRight_cons]
        show k ∈ keysOf (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) ∨ k = rHead ∨
              k ∈ keysOf (node rTail (rCh.drop 1)) ↔
            k ∈ keysOf (node lKeys lCh) ∨ k = sep ∨ k ∈ keysOf (node (rHead :: rTail) rCh)
        simp only [keysOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.flatMap_append]
        rw [hbridge]
        tauto

/--
**Membership across `rotateLeft`.**  Borrowing from the left sibling neither
creates nor destroys keys: the keys of the two produced nodes plus the new
separator are exactly the keys of the original nodes plus the old separator.
-/
lemma mem_keysOf_rotateLeft (l : BTree) (sep : Nat) (r : BTree) (k : Nat) :
    k ∈ keysOf (rotateLeft l sep r).1 ∨ k = (rotateLeft l sep r).2.1 ∨
      k ∈ keysOf (rotateLeft l sep r).2.2 ↔
    k ∈ keysOf l ∨ k = sep ∨ k ∈ keysOf r := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases lKeys with
      | nil =>
        rw [rotateLeft_nil]
      | cons lHead lTail =>
        have hb1 : (k = lHead ∨ k ∈ lTail) ↔ k ∈ (lHead :: lTail).dropLast ∨
            k = (lHead :: lTail).getLast (List.cons_ne_nil _ _) := by
          have h : k ∈ (lHead :: lTail) ↔ k ∈ (lHead :: lTail).dropLast ∨
              k = (lHead :: lTail).getLast (List.cons_ne_nil _ _) := by
            conv_lhs => rw [← List.dropLast_append_getLast (List.cons_ne_nil lHead lTail)]
            rw [List.mem_append, List.mem_singleton]
          rwa [List.mem_cons] at h
        have hb2 : k ∈ lCh.flatMap keysOf ↔
            k ∈ (lCh.take (lCh.length - 1)).flatMap keysOf ∨
              k ∈ (lCh.drop (lCh.length - 1)).flatMap keysOf := by
          conv_lhs => rw [← List.take_append_drop (lCh.length - 1) lCh]
          rw [List.flatMap_append, List.mem_append]
        rw [rotateLeft_cons]
        show k ∈ keysOf (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) ∨
              k = (lHead :: lTail).getLast (List.cons_ne_nil lHead lTail) ∨
              k ∈ keysOf (node (sep :: rKeys) ((lCh.drop (lCh.length - 1)) ++ rCh)) ↔
            k ∈ keysOf (node (lHead :: lTail) lCh) ∨ k = sep ∨
              k ∈ keysOf (node rKeys rCh)
        simp only [keysOf, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
          List.flatMap_append]
        rw [hb1, hb2]
        tauto


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

/-! ## Unconditional height bounds for rotations (termination of `composedDelete`) -/

/--
**{lit}`rotateRight` repaired-left height bound (unconditional).**  The new
left node's children are drawn from {lit}`lCh` and {lit}`rCh.take 1`, both
sub-lists of {lit}`lCh ++ rCh`, so its height is at most the maximum of the
two input heights.  No invariant hypotheses are needed, which is what makes
the lemma usable in {lit}`decreasing_by`.
-/
lemma heightOf_rotateRight_left_le (l : BTree) (sep : Nat) (r : BTree) :
    heightOf (rotateRight l sep r).1 ≤ max (heightOf l) (heightOf r) := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases rKeys with
      | nil =>
        rw [rotateRight_nil]
        exact Nat.le_max_left _ _
      | cons rHead rTail =>
        rw [rotateRight_cons]
        show heightOf (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) ≤ _
        have hsub : lCh ++ rCh.take 1 ⊆ lCh ++ rCh := by
          intro c hc
          rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact List.mem_append_left _ hc
          · exact List.mem_append_right _ (List.take_subset 1 rCh hc)
        have hle : heightOf (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) ≤
            heightOf (node (lKeys ++ sep :: rHead :: rTail) (lCh ++ rCh)) :=
          heightOf_le_of_children_subset hsub
        have hmax : heightOf (node (lKeys ++ sep :: rHead :: rTail) (lCh ++ rCh)) =
            max (heightOf (node lKeys lCh)) (heightOf (node (rHead :: rTail) rCh)) := by
          rw [← mergeNodes_node, heightOf_mergeNodes_eq_max]
        exact le_trans hle (le_of_eq hmax)

/--
**{lit}`rotateRight` trimmed-right height bound (unconditional).**  The new
right node's children are {lit}`rCh.drop 1 ⊆ rCh`.
-/
lemma heightOf_rotateRight_right_le (l : BTree) (sep : Nat) (r : BTree) :
    heightOf (rotateRight l sep r).2.2 ≤ max (heightOf l) (heightOf r) := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases rKeys with
      | nil =>
        rw [rotateRight_nil]
        exact Nat.le_max_right _ _
      | cons rHead rTail =>
        rw [rotateRight_cons]
        show heightOf (node rTail (rCh.drop 1)) ≤ _
        exact le_trans (heightOf_le_of_children_subset (List.drop_subset 1 rCh))
          (Nat.le_max_right _ _)

/--
**{lit}`rotateLeft` trimmed-left height bound (unconditional).**  The new left
node's children are {lit}`lCh.take (lCh.length - 1) ⊆ lCh`.
-/
lemma heightOf_rotateLeft_left_le (l : BTree) (sep : Nat) (r : BTree) :
    heightOf (rotateLeft l sep r).1 ≤ max (heightOf l) (heightOf r) := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases lKeys with
      | nil =>
        rw [rotateLeft_nil]
        exact Nat.le_max_left _ _
      | cons lHead lTail =>
        rw [rotateLeft_cons]
        show heightOf (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) ≤ _
        exact le_trans (heightOf_le_of_children_subset (List.take_subset _ lCh))
          (Nat.le_max_left _ _)

/--
**{lit}`rotateLeft` repaired-right height bound (unconditional).**  The new
right node's children are drawn from {lit}`lCh.drop (lCh.length - 1)` and
{lit}`rCh`, both sub-lists of {lit}`lCh ++ rCh`.  Mirrors
{lit}`heightOf_rotateRight_left_le`.
-/
lemma heightOf_rotateLeft_right_le (l : BTree) (sep : Nat) (r : BTree) :
    heightOf (rotateLeft l sep r).2.2 ≤ max (heightOf l) (heightOf r) := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases lKeys with
      | nil =>
        rw [rotateLeft_nil]
        exact Nat.le_max_right _ _
      | cons lHead lTail =>
        rw [rotateLeft_cons]
        show heightOf (node (sep :: rKeys) (lCh.drop (lCh.length - 1) ++ rCh)) ≤ _
        have hsub : lCh.drop (lCh.length - 1) ++ rCh ⊆ lCh ++ rCh := by
          intro c hc
          rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact List.mem_append_left _ (List.drop_subset _ lCh hc)
          · exact List.mem_append_right _ hc
        have hle : heightOf (node (sep :: rKeys) (lCh.drop (lCh.length - 1) ++ rCh)) ≤
            heightOf (node (lHead :: lTail ++ sep :: rKeys) (lCh ++ rCh)) :=
          heightOf_le_of_children_subset hsub
        have hmax : heightOf (node (lHead :: lTail ++ sep :: rKeys) (lCh ++ rCh)) =
            max (heightOf (node (lHead :: lTail) lCh)) (heightOf (node rKeys rCh)) := by
          rw [← mergeNodes_node, heightOf_mergeNodes_eq_max]
        exact le_trans hle (le_of_eq hmax)

/-! ## `maxKey` / `minKey`: rightmost / leftmost key read -/

/-- `BTree` default inhabitant, used by `getLast!` / `head!` spine descent. -/
instance : Inhabited BTree := ⟨node [] []⟩

/-- Bridge from the defaulting `getLast!` to the hypothesis-carrying `getLast`. -/
lemma getLast!_eq_getLast {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.getLast! = l.getLast h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- Bridge from the defaulting `head!` to the hypothesis-carrying `head`. -/
lemma head!_eq_head {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.head! = l.head h := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

lemma getLast!_mem {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.getLast! ∈ l := by
  rw [getLast!_eq_getLast h]; exact List.getLast_mem h

lemma head!_mem {α : Type*} [Inhabited α] {l : List α} (h : l ≠ []) :
    l.head! ∈ l := by
  rw [head!_eq_head h]; exact List.head_mem h

lemma getLast!_eq_getElem {α : Type*} [Inhabited α] {l : List α} (h : 0 < l.length) :
    l.getLast! = l[l.length - 1] := by
  have hne : l ≠ [] := by intro he; rw [he] at h; simp at h
  rw [getLast!_eq_getLast hne]; exact List.getLast_eq_getElem hne

lemma head!_eq_getElem {α : Type*} [Inhabited α] {l : List α} (h : 0 < l.length) :
    l.head! = l[0] := by
  cases l with
  | nil => simp at h
  | cons a as => rfl

/-- In a sorted (`≤`-pairwise) nonempty list, every element is below the last one. -/
lemma le_getLast!_of_pairwise {l : List Nat} (hp : l.Pairwise (· ≤ ·)) (hne : 0 < l.length)
    {k : Nat} (hk : k ∈ l) : k ≤ l.getLast! := by
  rw [getLast!_eq_getElem hne]
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
  exact pairwise_get_mono hp (by omega) hj (by omega)

/-- In a sorted (`≤`-pairwise) nonempty list, the first element is below every element. -/
lemma head!_le_of_pairwise {l : List Nat} (hp : l.Pairwise (· ≤ ·)) (hne : 0 < l.length)
    {k : Nat} (hk : k ∈ l) : l.head! ≤ k := by
  rw [head!_eq_getElem hne]
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hk
  exact pairwise_get_mono hp (Nat.zero_le j) hne hj

/-- Hereditary key-nonemptiness: every node of the tree has at least one key. -/
def AllKeysPos : BTree → Prop
  | node ks cs => 0 < ks.length ∧ ∀ c ∈ cs, AllKeysPos c

/-- Rightmost key of a B-tree: the last key of a leaf, else descend the last child. -/
def maxKey : BTree → Nat
  | node ks cs => if _h : cs.isEmpty then ks.getLast! else maxKey (cs.getLast!)
termination_by tr => heightOf tr
decreasing_by
  have hne : cs ≠ [] := by
    intro he; subst he; simp at _h
  exact heightOf_mem_lt (getLast!_mem hne)

/-- Leftmost key of a B-tree: the first key of a leaf, else descend the first child. -/
def minKey : BTree → Nat
  | node ks cs => if _h : cs.isEmpty then ks.head! else minKey (cs.head!)
termination_by tr => heightOf tr
decreasing_by
  have hne : cs ≠ [] := by
    intro he; subst he; simp at _h
  exact heightOf_mem_lt (head!_mem hne)

@[simp] lemma maxKey_leaf (ks : List Nat) : maxKey (node ks []) = ks.getLast! := by
  simp [maxKey]

lemma maxKey_internal {ks : List Nat} {cs : List BTree} (h : cs.isEmpty = false) :
    maxKey (node ks cs) = maxKey (cs.getLast!) := by
  simp [maxKey, h]

@[simp] lemma minKey_leaf (ks : List Nat) : minKey (node ks []) = ks.head! := by
  simp [minKey]

lemma minKey_internal {ks : List Nat} {cs : List BTree} (h : cs.isEmpty = false) :
    minKey (node ks cs) = minKey (cs.head!) := by
  simp [minKey, h]

/-- The rightmost key of a tree with nonempty keys everywhere is a key of the tree. -/
theorem maxKey_mem (tr : BTree) (hne : AllKeysPos tr) : maxKey tr ∈ keysOf tr := by
  let motive (n : Nat) : Prop :=
    ∀ (tr' : BTree), heightOf tr' = n → AllKeysPos tr' → maxKey tr' ∈ keysOf tr'
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ihn tr' hn hne'
    cases tr' with
    | node ks cs =>
      unfold AllKeysPos at hne'
      obtain ⟨hks, hcs⟩ := hne'
      by_cases hce : cs.isEmpty
      · have hcs' : cs = [] := List.isEmpty_iff.mp hce
        subst hcs'
        rw [maxKey_leaf]
        have hks' : ks ≠ [] := by intro he; rw [he] at hks; simp at hks
        simp only [keysOf, List.flatMap_nil, List.append_nil]
        exact getLast!_mem hks'
      · have hne'' : cs ≠ [] := by intro he; subst he; simp at hce
        have hmem : cs.getLast! ∈ cs := getLast!_mem hne''
        have hfalse : cs.isEmpty = false := by simpa using hce
        rw [maxKey_internal hfalse]
        have hlt : heightOf (cs.getLast!) < n := by
          calc heightOf (cs.getLast!) < heightOf (node ks cs) := heightOf_mem_lt hmem
            _ = n := hn
        have hrec := ihn _ hlt _ rfl (hcs _ hmem)
        simp only [keysOf, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨_, hmem, hrec⟩)
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hne

/-- The leftmost key of a tree with nonempty keys everywhere is a key of the tree. -/
theorem minKey_mem (tr : BTree) (hne : AllKeysPos tr) : minKey tr ∈ keysOf tr := by
  let motive (n : Nat) : Prop :=
    ∀ (tr' : BTree), heightOf tr' = n → AllKeysPos tr' → minKey tr' ∈ keysOf tr'
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ihn tr' hn hne'
    cases tr' with
    | node ks cs =>
      unfold AllKeysPos at hne'
      obtain ⟨hks, hcs⟩ := hne'
      by_cases hce : cs.isEmpty
      · have hcs' : cs = [] := List.isEmpty_iff.mp hce
        subst hcs'
        rw [minKey_leaf]
        have hks' : ks ≠ [] := by intro he; rw [he] at hks; simp at hks
        simp only [keysOf, List.flatMap_nil, List.append_nil]
        exact head!_mem hks'
      · have hne'' : cs ≠ [] := by intro he; subst he; simp at hce
        have hmem : cs.head! ∈ cs := head!_mem hne''
        have hfalse : cs.isEmpty = false := by simpa using hce
        rw [minKey_internal hfalse]
        have hlt : heightOf (cs.head!) < n := by
          calc heightOf (cs.head!) < heightOf (node ks cs) := heightOf_mem_lt hmem
            _ = n := hn
        have hrec := ihn _ hlt _ rfl (hcs _ hmem)
        simp only [keysOf, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨_, hmem, hrec⟩)
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hne

/-- Every key of a sorted, child-bounded tree with nonempty keys everywhere is at
most the rightmost key. -/
theorem maxKey_ge (tr : BTree) (hs : Sorted tr) (hcb : ChildBounded tr)
    (hne : AllKeysPos tr) : ∀ k ∈ keysOf tr, k ≤ maxKey tr := by
  let motive (n : Nat) : Prop :=
    ∀ (tr' : BTree), heightOf tr' = n → Sorted tr' → ChildBounded tr' → AllKeysPos tr' →
      ∀ k ∈ keysOf tr', k ≤ maxKey tr'
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ihn tr' hn hs hcb hne'
    cases tr' with
    | node ks cs =>
      unfold Sorted at hs
      unfold ChildBounded at hcb
      unfold AllKeysPos at hne'
      obtain ⟨hpw, hsC⟩ := hs
      obtain ⟨hrel, hbound, hcbC⟩ := hcb
      obtain ⟨hks, hneC⟩ := hne'
      intro k hk
      by_cases hce : cs.isEmpty
      · have hcs' : cs = [] := List.isEmpty_iff.mp hce
        subst hcs'
        rw [maxKey_leaf]
        simp only [keysOf, List.flatMap_nil, List.append_nil] at hk
        exact le_getLast!_of_pairwise hpw hks hk
      · have hne'' : cs ≠ [] := by intro he; subst he; simp at hce
        have hfalse : cs.isEmpty = false := by simpa using hce
        rw [maxKey_internal hfalse]
        have hlen : cs.length = ks.length + 1 := by
          rcases hrel with hemp | hlen
          · exact absurd (List.isEmpty_iff.mp hemp) hne''
          · exact hlen
        set len := ks.length with hlen_eq
        have hcs_pos : 0 < cs.length := by omega
        have hin : len < cs.length := by omega
        have hlast_mem : cs.getLast! ∈ cs := getLast!_mem hne''
        -- `cs.getLast!` is the child at index `len = cs.length - 1`.
        have hlast_eq : cs.getLast! = cs[len]'hin := by
          rw [getLast!_eq_getElem hcs_pos]
          congr 1
          omega
        -- The last separator key is a lower bound for the last child's keys.
        have hlast_key : ks.getLast! ≤ maxKey (cs.getLast!) := by
          have hkn1 : len - 1 < ks.length := by omega
          have hlow := (hbound len hin).1
          rw [List.getElem?_eq_getElem hkn1] at hlow
          rcases hlow with h0 | hb
          · omega
          · have hb' : ∀ k' ∈ keysOf (cs[len]'hin), ks[len - 1]'hkn1 ≤ k' := hb
            rw [← hlast_eq] at hb'
            have hmemmax : maxKey (cs.getLast!) ∈ keysOf (cs.getLast!) :=
              maxKey_mem _ (hneC _ hlast_mem)
            have hle := hb' _ hmemmax
            have hgoal : ks.getLast! = ks[len - 1]'hkn1 := by
              rw [getLast!_eq_getElem hks]
            rw [hgoal]
            exact hle
        simp only [keysOf, List.mem_append] at hk
        rcases hk with hkk | hkc
        · exact le_trans (le_getLast!_of_pairwise hpw hks hkk) hlast_key
        · obtain ⟨c, hc, hkc'⟩ := List.mem_flatMap.mp hkc
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
          by_cases hjn : j = len
          · -- Key in the last child: induction hypothesis.
            subst hjn
            rw [hlast_eq]
            have hlt : heightOf (cs[len]'hj) < n := by
              calc heightOf (cs[len]'hj) < heightOf (node ks cs) := heightOf_mem_lt hc
                _ = n := hn
            exact ihn _ hlt _ rfl (hsC _ hc) (hcbC _ hc) (hneC _ hc) k hkc'
          · -- Key in an earlier child: bounded above by `ks[j] ≤ ks.getLast!`.
            have hjk : j < ks.length := by omega
            have hup := (hbound j hj).2
            rw [List.getElem?_eq_getElem hjk] at hup
            have hup' : ∀ k' ∈ keysOf (cs[j]'hj), k' ≤ ks[j]'hjk := hup
            have hk_le := hup' k hkc'
            have hkj_mem : ks[j]'hjk ∈ ks := List.getElem_mem hjk
            exact le_trans (le_trans hk_le (le_getLast!_of_pairwise hpw hks hkj_mem)) hlast_key
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hs hcb hne

/-- Every key of a sorted, child-bounded tree with nonempty keys everywhere is at
least the leftmost key. -/
theorem minKey_le (tr : BTree) (hs : Sorted tr) (hcb : ChildBounded tr)
    (hne : AllKeysPos tr) : ∀ k ∈ keysOf tr, minKey tr ≤ k := by
  let motive (n : Nat) : Prop :=
    ∀ (tr' : BTree), heightOf tr' = n → Sorted tr' → ChildBounded tr' → AllKeysPos tr' →
      ∀ k ∈ keysOf tr', minKey tr' ≤ k
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ihn tr' hn hs hcb hne'
    cases tr' with
    | node ks cs =>
      unfold Sorted at hs
      unfold ChildBounded at hcb
      unfold AllKeysPos at hne'
      obtain ⟨hpw, hsC⟩ := hs
      obtain ⟨hrel, hbound, hcbC⟩ := hcb
      obtain ⟨hks, hneC⟩ := hne'
      intro k hk
      by_cases hce : cs.isEmpty
      · have hcs' : cs = [] := List.isEmpty_iff.mp hce
        subst hcs'
        rw [minKey_leaf]
        simp only [keysOf, List.flatMap_nil, List.append_nil] at hk
        exact head!_le_of_pairwise hpw hks hk
      · have hne'' : cs ≠ [] := by intro he; subst he; simp at hce
        have hfalse : cs.isEmpty = false := by simpa using hce
        rw [minKey_internal hfalse]
        have hlen : cs.length = ks.length + 1 := by
          rcases hrel with hemp | hlen
          · exact absurd (List.isEmpty_iff.mp hemp) hne''
          · exact hlen
        set len := ks.length with hlen_eq
        have hcs_pos : 0 < cs.length := by omega
        have hhead_mem : cs.head! ∈ cs := head!_mem hne''
        -- `cs.head!` is the child at index `0`.
        have hhead_eq : cs.head! = cs[0]'hcs_pos := head!_eq_getElem hcs_pos
        -- The first key is an upper bound for the first child's keys.
        have hfirst_key : minKey (cs.head!) ≤ ks.head! := by
          have hup := (hbound 0 hcs_pos).2
          rw [List.getElem?_eq_getElem hks] at hup
          have hup' : ∀ k' ∈ keysOf (cs[0]'hcs_pos), k' ≤ ks[0]'hks := hup
          rw [← hhead_eq] at hup'
          have hmemmin : minKey (cs.head!) ∈ keysOf (cs.head!) :=
            minKey_mem _ (hneC _ hhead_mem)
          have hle := hup' _ hmemmin
          rw [head!_eq_getElem hks]
          exact hle
        simp only [keysOf, List.mem_append] at hk
        rcases hk with hkk | hkc
        · exact le_trans hfirst_key (head!_le_of_pairwise hpw hks hkk)
        · obtain ⟨c, hc, hkc'⟩ := List.mem_flatMap.mp hkc
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
          by_cases hj0 : j = 0
          · -- Key in the first child: induction hypothesis.
            subst hj0
            rw [hhead_eq]
            have hlt : heightOf (cs[0]'hj) < n := by
              calc heightOf (cs[0]'hj) < heightOf (node ks cs) := heightOf_mem_lt hc
                _ = n := hn
            exact ihn _ hlt _ rfl (hsC _ hc) (hcbC _ hc) (hneC _ hc) k hkc'
          · -- Key in a later child: bounded below by `ks.head! ≤ ks[j-1] ≤ k`.
            have hjm1 : j - 1 < ks.length := by omega
            have hlow := (hbound j hj).1
            rw [List.getElem?_eq_getElem hjm1] at hlow
            rcases hlow with h0' | hb
            · omega
            · have hb' : ∀ k' ∈ keysOf (cs[j]'hj), ks[j - 1]'hjm1 ≤ k' := hb
              have hk_ge := hb' k hkc'
              have hjm1_mem : ks[j - 1]'hjm1 ∈ ks := List.getElem_mem hjm1
              exact le_trans (le_trans hfirst_key (head!_le_of_pairwise hpw hks hjm1_mem)) hk_ge
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl hs hcb hne

/-! ## {lit}`AllKeysPos` from {lit}`Occupancy`, and preservation across merge/rotations -/

/--
**Occupancy implies hereditary key-nonemptiness.**  Any tree satisfying
{lit}`Occupancy` whose root has at least one key has at least one key in every
node: non-root nodes carry at least {lit}`t - 1 ≥ 1` keys.  The root
nonemptiness hypothesis is needed because {lit}`Occupancy` allows the empty
root {lit}`node [] []`.  Proved by strong induction on height (a {lit}`BTree`
cannot use {lit}`induction` directly because of the nested list recursion).
-/
theorem allKeysPos_of_occupancy (t : Nat) (ht : 2 ≤ t) (tr : BTree) (b : Bool)
    (hocc : Occupancy t b tr) (hne : 0 < numKeys tr) : AllKeysPos tr := by
  let motive (n : Nat) : Prop := ∀ (tr' : BTree), heightOf tr' = n →
    ∀ (b' : Bool), Occupancy t b' tr' → 0 < numKeys tr' → AllKeysPos tr'
  have h_ind : ∀ n, (∀ m < n, motive m) → motive n := by
    intro n ihn tr' hn b' hocc' hne'
    cases tr' with
    | node ks cs =>
      unfold AllKeysPos
      refine ⟨hne', ?_⟩
      intro c hc
      have hocc_c : Occupancy t false c := by
        unfold Occupancy at hocc'; exact hocc'.2.2.2 c hc
      cases c with
      | node cks ccs =>
        have hne_c : 0 < numKeys (node cks ccs) := by
          unfold Occupancy at hocc_c
          obtain ⟨hlo_c, -, -, -⟩ := hocc_c
          have hlo : t - 1 ≤ cks.length := hlo_c
          show 0 < cks.length
          omega
        have hlt : heightOf (node cks ccs) < n :=
          calc heightOf (node cks ccs) < heightOf (node ks cs) := heightOf_mem_lt hc
            _ = n := hn
        exact ihn _ hlt _ rfl false hocc_c hne_c
  exact (Nat.strongRecOn (motive := motive) (heightOf tr) h_ind) tr rfl b hocc hne

/--
**Merge preserves hereditary key-nonemptiness.**  The merged key list
{lit}`lKeys ++ sep :: rKeys` is always nonempty, and children are inherited
from the two inputs.
-/
lemma allKeysPos_mergeNodes {l r : BTree} {sep : Nat}
    (hl : AllKeysPos l) (hr : AllKeysPos r) : AllKeysPos (mergeNodes l sep r) := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      rw [mergeNodes_node]
      show AllKeysPos (node (lKeys ++ sep :: rKeys) (lCh ++ rCh))
      unfold AllKeysPos at hl hr ⊢
      obtain ⟨hlk, hlc⟩ := hl
      obtain ⟨hrk, hrc⟩ := hr
      refine ⟨?_, ?_⟩
      · simp only [List.length_append, List.length_cons]; omega
      · intro c hc
        rw [List.mem_append] at hc
        rcases hc with hc | hc
        · exact hlc c hc
        · exact hrc c hc

/--
**{lit}`rotateRight` repaired-left node preserves {lit}`AllKeysPos`.**  The
new key list {lit}`lKeys ++ [sep]` is always nonempty and the children come
from the two inputs.
-/
lemma allKeysPos_rotateRight_left (t : Nat) (ht : 2 ≤ t) (l : BTree) (sep : Nat) (r : BTree)
    (_hrlen : t ≤ numKeys r) (hl : AllKeysPos l) (hr : AllKeysPos r) :
    AllKeysPos (rotateRight l sep r).1 := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases rKeys with
      | nil => rw [rotateRight_nil]; exact hl
      | cons rHead rTail =>
        rw [rotateRight_cons]
        show AllKeysPos (node (lKeys ++ [sep]) (lCh ++ rCh.take 1))
        unfold AllKeysPos at hl hr ⊢
        obtain ⟨hlk, hlc⟩ := hl
        obtain ⟨hrk, hrc⟩ := hr
        refine ⟨?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · intro c hc
          rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact hlc c hc
          · exact hrc c (List.take_subset 1 rCh hc)

/--
**{lit}`rotateRight` trimmed-right node preserves {lit}`AllKeysPos`.**  The
trimmed key list {lit}`rTail` is nonempty because the lender had ≥ {lit}`t`
keys (so ≥ 2); the children are a sub-list of the original right children.
-/
lemma allKeysPos_rotateRight_right (t : Nat) (ht : 2 ≤ t) (l : BTree) (sep : Nat) (r : BTree)
    (hrlen : t ≤ numKeys r) (hl : AllKeysPos l) (hr : AllKeysPos r) :
    AllKeysPos (rotateRight l sep r).2.2 := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases rKeys with
      | nil => change t ≤ 0 at hrlen; omega
      | cons rHead rTail =>
        rw [rotateRight_cons]
        show AllKeysPos (node rTail (rCh.drop 1))
        unfold AllKeysPos at hr ⊢
        obtain ⟨hrk, hrc⟩ := hr
        refine ⟨?_, ?_⟩
        · have h1 : t ≤ rTail.length + 1 := hrlen
          omega
        · intro c hc
          exact hrc c (List.drop_subset 1 rCh hc)

/--
**{lit}`rotateLeft` trimmed-left node preserves {lit}`AllKeysPos`.**  The
trimmed key list {lit}`lKeys.dropLast` is nonempty because the lender had ≥
{lit}`t` keys (so ≥ 2).
-/
lemma allKeysPos_rotateLeft_left (t : Nat) (ht : 2 ≤ t) (l : BTree) (sep : Nat) (r : BTree)
    (hllen : t ≤ numKeys l) (hl : AllKeysPos l) (hr : AllKeysPos r) :
    AllKeysPos (rotateLeft l sep r).1 := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases lKeys with
      | nil => change t ≤ 0 at hllen; omega
      | cons lHead lTail =>
        rw [rotateLeft_cons]
        show AllKeysPos (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1)))
        unfold AllKeysPos at hl ⊢
        obtain ⟨hlk, hlc⟩ := hl
        refine ⟨?_, ?_⟩
        · have h1 : t ≤ lTail.length + 1 := hllen
          rw [List.length_dropLast, List.length_cons]
          omega
        · intro c hc
          exact hlc c (List.take_subset _ lCh hc)

/--
**{lit}`rotateLeft` repaired-right node preserves {lit}`AllKeysPos`.**  The
new key list {lit}`sep :: rKeys` is always nonempty and the children come from
the two inputs.
-/
lemma allKeysPos_rotateLeft_right (t : Nat) (ht : 2 ≤ t) (l : BTree) (sep : Nat) (r : BTree)
    (_hllen : t ≤ numKeys l) (hl : AllKeysPos l) (hr : AllKeysPos r) :
    AllKeysPos (rotateLeft l sep r).2.2 := by
  cases l with
  | node lKeys lCh =>
    cases r with
    | node rKeys rCh =>
      cases lKeys with
      | nil => rw [rotateLeft_nil]; exact hr
      | cons lHead lTail =>
        rw [rotateLeft_cons]
        show AllKeysPos (node (sep :: rKeys) (lCh.drop (lCh.length - 1) ++ rCh))
        unfold AllKeysPos at hl hr ⊢
        obtain ⟨hlk, hlc⟩ := hl
        obtain ⟨hrk, hrc⟩ := hr
        refine ⟨?_, ?_⟩
        · simp only [List.length_cons]; omega
        · intro c hc
          rw [List.mem_append] at hc
          rcases hc with hc | hc
          · exact hlc c (List.drop_subset _ lCh hc)
          · exact hrc c hc

/--
**Composed B-tree deletion (CLRS {lit}`B-TREE-DELETE` with pre-emptive repair).**

Semantic contract:

- *Leaf*: {lit}`node (sortedRemove x ks) []` — remove {lit}`x` from the key list.
- *Case 1* ({lit}`x = ks[ki]` hits a separator, {lit}`ki = findChild ks x - 1`):
  - **1a** left child has ≥ {lit}`t` keys: replace the separator by
    {lit}`m := maxKey leftChild` and recursively delete {lit}`m` from the left
    child.
  - **1b** else the right child has ≥ {lit}`t` keys: symmetric, with
    {lit}`m := minKey rightChild` deleted from the right child.
  - **1c** else both children are minimal: merge them around {lit}`x` and
    recurse into the merged node (as before).
- *Case 2* (descend into child {lit}`j`, three descent sites: {lit}`k ≠ x`,
  {lit}`ks[ki]? = none`, and {lit}`findChild ks x = 0`): guarded descent —
  - child has ≥ {lit}`t` keys: descend directly (as before);
  - else the left sibling {lit}`cs[j-1]` exists ({lit}`j > 0`) and has ≥
    {lit}`t` keys: {lit}`rotateLeft` borrows across separator {lit}`ks[j-1]`,
    descend into the repaired child;
  - else the right sibling {lit}`cs[j+1]` exists and has ≥ {lit}`t` keys:
    {lit}`rotateRight` borrows across separator {lit}`ks[j]`, descend into the
    repaired child;
  - else merge with an available sibling ({lit}`j > 0`: left, {lit}`j = 0`:
    right) and descend into the merged node.
  Degenerate branches (sibling or separator lookup failure) fall back to the
  unguarded direct descent, keeping the function total on arbitrary inputs.
- The {lit}`i = 0` descent site has no left sibling, so its guard sequence is
  only "direct → borrow right → merge right".

Termination is by {lit}`heightOf`: every recursive call targets either a child
({lit}`heightOf_mem_lt`) or a rotation/merge result whose height is at most the
maximum of two child heights ({lit}`heightOf_rotateLeft_right_le`,
{lit}`heightOf_rotateRight_left_le`, {lit}`heightOf_mergeNodes_eq_max`),
strictly below the parent's height.
-/
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
                if hla : t ≤ numKeys leftChild then
                  -- Case 1a: predecessor replaces the separator
                  node (ks.set ki (maxKey leftChild))
                    (cs.set ki (composedDelete t (maxKey leftChild) leftChild))
                else if hlb : t ≤ numKeys rightChild then
                  -- Case 1b: successor replaces the separator
                  node (ks.set ki (minKey rightChild))
                    (cs.set (ki + 1) (composedDelete t (minKey rightChild) rightChild))
                else
                  -- Case 1c: both children minimal, merge and recurse
                  let merged := mergeNodes leftChild k rightChild
                  let newMerged := composedDelete t x merged
                  node (ks.take ki ++ ks.drop (ki + 1)) ((cs.take ki) ++ [newMerged] ++ (cs.drop (ki + 2)))
              | none => node (sortedRemove x ks) []
            | none => node (sortedRemove x ks) []
          else
            -- Case 2 descent at j = i (separator key not equal to x)
            match hc : cs[i]? with
            | some child =>
              if hcg : t ≤ numKeys child then
                node ks (cs.set i (composedDelete t x child))
              else
                match hls : cs[i - 1]? with
                | some leftSib =>
                  if hlg : t ≤ numKeys leftSib then
                    match hsep : ks[i - 1]? with
                    | some sep =>
                      node (ks.set (i - 1) (rotateLeft leftSib sep child).2.1)
                        ((cs.set (i - 1) (rotateLeft leftSib sep child).1).set i
                          (composedDelete t x (rotateLeft leftSib sep child).2.2))
                    | none => node ks (cs.set i (composedDelete t x child))
                  else
                    match hrs : cs[i + 1]? with
                    | some rightSib =>
                      if hrg : t ≤ numKeys rightSib then
                        match hsep : ks[i]? with
                        | some sep =>
                          node (ks.set i (rotateRight child sep rightSib).2.1)
                            ((cs.set i (composedDelete t x (rotateRight child sep rightSib).1)).set
                              (i + 1) (rotateRight child sep rightSib).2.2)
                        | none => node ks (cs.set i (composedDelete t x child))
                      else
                        match hsep : ks[i - 1]? with
                        | some sep =>
                          node (ks.take (i - 1) ++ ks.drop i)
                            (cs.take (i - 1) ++
                              [composedDelete t x (mergeNodes leftSib sep child)] ++
                              cs.drop (i + 1))
                        | none => node ks (cs.set i (composedDelete t x child))
                    | none =>
                      match hsep : ks[i - 1]? with
                      | some sep =>
                        node (ks.take (i - 1) ++ ks.drop i)
                          (cs.take (i - 1) ++
                            [composedDelete t x (mergeNodes leftSib sep child)] ++
                            cs.drop (i + 1))
                      | none => node ks (cs.set i (composedDelete t x child))
                | none => node ks (cs.set i (composedDelete t x child))
            | none => node ks cs
        | none =>
          -- Case 2 descent at j = i (separator lookup failed)
          match hc : cs[i]? with
          | some child =>
            if hcg : t ≤ numKeys child then
              node ks (cs.set i (composedDelete t x child))
            else
              match hls : cs[i - 1]? with
              | some leftSib =>
                if hlg : t ≤ numKeys leftSib then
                  match hsep : ks[i - 1]? with
                  | some sep =>
                    node (ks.set (i - 1) (rotateLeft leftSib sep child).2.1)
                      ((cs.set (i - 1) (rotateLeft leftSib sep child).1).set i
                        (composedDelete t x (rotateLeft leftSib sep child).2.2))
                  | none => node ks (cs.set i (composedDelete t x child))
                else
                  match hrs : cs[i + 1]? with
                  | some rightSib =>
                    if hrg : t ≤ numKeys rightSib then
                      match hsep : ks[i]? with
                      | some sep =>
                        node (ks.set i (rotateRight child sep rightSib).2.1)
                          ((cs.set i (composedDelete t x (rotateRight child sep rightSib).1)).set
                            (i + 1) (rotateRight child sep rightSib).2.2)
                      | none => node ks (cs.set i (composedDelete t x child))
                    else
                      match hsep : ks[i - 1]? with
                      | some sep =>
                        node (ks.take (i - 1) ++ ks.drop i)
                          (cs.take (i - 1) ++
                            [composedDelete t x (mergeNodes leftSib sep child)] ++
                            cs.drop (i + 1))
                      | none => node ks (cs.set i (composedDelete t x child))
                  | none =>
                    match hsep : ks[i - 1]? with
                    | some sep =>
                      node (ks.take (i - 1) ++ ks.drop i)
                        (cs.take (i - 1) ++
                          [composedDelete t x (mergeNodes leftSib sep child)] ++
                          cs.drop (i + 1))
                    | none => node ks (cs.set i (composedDelete t x child))
              | none => node ks (cs.set i (composedDelete t x child))
          | none => node ks cs
      else
        -- Case 2 descent at j = 0: no left sibling, right-only guard sequence
        match hc : cs[0]? with
        | some child =>
          if hcg : t ≤ numKeys child then
            node ks (cs.set 0 (composedDelete t x child))
          else
            match hrs : cs[1]? with
            | some rightSib =>
              if hrg : t ≤ numKeys rightSib then
                match hsep : ks[0]? with
                | some sep =>
                  node (ks.set 0 (rotateRight child sep rightSib).2.1)
                    ((cs.set 0 (composedDelete t x (rotateRight child sep rightSib).1)).set 1
                      (rotateRight child sep rightSib).2.2)
                | none => node ks (cs.set 0 (composedDelete t x child))
              else
                match hsep : ks[0]? with
                | some sep =>
                  node (ks.drop 1)
                    ([composedDelete t x (mergeNodes child sep rightSib)] ++ cs.drop 2)
                | none => node ks (cs.set 0 (composedDelete t x child))
            | none => node ks (cs.set 0 (composedDelete t x child))
        | none => node ks cs
termination_by tr => heightOf tr
decreasing_by
  · -- Case 1a: recurse into the left child
    exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki, hcl⟩)
  · -- Case 1b: recurse into the right child
    exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki + 1, hcr⟩)
  · -- Case 1c merge: the merged node has the maximum of the two heights
    rw [heightOf_mergeNodes_eq_max]
    have ha : heightOf leftChild < heightOf (node ks cs) :=
      heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki, hcl⟩)
    have hb : heightOf rightChild < heightOf (node ks cs) :=
      heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki + 1, hcr⟩)
    omega
  all_goals
    first
      -- Merge branches: the merged node has the maximum of the two heights
      | (rw [heightOf_mergeNodes_eq_max]
         first
           | (have ha : heightOf leftSib < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hls⟩)
              have hb : heightOf child < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
              omega)
           | (have ha : heightOf child < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
              have hb : heightOf rightSib < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hrs⟩)
              omega))
      -- Direct descents and degenerate fallbacks: recurse into a child of `cs`
      | exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
      -- Borrow-left: the repaired child is bounded by both sibling heights
      | (have hle := heightOf_rotateLeft_right_le leftSib sep child
         have ha : heightOf leftSib < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hls⟩)
         have hb : heightOf child < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
         omega)
      -- Borrow-right: the repaired child is bounded by both sibling heights
      | (have hle := heightOf_rotateRight_left_le child sep rightSib
         have ha : heightOf child < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
         have hb : heightOf rightSib < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hrs⟩)
         omega)

end BTree
end Chapter18
end CLRS
