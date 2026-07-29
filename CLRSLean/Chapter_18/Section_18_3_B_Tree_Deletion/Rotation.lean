import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion

/-! # B-tree deletion: rotations preserve `Sorted` and `ChildBounded`

This submodule collects the ordering and key-range preservation lemmas for the
two sibling rotations of CLRS `B-TREE-DELETE` case 3a: {lit}`rotateRight`
(the underflowing left child borrows the separator and the right sibling's
first child) and {lit}`rotateLeft` (the symmetric borrow from the left
sibling).  For each rotation, both result nodes are shown to preserve the
{lit}`Sorted` invariant and the {lit}`ChildBounded` key-range invariant, given
the corresponding invariants on the two input siblings plus the
separator-ordering facts ({lit}`hL_le`, {lit}`hR_ge`) supplied by the parent's
{lit}`ChildBounded` invariant.

The hypothesis shape and proof technique mirror {lit}`mergeNodes_sorted` and
{lit}`mergeNodes_childBounded`: pairwise ordering of concatenated key lists,
and per-child bound transfer via `getElem`/`getElem?` index arithmetic over
the split and joined child lists.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-! ## `rotateRight`: the new left node preserves `Sorted` -/

/--
**`rotateRight` new-left node is `Sorted`.**  The borrowed separator becomes
the new last key of the left child; `hL_le` (every key of the left sibling is
at most `sep`) is exactly what keeps the extended key list pairwise ordered.
The moved child `rCh[0]` inherits `Sorted` from the right sibling.
-/
lemma rotateRight_sorted_left
    {lKeys rTail : List Nat} {lCh rCh : List BTree} {sep rHead : Nat}
    (hL_s : Sorted (node lKeys lCh)) (hR_s : Sorted (node (rHead :: rTail) rCh))
    (hL_le : ∀ k ∈ keysOf (node lKeys lCh), k ≤ sep) (hsep : sep ≤ rHead) :
    Sorted (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) := by
  unfold Sorted at hL_s hR_s ⊢
  obtain ⟨hL_pw, hL_ch⟩ := hL_s
  obtain ⟨hR_pw, hR_ch⟩ := hR_s
  refine ⟨?_, ?_⟩
  · -- Pairwise (lKeys ++ [sep])
    rw [List.pairwise_append]
    refine ⟨hL_pw, by simp, ?_⟩
    intro a ha b hb
    simp only [List.mem_singleton] at hb
    subst hb
    exact hL_le a (by simp [keysOf, ha])
  · -- children inherit Sorted from the two siblings
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_ch c hc
    · exact hR_ch c (List.mem_of_mem_take hc)

/--
**`rotateRight` new-right node is `Sorted`.**  Dropping the first key and the
first child of the right sibling keeps both components of `Sorted`.
-/
lemma rotateRight_sorted_right {rHead : Nat} {rTail : List Nat} {rCh : List BTree}
    (hR_s : Sorted (node (rHead :: rTail) rCh)) :
    Sorted (node rTail (rCh.drop 1)) := by
  unfold Sorted at hR_s ⊢
  obtain ⟨hR_pw, hR_ch⟩ := hR_s
  exact ⟨(List.pairwise_cons.mp hR_pw).2,
    fun c hc => hR_ch c ((List.drop_subset 1 rCh) hc)⟩

/-! ## `rotateRight`: the new nodes preserve `ChildBounded` -/

/--
**`rotateRight` new-left node is `ChildBounded`.**  The appended child
`rCh[0]` sits between the new last key `sep` (lower bound, from `hR_ge`) and
no upper key; every other child keeps its original neighboring keys.
-/
lemma rotateRight_childBounded_left
    {lKeys rTail : List Nat} {lCh rCh : List BTree} {sep rHead : Nat}
    (hL_cb : ChildBounded (node lKeys lCh))
    (hR_cb : ChildBounded (node (rHead :: rTail) rCh))
    (hshape : (lCh = []) ↔ (rCh = []))
    (hL_le : ∀ k ∈ keysOf (node lKeys lCh), k ≤ sep)
    (hR_ge : ∀ k ∈ keysOf (node (rHead :: rTail) rCh), sep ≤ k) :
    ChildBounded (node (lKeys ++ [sep]) (lCh ++ rCh.take 1)) := by
  unfold ChildBounded at hL_cb hR_cb ⊢
  obtain ⟨hL_rel, hL_bounds, hL_sub⟩ := hL_cb
  obtain ⟨hR_rel, hR_bounds, hR_sub⟩ := hR_cb
  have hL_len : lCh = [] ∨ lCh.length = lKeys.length + 1 := by
    rcases hL_rel with hLe | hLlen
    · left; cases lCh with | nil => rfl | cons x xs => simp at hLe
    · right; exact hLlen
  have hR_len : rCh = [] ∨ rCh.length = (rHead :: rTail).length + 1 := by
    rcases hR_rel with hRe | hRlen
    · left; cases rCh with | nil => rfl | cons x xs => simp at hRe
    · right; exact hRlen
  refine ⟨?_, ?_, ?_⟩
  · -- component 1: children count
    rcases hL_len with hl | hLlen
    · have hr : rCh = [] := hshape.mp hl
      subst hl; subst hr; left; rfl
    · rcases hR_len with hr | hRlen
      · have hl0 : lCh = [] := hshape.mpr hr
        rw [hl0] at hLlen; simp at hLlen
      · right
        simp only [List.length_append, List.length_take, List.length_cons,
          List.length_nil, hLlen]
        simp only [List.length_cons] at hRlen
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
      have hRpos : 0 < rCh.length := by
        rcases hR_len with h | h
        · exact absurd h hrCh
        · simp only [List.length_cons] at h; omega
      have htake1 : (rCh.take 1).length = 1 := by
        rw [List.length_take]; omega
      refine ⟨?_, ?_⟩
      · -- lower bound: (lKeys ++ [sep])[i-1]? bounds child i from below
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · exact Or.inl hi0
        · right
          by_cases hiL : i < lCh.length
          · -- child in the left segment: lower key is lKeys[i-1]
            have hi1 : i - 1 < lKeys.length := by omega
            have hchild : (lCh ++ rCh.take 1).get ⟨i, hi⟩ = lCh.get ⟨i, hiL⟩ :=
              List.getElem_append_left hiL
            have heq : (lKeys ++ [sep])[i-1]? = lKeys[i-1]? :=
              List.getElem?_append_left (by omega)
            rw [heq, List.getElem?_eq_getElem hi1]
            have hb := (hL_bounds i hiL).1
            rcases hb with h0 | hb
            · omega
            · simp only [List.getElem?_eq_getElem hi1] at hb
              intro k hk
              rw [hchild] at hk
              exact hb k hk
          · -- child is the moved rCh[0]: lower key is the separator
            have hlo : (lKeys ++ [sep])[i-1]? = some sep := by
              have e : i - 1 = lKeys.length := by
                have hi' := hi
                rw [List.length_append, htake1] at hi'
                omega
              rw [e, List.getElem?_append_right (Nat.le_refl _)]
              simp
            rw [hlo]
            intro k hk
            have hchild : (lCh ++ rCh.take 1).get ⟨i, hi⟩ = rCh.get ⟨0, hRpos⟩ := by
              have hpi : i - lCh.length < (rCh.take 1).length := by
                rw [htake1]
                have hi' := hi
                rw [List.length_append, htake1] at hi'
                omega
              have h1 : (lCh ++ rCh.take 1).get ⟨i, hi⟩ =
                  (rCh.take 1).get ⟨i - lCh.length, hpi⟩ :=
                List.getElem_append_right (Nat.le_of_not_lt hiL)
              rw [h1]
              have hopt : (rCh.take 1)[i - lCh.length]? = rCh[0]? := by
                have e : i - lCh.length = 0 := by
                  have hi' := hi
                  rw [List.length_append, htake1] at hi'
                  omega
                rw [e, List.getElem?_take_of_lt Nat.zero_lt_one]
              have ha := List.getElem?_eq_getElem hpi
              have hb := List.getElem?_eq_getElem hRpos
              rw [hopt] at ha
              rw [ha] at hb
              exact Option.some.inj hb
            rw [hchild] at hk
            have hmem : k ∈ keysOf (node (rHead :: rTail) rCh) := by
              simp only [keysOf, List.mem_append, List.mem_flatMap]
              exact Or.inr ⟨rCh.get ⟨0, hRpos⟩, List.getElem_mem _, hk⟩
            exact hR_ge k hmem
      · -- upper bound: (lKeys ++ [sep])[i]? bounds child i from above
        by_cases hiL : i < lCh.length
        · -- child in the left segment
          have hchild : (lCh ++ rCh.take 1).get ⟨i, hi⟩ = lCh.get ⟨i, hiL⟩ :=
            List.getElem_append_left hiL
          by_cases hiK : i < lKeys.length
          · -- upper key is lKeys[i]
            have heq : (lKeys ++ [sep])[i]? = lKeys[i]? :=
              List.getElem?_append_left hiK
            rw [heq, List.getElem?_eq_getElem hiK]
            have hub := (hL_bounds i hiL).2
            simp only [List.getElem?_eq_getElem hiK] at hub
            intro k hk
            rw [hchild] at hk
            exact hub k hk
          · -- child is lCh[lKeys.length]: upper key is the separator
            have hieq : i = lKeys.length := by omega
            have heq : (lKeys ++ [sep])[i]? = some sep := by
              rw [hieq, List.getElem?_append_right (Nat.le_refl _)]
              simp
            rw [heq]
            intro k hk
            rw [hchild] at hk
            have hmem : k ∈ keysOf (node lKeys lCh) := by
              simp only [keysOf, List.mem_append, List.mem_flatMap]
              exact Or.inr ⟨lCh.get ⟨i, hiL⟩, List.getElem_mem _, hk⟩
            exact hL_le k hmem
        · -- child is the moved rCh[0]: no upper key
          have hnone : (lKeys ++ [sep])[i]? = none := by
            apply List.getElem?_eq_none
            have hieq : i = lCh.length := by
              have hi' := hi
              rw [List.length_append, htake1] at hi'
              omega
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          rw [hnone]
          exact trivial
  · -- component 3: recursive ChildBounded on children
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_sub c hc
    · exact hR_sub c (List.mem_of_mem_take hc)

/--
**`rotateRight` new-right node is `ChildBounded`.**  Dropping the first key
and first child is the `d = 1` case of `childBounded_drop_of_full`; the leaf
case keeps an empty child list.
-/
lemma rotateRight_childBounded_right {rHead : Nat} {rTail : List Nat} {rCh : List BTree}
    (hR_cb : ChildBounded (node (rHead :: rTail) rCh)) :
    ChildBounded (node rTail (rCh.drop 1)) := by
  by_cases hr : rCh = []
  · subst hr
    exact childBounded_node_nil rTail
  · have hlen : rCh.length = (rHead :: rTail).length + 1 :=
      (childBounded_children_rel hR_cb).resolve_left hr
    have h1 : 1 < rCh.length := by
      simp only [List.length_cons] at hlen; omega
    exact childBounded_drop_of_full hR_cb (d := 1) (by omega) h1

/-! ## `rotateLeft`: the new nodes preserve `Sorted` -/

/--
**`rotateLeft` new-left node is `Sorted`.**  The left sibling loses its last
key and last child; truncating preserves both components of `Sorted`.
-/
lemma rotateLeft_sorted_left {lHead : Nat} {lTail : List Nat} {lCh : List BTree}
    (hL_s : Sorted (node (lHead :: lTail) lCh)) :
    Sorted (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) := by
  unfold Sorted at hL_s ⊢
  obtain ⟨hL_pw, hL_ch⟩ := hL_s
  exact ⟨hL_pw.sublist (List.dropLast_sublist _),
    fun c hc => hL_ch c (List.mem_of_mem_take hc)⟩

/--
**`rotateLeft` new-right node is `Sorted`.**  The separator becomes the new
first key of the right child; `hR_ge` (every key of the right sibling is at
least `sep`) keeps the extended key list pairwise ordered.  The moved child
inherits `Sorted` from the left sibling.
-/
lemma rotateLeft_sorted_right
    {lHead : Nat} {lTail rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hL_s : Sorted (node (lHead :: lTail) lCh)) (hR_s : Sorted (node rKeys rCh))
    (_hL_le : ∀ k ∈ keysOf (node (lHead :: lTail) lCh), k ≤ sep)
    (hR_ge : ∀ k ∈ keysOf (node rKeys rCh), sep ≤ k) :
    Sorted (node (sep :: rKeys) (lCh.drop (lCh.length - 1) ++ rCh)) := by
  unfold Sorted at hL_s hR_s ⊢
  obtain ⟨hL_pw, hL_ch⟩ := hL_s
  obtain ⟨hR_pw, hR_ch⟩ := hR_s
  refine ⟨?_, ?_⟩
  · -- Pairwise (sep :: rKeys)
    apply List.Pairwise.cons
    · intro k hk
      exact hR_ge k (by simp [keysOf, hk])
    · exact hR_pw
  · -- children inherit Sorted from the two siblings
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_ch c ((List.drop_subset _ _) hc)
    · exact hR_ch c hc

/-! ## `rotateLeft`: the new nodes preserve `ChildBounded` -/

/--
**`rotateLeft` new-left node is `ChildBounded`.**  Dropping the last key and
last child is truncation to `m = lTail.length`, i.e. `childBounded_take_of_full`
with `dropLast = take (length - 1)`; the leaf case keeps an empty child list.
-/
lemma rotateLeft_childBounded_left {lHead : Nat} {lTail : List Nat} {lCh : List BTree}
    (hL_cb : ChildBounded (node (lHead :: lTail) lCh)) :
    ChildBounded (node (lHead :: lTail).dropLast (lCh.take (lCh.length - 1))) := by
  by_cases hl : lCh = []
  · subst hl
    simp only [List.take_nil]
    exact childBounded_node_nil _
  · have hlen : lCh.length = (lHead :: lTail).length + 1 :=
      (childBounded_children_rel hL_cb).resolve_left hl
    rw [List.dropLast_eq_take]
    simp only [List.length_cons] at hlen
    have e1 : (lHead :: lTail).length - 1 = lTail.length := by simp
    have e2 : lCh.length - 1 = lTail.length + 1 := by omega
    rw [e1, e2]
    exact childBounded_take_of_full hL_cb (by simp only [List.length_cons]; omega)

/--
**`rotateLeft` new-right node is `ChildBounded`.**  The prepended child (the
left sibling's last child) sits between no lower key and the new first key
`sep` (upper bound, from `hL_le`); every other child keeps its original
neighboring keys, shifted by one.
-/
lemma rotateLeft_childBounded_right
    {lHead : Nat} {lTail rKeys : List Nat} {lCh rCh : List BTree} {sep : Nat}
    (hL_cb : ChildBounded (node (lHead :: lTail) lCh))
    (hR_cb : ChildBounded (node rKeys rCh))
    (hshape : (lCh = []) ↔ (rCh = []))
    (hL_le : ∀ k ∈ keysOf (node (lHead :: lTail) lCh), k ≤ sep)
    (hR_ge : ∀ k ∈ keysOf (node rKeys rCh), sep ≤ k) :
    ChildBounded (node (sep :: rKeys) (lCh.drop (lCh.length - 1) ++ rCh)) := by
  unfold ChildBounded at hL_cb hR_cb ⊢
  obtain ⟨hL_rel, hL_bounds, hL_sub⟩ := hL_cb
  obtain ⟨hR_rel, hR_bounds, hR_sub⟩ := hR_cb
  have hL_len : lCh = [] ∨ lCh.length = (lHead :: lTail).length + 1 := by
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
    · have hr : rCh = [] := hshape.mp hl
      subst hl; subst hr; left; rfl
    · rcases hR_len with hr | hRlen
      · have hl0 : lCh = [] := hshape.mpr hr
        rw [hl0] at hLlen; simp at hLlen
      · right
        have hdroplen1 : (lCh.drop (lCh.length - 1)).length = 1 := by
          rw [List.length_drop]
          simp only [List.length_cons] at hLlen
          omega
        simp only [List.length_append, List.length_cons, hdroplen1]
        omega
  · -- component 2: per-child key bounds
    intro i hi
    by_cases hlCh : lCh = []
    · have hrCh : rCh = [] := hshape.mp hlCh
      subst hlCh; subst hrCh; simp at hi
    · have hrCh : rCh ≠ [] := fun h => hlCh (hshape.mpr h)
      have hLlen : lCh.length = lTail.length + 2 := by
        rcases hL_len with h | h
        · exact absurd h hlCh
        · simp only [List.length_cons] at h; omega
      have hRlen : rCh.length = rKeys.length + 1 := by
        rcases hR_len with h | h
        · exact absurd h hrCh
        · exact h
      have hdroplen : (lCh.drop (lCh.length - 1)).length = 1 := by
        rw [List.length_drop]; omega
      refine ⟨?_, ?_⟩
      · -- lower bound: (sep :: rKeys)[i-1]? bounds child i from below
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · exact Or.inl hi0
        · right
          have hj : i - 1 < rCh.length := by
            have hi' := hi
            rw [List.length_append, hdroplen] at hi'
            omega
          have hchild : (lCh.drop (lCh.length - 1) ++ rCh).get ⟨i, hi⟩ =
              rCh.get ⟨i - 1, hj⟩ := by
            have hopt : (lCh.drop (lCh.length - 1) ++ rCh)[i]? = rCh[i - 1]? := by
              rw [List.getElem?_append_right (by rw [hdroplen]; omega), hdroplen]
            have ha := List.getElem?_eq_getElem hi
            have hb := List.getElem?_eq_getElem hj
            rw [hopt] at ha
            rw [ha] at hb
            exact Option.some.inj hb
          by_cases hj0 : i - 1 = 0
          · -- child is rCh[0]: lower key is the separator
            have h0 : (sep :: rKeys)[i-1]? = some sep := by simp [hj0]
            rw [h0]
            intro k hk
            rw [hchild] at hk
            have hmem : k ∈ keysOf (node rKeys rCh) := by
              simp only [keysOf, List.mem_append, List.mem_flatMap]
              exact Or.inr ⟨rCh.get ⟨i - 1, hj⟩, List.getElem_mem _, hk⟩
            exact hR_ge k hmem
          · -- lower key is rKeys[i-2]
            have hj1 : i - 1 - 1 < rKeys.length := by omega
            have hcons : (sep :: rKeys)[i-1]? = rKeys[i-1-1]? := by
              conv_lhs => rw [show i - 1 = (i - 1 - 1) + 1 from by omega]
              exact List.getElem?_cons_succ
            rw [hcons, List.getElem?_eq_getElem hj1]
            have hb := (hR_bounds (i - 1) hj).1
            rcases hb with h0' | hb
            · omega
            · simp only [List.getElem?_eq_getElem hj1] at hb
              intro k hk
              rw [hchild] at hk
              exact hb k hk
      · -- upper bound: (sep :: rKeys)[i]? bounds child i from above
        by_cases hi0 : i = 0
        · -- child is the moved lCh-last child: upper key is the separator
          subst hi0
          have h0 : (sep :: rKeys)[0]? = some sep := by simp
          rw [h0]
          intro k hk
          have hpos : lCh.length - 1 < lCh.length := by omega
          have hchild : (lCh.drop (lCh.length - 1) ++ rCh).get ⟨0, hi⟩ =
              lCh.get ⟨lCh.length - 1, hpos⟩ := by
            have hopt : (lCh.drop (lCh.length - 1) ++ rCh)[0]? = lCh[lCh.length - 1]? := by
              rw [List.getElem?_append_left (by rw [hdroplen]; omega),
                List.getElem?_drop, Nat.add_zero]
            have ha := List.getElem?_eq_getElem hi
            have hb := List.getElem?_eq_getElem hpos
            rw [hopt] at ha
            rw [ha] at hb
            exact Option.some.inj hb
          rw [hchild] at hk
          have hmem : k ∈ keysOf (node (lHead :: lTail) lCh) := by
            simp only [keysOf, List.mem_append, List.mem_flatMap]
            exact Or.inr ⟨lCh.get ⟨lCh.length - 1, hpos⟩, List.getElem_mem _, hk⟩
          exact hL_le k hmem
        · -- child is rCh[i-1]: upper key is rKeys[i-1]
          have hj : i - 1 < rCh.length := by
            have hi' := hi
            rw [List.length_append, hdroplen] at hi'
            omega
          have hchild : (lCh.drop (lCh.length - 1) ++ rCh).get ⟨i, hi⟩ =
              rCh.get ⟨i - 1, hj⟩ := by
            have hopt : (lCh.drop (lCh.length - 1) ++ rCh)[i]? = rCh[i - 1]? := by
              rw [List.getElem?_append_right (by rw [hdroplen]; omega), hdroplen]
            have ha := List.getElem?_eq_getElem hi
            have hb := List.getElem?_eq_getElem hj
            rw [hopt] at ha
            rw [ha] at hb
            exact Option.some.inj hb
          have heq : (sep :: rKeys)[i]? = rKeys[i-1]? := by
            conv_lhs => rw [show i = (i - 1) + 1 from by omega]
            exact List.getElem?_cons_succ
          rw [heq]
          by_cases hjK : i - 1 < rKeys.length
          · rw [List.getElem?_eq_getElem hjK]
            have hub := (hR_bounds (i - 1) hj).2
            simp only [List.getElem?_eq_getElem hjK] at hub
            intro k hk
            rw [hchild] at hk
            exact hub k hk
          · -- child is rCh[rKeys.length]: no upper key
            have hnone : rKeys[i-1]? = none := List.getElem?_eq_none (by omega)
            rw [hnone]
            exact trivial
  · -- component 3: recursive ChildBounded on children
    intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact hL_sub c ((List.drop_subset _ _) hc)
    · exact hR_sub c hc

end BTree
end Chapter18
end CLRS
