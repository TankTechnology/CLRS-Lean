import CLRSLean.FourthEdition.Chapter_18.Section_18_1_B_Tree_Model

/-!
# CLRS Section 18.1 - Separator-guided B-tree search

Defines the child-selection function used by B-tree search and insertion,
reusable path-localization and height lemmas, and a total executable search
that descends through exactly one separator-selected child.

Main results:

* {lit}`findChild_localizes_mem`: localizes a non-separator member to the
  selected child under sorted and child-bounded node invariants.
* {lit}`searchExec`: checks the current node and otherwise follows only the
  separator-selected child.
* {lit}`searchExec_sound`: successful executable search implies membership
  without structural assumptions.
* {lit}`searchExec_complete`: sorted, child-bounded trees expose every member
  along the selected path.
* {lit}`searchExec_true_iff`: on sorted, child-bounded trees, characterizes
  successful executable search by membership.
* {lit}`searchExec_eq_search`: on sorted, child-bounded trees, connects
  executable search to the imported specification oracle
  {name (full := CLRS.Chapter18.BTree.search)}`search`.

The selected-child localization and routing wrappers are used by the proved
exact erase-one semantics for executable deletion.
-/

namespace CLRS.Chapter18.BTree

open List

/-! ## Child selection -/

/-- Index of the child that key `x` descends into: the number of leading keys
`≤ x` (correct for a sorted key list). -/
def findChild : List Nat → Nat → Nat
  | [], _ => 0
  | k :: ks, x => if k ≤ x then findChild ks x + 1 else 0

/-! ## Height lemmas -/

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

/-! ## Child-index bounds and range correctness -/

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

/--
If a key absent from a sorted node's separators occurs in one of its children,
that child is exactly the one selected by {name}`findChild`.
-/
theorem findChild_localizes_mem
    {ks : List Nat} {cs : List BTree} {x j : Nat} {child : BTree}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hbounded : ChildBounded (node ks cs))
    (hxkeys : x ∉ ks)
    (hchild : cs[j]? = some child)
    (hxchild : x ∈ keysOf child) :
    j = findChild ks x := by
  have hjcs : j < cs.length :=
    _root_.of_getElem?_eq_some (c := cs) (i := j) hchild
  have hchild_get : cs.get ⟨j, hjcs⟩ = child :=
    (_root_.getElem?_eq_some_iff.mp hchild).choose_spec
  unfold ChildBounded at hbounded
  rcases hbounded with ⟨hshape, hbounds, _⟩
  have hlength : cs.length = ks.length + 1 := by
    rcases hshape with hempty | hlength
    · have : cs.length = 0 := by simpa using hempty
      omega
    · exact hlength
  have hjbounds := hbounds j hjcs
  dsimp only at hjbounds
  rw [hchild_get] at hjbounds
  have hnot_left : ¬j < findChild ks x := by
    intro hjleft
    have hjks : j < ks.length := by
      have := findChild_le ks x
      omega
    have hsep_mem : ks[j] ∈ ks.take (findChild ks x) := by
      rw [List.mem_iff_getElem?]
      refine ⟨j, ?_⟩
      rw [List.getElem?_take_of_lt hjleft, List.getElem?_eq_getElem hjks]
    have hsep_le : ks[j] ≤ x :=
      findChild_take_le x ks ks[j] hsep_mem
    have hkey_le : x ≤ ks[j] := by
      have hupper := hjbounds.2
      simp only [List.getElem?_eq_getElem hjks] at hupper
      exact hupper x hxchild
    apply hxkeys
    rw [show x = ks[j] by omega]
    exact List.getElem_mem hjks
  have hnot_right : ¬findChild ks x < j := by
    intro hjright
    have hjpos : 0 < j := by omega
    have hjpred : j - 1 < ks.length := by omega
    have hsep_mem : ks[j - 1] ∈ ks.drop (findChild ks x) := by
      rw [List.mem_iff_getElem?]
      refine ⟨j - 1 - findChild ks x, ?_⟩
      rw [List.getElem?_drop]
      have hindex :
          findChild ks x + (j - 1 - findChild ks x) = j - 1 := by
        omega
      rw [hindex, List.getElem?_eq_getElem hjpred]
    have hx_lt : x < ks[j - 1] :=
      findChild_drop_gt x hsorted (ks[j - 1]) hsep_mem
    have hsep_le : ks[j - 1] ≤ x := by
      rcases hjbounds.1 with hjzero | hlower
      · omega
      · simp only [List.getElem?_eq_getElem hjpred] at hlower
        exact hlower x hxchild
    omega
  omega

/--
If a key occurs among sorted separators, the selected child index is positive
and its predecessor separator is that key.
-/
theorem findChild_pos_and_pred_eq_of_mem
    {ks : List Nat} {x : Nat}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hx : x ∈ ks) :
    0 < findChild ks x ∧
      ks[findChild ks x - 1]? = some x := by
  induction ks with
  | nil => simp at hx
  | cons a as ih =>
      have hsortedTail : List.Pairwise (· ≤ ·) as :=
        (List.pairwise_cons.mp hsorted).2
      have ha_le : a ≤ x := by
        rcases List.mem_cons.mp hx with hxa | hxTail
        · omega
        · exact (List.pairwise_cons.mp hsorted).1 x hxTail
      rw [findChild, if_pos ha_le]
      refine ⟨by omega, ?_⟩
      simp only [Nat.add_sub_cancel]
      by_cases hxTail : x ∈ as
      · obtain ⟨hpos, hpred⟩ := ih hsortedTail hxTail
        cases hfind : findChild as x with
        | zero => omega
        | succ j =>
            simp only [hfind, Nat.succ_sub_one] at hpred
            simpa [hfind] using hpred
      · have hxa : x = a :=
          (List.mem_cons.mp hx).resolve_right hxTail
        subst x
        have hzero : findChild as a = 0 := by
          cases as with
          | nil => rfl
          | cons b bs =>
              have hab : a ≤ b :=
                (List.pairwise_cons.mp hsorted).1 b (by simp)
              have hne : b ≠ a := by
                intro hba
                apply hxTail
                simp [hba]
              have hnot : ¬b ≤ a := by omega
              simp [findChild, hnot]
        simp [hzero]

/--
A non-selected child of a sorted, child-bounded node cannot contain a key
that is absent from the node's separators.
-/
theorem findChild_not_mem_child_of_ne
    {ks : List Nat} {cs : List BTree} {x j : Nat} {child : BTree}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hbounded : ChildBounded (node ks cs))
    (hxkeys : x ∉ ks)
    (hchild : cs[j]? = some child)
    (hne : j ≠ findChild ks x) :
    x ∉ keysOf child := by
  intro hxchild
  exact hne
    (findChild_localizes_mem hsorted hbounded hxkeys hchild hxchild)

/--
If a non-separator key belongs to a sorted, child-bounded node, it belongs to
the selected child.
-/
theorem findChild_selected_child_mem
    {ks : List Nat} {cs : List BTree} {x : Nat} {child : BTree}
    (hsorted : List.Pairwise (· ≤ ·) ks)
    (hbounded : ChildBounded (node ks cs))
    (hxkeys : x ∉ ks)
    (hchild : cs[findChild ks x]? = some child)
    (hx : x ∈ keysOf (node ks cs)) :
    x ∈ keysOf child := by
  unfold keysOf at hx
  rw [List.mem_append, List.mem_flatMap] at hx
  rcases hx with hxnode | ⟨descendant, hdescendant, hxdescendant⟩
  · exact (hxkeys hxnode).elim
  · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdescendant
    have hjfind : j = findChild ks x :=
      findChild_localizes_mem hsorted hbounded hxkeys hj hxdescendant
    rw [hjfind, hchild] at hj
    cases hj
    exact hxdescendant

/-! ## Executable search -/

/--
Separator-guided executable B-tree search.  The current node is checked first;
on a miss, search continues only in the child selected by {name}`findChild`.
-/
def searchExec (x : Nat) : BTree → Bool
  | node ks cs =>
      if x ∈ ks then
        true
      else
        match _hc : cs[findChild ks x]? with
        | some child => searchExec x child
        | none => false
termination_by tr => heightOf tr
decreasing_by
  exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨findChild ks x, _hc⟩)

/--
Executable search is sound on every B-tree: a successful result witnesses
membership in the tree, without requiring structural invariants.
-/
theorem searchExec_sound {x : Nat} {tr : BTree}
    (hsearch : searchExec x tr = true) : mem x tr := by
  revert hsearch
  induction tr using searchExec.induct x with
  | case1 ks cs hxkeys =>
      intro _
      unfold mem keysOf
      exact List.mem_append_left _ hxkeys
  | case2 ks cs hxkeys child hchild ih =>
      intro hsearch
      have hchild_search : searchExec x child = true := by
        rw [searchExec, if_neg hxkeys] at hsearch
        split at hsearch
        · rename_i child' hchild'
          rw [hchild] at hchild'
          cases hchild'
          exact hsearch
        · rename_i hnone
          rw [hchild] at hnone
          contradiction
      have hchild_mem : x ∈ keysOf child := ih hchild_search
      unfold mem keysOf
      rw [List.mem_append, List.mem_flatMap]
      right
      exact ⟨child, List.mem_iff_getElem?.mpr ⟨findChild ks x, hchild⟩, hchild_mem⟩
  | case3 ks cs hxkeys hchild =>
      intro hsearch
      rw [searchExec, if_neg hxkeys] at hsearch
      split at hsearch
      · rename_i child hsome
        rw [hchild] at hsome
        contradiction
      · simp at hsearch

/--
On sorted, child-bounded B-trees, executable search is complete: every member
is found by the separator-selected descent path.
-/
theorem searchExec_complete {x : Nat} {tr : BTree}
    (hsorted : Sorted tr) (hbounded : ChildBounded tr)
    (hmem : mem x tr) : searchExec x tr = true := by
  revert hsorted hbounded hmem
  induction tr using searchExec.induct x with
  | case1 ks cs hxkeys =>
      intro _ _ _
      rw [searchExec, if_pos hxkeys]
  | case2 ks cs hxkeys child hchild ih =>
      intro hsorted hbounded hmem
      unfold Sorted at hsorted
      rcases hsorted with ⟨hkeys_sorted, hchildren_sorted⟩
      unfold mem keysOf at hmem
      rw [List.mem_append, List.mem_flatMap] at hmem
      rcases hmem with hxnode | ⟨descendant, hdescendant, hxdescendant⟩
      · exact (hxkeys hxnode).elim
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdescendant
        have hjfind : j = findChild ks x :=
          findChild_localizes_mem hkeys_sorted hbounded hxkeys hj hxdescendant
        subst j
        rw [hchild] at hj
        cases hj
        have hchild_mem : child ∈ cs :=
          List.mem_iff_getElem?.mpr ⟨findChild ks x, hchild⟩
        have hchild_sorted : Sorted child :=
          hchildren_sorted child hchild_mem
        have hchild_bounded : ChildBounded child := by
          unfold ChildBounded at hbounded
          exact hbounded.2.2 child hchild_mem
        have hchild_search : searchExec x child = true :=
          ih hchild_sorted hchild_bounded hxdescendant
        rw [searchExec, if_neg hxkeys]
        split
        · rename_i child' hchild'
          rw [hchild] at hchild'
          cases hchild'
          exact hchild_search
        · rename_i hnone
          rw [hchild] at hnone
          contradiction
  | case3 ks cs hxkeys hchild =>
      intro hsorted hbounded hmem
      unfold Sorted at hsorted
      rcases hsorted with ⟨hkeys_sorted, _⟩
      unfold mem keysOf at hmem
      rw [List.mem_append, List.mem_flatMap] at hmem
      rcases hmem with hxnode | ⟨descendant, hdescendant, hxdescendant⟩
      · exact (hxkeys hxnode).elim
      · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hdescendant
        have hjfind : j = findChild ks x :=
          findChild_localizes_mem hkeys_sorted hbounded hxkeys hj hxdescendant
        rw [hjfind, hchild] at hj
        contradiction

/--
On sorted, child-bounded trees, executable search returns true exactly for
members of the tree.
-/
theorem searchExec_true_iff {x : Nat} {tr : BTree}
    (hsorted : Sorted tr) (hbounded : ChildBounded tr) :
    searchExec x tr = true ↔ mem x tr :=
  ⟨searchExec_sound, searchExec_complete hsorted hbounded⟩

/--
On sorted, child-bounded trees, separator-guided executable search agrees with
the specification-level membership oracle {name}`search`.
-/
theorem searchExec_eq_search {x : Nat} {tr : BTree}
    (hsorted : Sorted tr) (hbounded : ChildBounded tr) :
    searchExec x tr = search x tr := by
  apply Bool.eq_iff_iff.mpr
  exact (searchExec_true_iff hsorted hbounded).trans (search_true_iff x tr).symm

end CLRS.Chapter18.BTree
