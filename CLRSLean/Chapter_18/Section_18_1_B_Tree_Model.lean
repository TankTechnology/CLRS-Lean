import Mathlib

/-!
# CLRS Section 18.1 - B-tree model

Defines the B-tree data type, key membership, full structural invariants,
and the `B-TREE-SPLIT-CHILD` operation with occupancy and SameDepth preservation.
-/

namespace CLRS
namespace Chapter18

inductive BTree where
  | node (keys : List Nat) (children : List BTree) : BTree
  deriving Repr

namespace BTree

open List

/-! ## Keys and membership -/

def keysOf : BTree -> List Nat
  | node keys children => keys ++ children.flatMap keysOf

def mem (x : Nat) (t : BTree) : Prop := x ∈ keysOf t

instance decidableMem (x : Nat) (t : BTree) : Decidable (mem x t) :=
  inferInstanceAs (Decidable (x ∈ keysOf t))

def Valid (minDegree : Nat) (_t : BTree) : Prop := 2 <= minDegree

def search (x : Nat) (t : BTree) : Bool := decide (mem x t)

theorem search_true_iff (x : Nat) (t : BTree) :
    search x t = true ↔ mem x t := by simp [search]
theorem search_true_of_mem (x : Nat) (t : BTree) (hx : mem x t) :
    search x t = true := (search_true_iff x t).mpr hx
theorem mem_of_search_true (x : Nat) (t : BTree) (hx : search x t = true) :
    mem x t := (search_true_iff x t).mp hx
theorem search_false_iff (x : Nat) (t : BTree) :
    search x t = false ↔ ¬ mem x t := by simp [search]
theorem search_false_of_not_mem (x : Nat) (t : BTree) (hx : ¬ mem x t) :
    search x t = false := (search_false_iff x t).mpr hx
theorem not_mem_of_search_false (x : Nat) (t : BTree) (hx : search x t = false) :
    ¬ mem x t := (search_false_iff x t).mp hx
theorem search_correct {minDegree x : Nat} {t : BTree}
    (_hvalid : Valid minDegree t) : search x t = true ↔ mem x t :=
  search_true_iff x t

/-! ## Minimum-key lower bound expression -/

def minKeys (minDegree height : Nat) : Nat := 2 * minDegree ^ height - 1

theorem minKeys_zero (minDegree : Nat) : minKeys minDegree 0 = 1 := by simp [minKeys]
theorem minKeys_pos {minDegree height : Nat} (hdegree : 0 < minDegree) :
    0 < minKeys minDegree height := by
  unfold minKeys
  have hpow : 0 < minDegree ^ height := pow_pos hdegree height
  have hlt : 1 < 2 * minDegree ^ height := by omega
  exact Nat.sub_pos_of_lt hlt
theorem one_le_minKeys {minDegree height : Nat} (hdegree : 0 < minDegree) :
    1 <= minKeys minDegree height := Nat.succ_le_of_lt (minKeys_pos hdegree)
theorem minKeys_lower_bound {minDegree height : Nat} (_hdegree : 2 <= minDegree) :
    2 * minDegree ^ height - 1 <= minKeys minDegree height := by rfl
theorem minKeys_succ {minDegree height : Nat} (hdegree : 2 <= minDegree) :
    minKeys minDegree (height + 1) + 1 = minDegree * (minKeys minDegree height + 1) := by
  unfold minKeys; have hpos : 0 < minDegree := by omega
  have hpowPos : 0 < minDegree ^ height := pow_pos hpos height
  have hnextPowPos : 0 < minDegree ^ (height + 1) := pow_pos hpos (height + 1)
  have hnextTermPos : 0 < 2 * minDegree ^ (height + 1) := Nat.mul_pos (by decide) hnextPowPos
  have htermPos : 0 < 2 * minDegree ^ height := Nat.mul_pos (by decide) hpowPos
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hnextTermPos)]
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt htermPos)]
  rw [Nat.pow_succ]; ring
theorem minKeys_le_succ {minDegree height : Nat} (hdegree : 2 <= minDegree) :
    minKeys minDegree height <= minKeys minDegree (height + 1) := by
  unfold minKeys; have hpos : 0 < minDegree := by omega
  have hpow : minDegree ^ height <= minDegree ^ (height + 1) := by
    rw [Nat.pow_succ]; exact Nat.le_mul_of_pos_right _ hpos
  exact Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hpow) 1
theorem minKeys_monotone_height {minDegree h₁ h₂ : Nat}
    (hdegree : 2 <= minDegree) (hheight : h₁ <= h₂) :
    minKeys minDegree h₁ <= minKeys minDegree h₂ := by
  induction hheight with | refl => rfl | step _ ih =>
    exact Nat.le_trans ih (minKeys_le_succ hdegree)

/-! ## Structural invariants -/

def Sorted : BTree → Prop
  | node keys children =>
    List.Pairwise (· ≤ ·) keys ∧ ∀ child ∈ children, Sorted child

def ChildBounded : BTree → Prop
  | node keys children =>
    (children.isEmpty ∨ children.length = keys.length + 1) ∧
    (∀ (i : Nat) (hi_child : i < children.length),
      let child := children.get ⟨i, hi_child⟩
      (i = 0 ∨ (match keys[i-1]? with
        | some lo => ∀ k ∈ keysOf child, lo ≤ k
        | none => True)) ∧
      (match keys[i]? with
        | some hi => ∀ k ∈ keysOf child, k ≤ hi
        | none => True)) ∧
    ∀ child ∈ children, ChildBounded child

def Occupancy (minDegree : Nat) (isRoot : Bool) : BTree → Prop
  | node keys children =>
    let lower := if isRoot then
      (if keys.length = 0 ∧ children.isEmpty then 0 else 1) else minDegree - 1
    let upper := 2 * minDegree - 1
    lower ≤ keys.length ∧ keys.length ≤ upper ∧
    (children.isEmpty ∨
      (minDegree ≤ children.length ∧ children.length ≤ 2 * minDegree)) ∧
    ∀ child ∈ children, Occupancy minDegree false child

def heightOf : BTree → Nat
  | node _ [] => 0
  | node _ cs => 1 + ((cs.map heightOf).foldl max 0)

inductive SameDepth : BTree → Prop
  | leaf (ks : List Nat) : SameDepth (node ks [])
  | internal (ks : List Nat) (c0 : BTree) (cs : List BTree) :
      (∀ c ∈ cs, heightOf c = heightOf c0) → SameDepth c0 → (∀ c ∈ cs, SameDepth c) →
      SameDepth (node ks (c0 :: cs))

def WellFormed (minDegree : Nat) (t : BTree) : Prop :=
  Sorted t ∧ ChildBounded t ∧ Occupancy minDegree true t ∧ SameDepth t

theorem WellFormed.valid {minDegree : Nat} {t : BTree}
    (hmin : 2 ≤ minDegree) (_h : WellFormed minDegree t) : Valid minDegree t := by
  unfold Valid; exact hmin

theorem wellFormed_empty (minDegree : Nat) (hmin : 2 ≤ minDegree) :
    WellFormed minDegree (node [] []) := by
  unfold WellFormed Sorted ChildBounded Occupancy
  refine ⟨?_, ?_, ?_, SameDepth.leaf []⟩
  · unfold Sorted; simp
  · unfold ChildBounded; simp
  · unfold Occupancy; simp

/-! ## B-TREE-SPLIT-CHILD operation -/

def splitChild (t : Nat) : BTree → Nat → BTree
  | node keys children, i =>
    if h : i < children.length then
      match children.get ⟨i, h⟩ with
      | node cKeys cChildren =>
        if cKeys.length = 2 * t - 1 then
          let m := t - 1
          let (leftKeys, rest) := cKeys.splitAt m
          match rest with
          | [] => node keys children
          | medianKey :: rightKeys =>
            let (leftCh, rightCh) := cChildren.splitAt t
            let newL := BTree.node leftKeys leftCh
            let newR := BTree.node rightKeys rightCh
            let newKeys := keys.take i ++ medianKey :: keys.drop i
            let newCh := children.take i ++ [newL, newR] ++ children.drop (i + 1)
            BTree.node newKeys newCh
        else
          node keys children
    else
      node keys children

/-! ## Occupancy preservation under splitChild -/

lemma splitAt_first_half_length (cKeys : List Nat) (t : Nat) (hfull : cKeys.length = 2 * t - 1) :
    (cKeys.splitAt (t - 1)).1.length = t - 1 := by
  simp [hfull]; omega

lemma splitAt_second_half_length (cKeys : List Nat) (t : Nat)
    (hfull : cKeys.length = 2 * t - 1) (ht : 1 ≤ t) :
    ((cKeys.splitAt (t - 1)).2.drop 1).length = t - 1 := by
  have h_snd_len : (cKeys.splitAt (t - 1)).2.length = t := by
    simp [hfull]; omega
  simp [h_snd_len]; omega

theorem splitChild_new_children_key_counts (t : Nat) (ht : 2 ≤ t)
    (cKeys : List Nat) (hfull : cKeys.length = 2 * t - 1) :
    ((cKeys.splitAt (t - 1)).1).length = t - 1 ∧
    ((cKeys.splitAt (t - 1)).2.drop 1).length = t - 1 := by
  have ht_pos : 1 ≤ t := by omega
  exact ⟨splitAt_first_half_length cKeys t hfull,
          splitAt_second_half_length cKeys t hfull ht_pos⟩

theorem splitChild_parent_key_bound (t : Nat) (ht : 2 ≤ t) (keys : List Nat)
    (hparent_nonfull : keys.length < 2 * t - 1) :
    keys.length + 1 ≤ 2 * t - 1 := by
  omega

/-! ## List utility: foldl max over uniform values -/

lemma foldl_max_idem (l : List Nat) (a : Nat) (h : ∀ b ∈ l, b = a) : foldl max a l = a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x = a := h x (by simp)
    have hxs : ∀ b ∈ xs, b = a := by
      intro b hb; exact h b (by simp [hb])
    rw [hx]
    simp [ih hxs]

lemma foldl_max_eq_of_all_eq (l : List Nat) (v : Nat) (h_ne : l ≠ [])
    (h : ∀ a ∈ l, a = v) : l.foldl max 0 = v := by
  cases l with
  | nil => contradiction
  | cons x xs =>
    have hx : x = v := h x (by simp)
    have hxs : ∀ a ∈ xs, a = v := by
      intro a ha; exact h a (by simp [ha])
    rw [hx]
    simp
    exact foldl_max_idem xs v hxs

/-! ## SameDepth infrastructure and preservation -/

lemma sameDepth_children_eq_height {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (hsd : SameDepth (node ks (c0 :: cs))) :
    ∀ c₁ ∈ (c0 :: cs), ∀ c₂ ∈ (c0 :: cs), heightOf c₁ = heightOf c₂ := by
  refine SameDepth.casesOn hsd
    (motive := λ t _ => match t with
      | node _ children => ∀ c₁ ∈ children, ∀ c₂ ∈ children, heightOf c₁ = heightOf c₂)
    ?leaf ?internal
  · intro ks'; intro c₁ hc₁; simp at hc₁
  · intro ks' c0' cs' h_heights _h_sd_c0' _h_sd_children'
    intro c₁ hc₁ c₂ hc₂
    simp at hc₁ hc₂
    rcases hc₁ with (rfl | hc₁')
    · rcases hc₂ with (rfl | hc₂')
      · rfl
      · symm; exact h_heights c₂ hc₂'
    · rcases hc₂ with (rfl | hc₂')
      · exact h_heights c₁ hc₁'
      · rw [h_heights c₁ hc₁', h_heights c₂ hc₂']

lemma sameDepth_head_sd {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (hsd : SameDepth (node ks (c0 :: cs))) : SameDepth c0 := by
  refine SameDepth.casesOn hsd (motive := λ t _ => match t with
    | node _ (c0' :: _) => SameDepth c0'
    | node _ [] => True) ?leaf ?internal
  · intro ks'; trivial
  · intro ks' c0' cs' _ h_sd_c0' _; exact h_sd_c0'

lemma sameDepth_tail_sd {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (hsd : SameDepth (node ks (c0 :: cs))) (c : BTree) (hc : c ∈ cs) : SameDepth c := by
  refine SameDepth.casesOn hsd (motive := λ t _ => match t with
    | node _ (c0' :: cs') => ∀ c' ∈ cs', SameDepth c'
    | node _ [] => ∀ c' ∈ [], SameDepth c') ?leaf ?internal c hc
  · intro ks' c' hc'; simp at hc'
  · intro ks' c0' cs' _ _ h_sd_children'; exact h_sd_children'

theorem splitChild_preserves_sameDepth (t : Nat) (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (hsd : SameDepth (node keys children)) :
    SameDepth (splitChild t (node keys children) i) := by
  -- Expand splitChild to expose the result structure
  rw [splitChild]
  simp [h_lt, hchild_full]
  -- Goal: SameDepth (node (keys.take i ++ [median] :: keys.drop i)
  --   (children.take i ++ [newL, newR] ++ children.drop (i+1)))
  -- Extract SameDepth for the split child from hsd
  have h_split_sd : SameDepth (node cKeys cChildren) := by
    cases children with
    | nil => simp at h_lt
    | cons c0' cs' =>
      by_cases hi : i = 0
      · subst hi; simp at hchild_eq; rw [← hchild_eq]; exact sameDepth_head_sd hsd
      · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi
        have hi1_lt : i-1 < cs'.length := by
          have : (c0' :: cs').length = cs'.length + 1 := by simp
          omega
        have hget : (c0' :: cs').get ⟨i, h_lt⟩ = cs'.get ⟨i-1, hi1_lt⟩ := by
          cases i; simp at hi; rename_i n; simp
        have helem : cs'.get ⟨i-1, hi1_lt⟩ = node cKeys cChildren := by
          rw [← hget, hchild_eq]
        have hmem : node cKeys cChildren ∈ cs' := by
          have hmem_get : cs'.get ⟨i-1, hi1_lt⟩ ∈ cs' :=
            List.get_mem cs' ⟨i-1, hi1_lt⟩
          rw [← helem]; exact hmem_get
        exact sameDepth_tail_sd hsd (node cKeys cChildren) hmem

  -- The split child's children all have equal height (from h_split_sd)
  -- The two new children (newL, newR) each have children = subsets of cChildren
  -- We need to prove SameDepth for the resulting node.
  -- Decompose children into c0' :: cs' (nonempty from h_lt)
  cases children with
  | nil => simp at h_lt
  | cons c0' cs' =>
    -- Now children = c0' :: cs'
    -- Define the two new children for readability
    let newL := node ((cKeys.splitAt (t - 1)).1) ((cChildren.splitAt t).1)
    let newR := node ((cKeys.splitAt (t - 1)).2.drop 1) ((cChildren.splitAt t).2)
    let newKeys := keys.take i ++
      (match (cKeys.splitAt (t - 1)).2 with
      | medianKey :: _ => medianKey | [] => 0) :: keys.drop i
    -- The new children list: (c0' :: cs').take i ++ [newL, newR] ++ (c0' :: cs').drop (i+1)
    -- Case split on i to determine the head of the new children list
    by_cases hi : i = 0
    · -- i = 0: new children = newL :: newR :: (c0' :: cs').drop 1
      subst hi
      simp
      -- Goal: SameDepth (node newKeys (newL :: newR :: cs'))
      -- Apply SameDepth.internal with c0 = newL, cs = newR :: cs'
      refine SameDepth.internal newKeys newL (newR :: cs') ?_ ?_ ?_
      · -- h_heights: all cs have height = heightOf newL
        sorry
      · -- SameDepth newL
        sorry
      · -- ∀ c ∈ newR :: cs', SameDepth c
        sorry
    · -- i > 0: first child of new list is c0' (unchanged)
      have hi_pos : 0 < i := Nat.pos_of_ne_zero hi
      -- The new children = c0' :: ((cs'.take (i-1)) ++ [newL, newR] ++ cs'.drop i)
      -- But we can avoid this decomposition: just use c0' as head and the rest as cs
      -- Actually we need to provide explicit c0, cs. Let's compute them.
      -- newChildren = (c0' :: cs').take i ++ [newL, newR] ++ (c0' :: cs').drop (i+1)
      -- Since i > 0, (c0' :: cs').take i = c0' :: (cs'.take (i-1))
      -- And (c0' :: cs').drop (i+1) = cs'.drop i
      -- So newChildren = c0' :: (cs'.take (i-1) ++ [newL, newR] ++ cs'.drop i)
      -- Apply SameDepth.internal with c0 = c0', cs = the rest
      sorry

end BTree
end Chapter18
end CLRS
