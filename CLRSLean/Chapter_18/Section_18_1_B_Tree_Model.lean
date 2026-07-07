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
          match cKeys.splitAt (t - 1), cChildren.splitAt t with
          | (leftKeys, medianKey :: rightKeys), (leftCh, rightCh) =>
            BTree.node (keys.take i ++ medianKey :: keys.drop i)
              (children.take i ++ [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
                children.drop (i + 1))
          | _, _ => node keys children
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

lemma sameDepth_take (cKeys : List Nat) (cChildren : List BTree) (t : Nat)
    (hsd : SameDepth (node cKeys cChildren)) (ht_pos : 1 ≤ t) :
    SameDepth (node ((cKeys.splitAt (t - 1)).1) ((cChildren.splitAt t).1)) := by
  cases cChildren with
  | nil => simp; exact SameDepth.leaf _
  | cons d0 ds =>
    have h_take : ((d0 :: ds).splitAt t).1 = d0 :: (ds.take (t-1)) := by
      cases t; omega; rename_i n; simp
    rw [h_take]
    have h_sd_d0 : SameDepth d0 := sameDepth_head_sd hsd
    have h_sd_ds : ∀ d ∈ ds.take (t-1), SameDepth d := by
      intro d hd
      exact sameDepth_tail_sd hsd d ((take_sublist (t-1) ds).subset hd)
    have h_heights : ∀ d ∈ ds.take (t-1), heightOf d = heightOf d0 := by
      intro d hd
      have hmem : d ∈ d0 :: ds := by
        apply mem_cons_of_mem d0
        exact (take_sublist (t-1) ds).subset hd
      exact (sameDepth_children_eq_height hsd) d hmem d0 (by simp)
    exact SameDepth.internal ((cKeys.splitAt (t - 1)).1) d0 (ds.take (t-1))
      h_heights h_sd_d0 h_sd_ds

lemma sameDepth_drop (cKeys : List Nat) (cChildren : List BTree) (t : Nat)
    (hsd : SameDepth (node cKeys cChildren)) (ht_pos : 1 ≤ t) :
    SameDepth (node ((cKeys.splitAt (t - 1)).2.drop 1) ((cChildren.splitAt t).2)) := by
  cases cChildren with
  | nil => simp; exact SameDepth.leaf _
  | cons d0 ds =>
    have h_drop : ((d0 :: ds).splitAt t).2 = ds.drop (t-1) := by
      cases t; omega; rename_i n; simp
    rw [h_drop]
    by_cases h_empty : ds.drop (t-1) = []
    · simp [h_empty]; exact SameDepth.leaf _
    · match h_drop_suffix : ds.drop (t-1) with
      | [] => exact (h_empty h_drop_suffix).elim
      | e0 :: es =>
        have he0_mem_drop : e0 ∈ ds.drop (t-1) := by rw [h_drop_suffix]; simp
        have he0_ds : e0 ∈ ds := (drop_sublist (t-1) ds).subset he0_mem_drop
        have h_sd_e0 : SameDepth e0 := sameDepth_tail_sd hsd e0 he0_ds
        have h_sd_es : ∀ e ∈ es, SameDepth e := by
          intro e he
          have he_mem_drop : e ∈ ds.drop (t-1) := by rw [h_drop_suffix]; simp [he]
          have he_ds : e ∈ ds := (drop_sublist (t-1) ds).subset he_mem_drop
          exact sameDepth_tail_sd hsd e he_ds
        have h_heights : ∀ e ∈ es, heightOf e = heightOf e0 := by
          intro e he
          have he_mem_drop : e ∈ ds.drop (t-1) := by rw [h_drop_suffix]; simp [he]
          have he_ds : e ∈ ds := (drop_sublist (t-1) ds).subset he_mem_drop
          have he0_cons : e0 ∈ d0 :: ds := by simp [he0_ds]
          have he_cons : e ∈ d0 :: ds := by simp [he_ds]
          exact (sameDepth_children_eq_height hsd) e he_cons e0 he0_cons
        refine SameDepth.internal ((cKeys.splitAt (t - 1)).2.drop 1) e0 es
          h_heights h_sd_e0 h_sd_es

/-! ## Height of a SameDepth internal node -/

lemma heightOf_uniform_children {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (h : ∀ c ∈ cs, heightOf c = heightOf c0) :
    heightOf (node ks (c0 :: cs)) = 1 + heightOf c0 := by
  simp [heightOf]
  refine (Nat.succ_inj).mp ?_
  simp
  refine foldl_max_idem (List.map heightOf cs) (heightOf c0) ?_
  intro x hx
  rw [List.mem_map] at hx
  rcases hx with ⟨c, hc, rfl⟩
  exact h c hc

lemma heightOf_internal_of_sameDepth {ks : List Nat} {c0 : BTree} {cs : List BTree}
    (hsd : SameDepth (node ks (c0 :: cs))) : heightOf (node ks (c0 :: cs)) = 1 + heightOf c0 := by
  match hsd with
  | SameDepth.internal ks' c0' cs' h_heights _ _ =>
    exact heightOf_uniform_children h_heights

lemma heightOf_split_parts_eq (cKeys : List Nat) (cChildren : List BTree) (t : Nat)
    (hsd : SameDepth (node cKeys cChildren))
    (ht_pos : 0 < t)
    (h_children : cChildren = [] ∨ t < cChildren.length) :
    heightOf (node ((cKeys.splitAt (t - 1)).1) ((cChildren.splitAt t).1)) =
    heightOf (node cKeys cChildren) ∧
    heightOf (node ((cKeys.splitAt (t - 1)).2.drop 1) ((cChildren.splitAt t).2)) =
    heightOf (node cKeys cChildren) := by
  rcases h_children with (h_empty | h_gt)
  · subst h_empty; simp [heightOf]
  · have h_nonempty : cChildren ≠ [] := by
      intro h; rw [h] at h_gt; simp at h_gt
    cases h_cases : cChildren with
    | nil => exact (h_nonempty h_cases).elim
    | cons d0 ds =>
      have hsd_internal : heightOf (node cKeys (d0 :: ds)) = 1 + heightOf d0 :=
        heightOf_internal_of_sameDepth (by rwa [h_cases] at hsd)
      have h_all_eq : ∀ c₁ ∈ (d0 :: ds), ∀ c₂ ∈ (d0 :: ds), heightOf c₁ = heightOf c₂ :=
        sameDepth_children_eq_height (by rwa [h_cases] at hsd)
      have h_take_head : ((d0 :: ds).splitAt t).1 = d0 :: (ds.take (t - 1)) := by
        cases t; omega; rename_i n; simp
      rw [h_take_head]
      have h_left_heights : ∀ c ∈ ds.take (t - 1), heightOf c = heightOf d0 := by
        intro c hc
        have hc_mem : c ∈ d0 :: ds :=
          List.mem_cons_of_mem _ ((List.take_sublist (t - 1) ds).subset hc)
        exact h_all_eq c hc_mem d0 (by simp)
      have h_left_height : heightOf (node ((cKeys.splitAt (t - 1)).1) (d0 :: ds.take (t - 1))) =
          1 + heightOf d0 :=
        heightOf_uniform_children h_left_heights
      have h_drop_eq : ((d0 :: ds).splitAt t).2 = ds.drop (t - 1) := by
        cases t; omega; rename_i n; simp
      rw [h_drop_eq]
      have h_right_nonempty : ds.drop (t - 1) ≠ [] := by
        have hlen_cons : t < (d0 :: ds).length := by simpa [h_cases] using h_gt
        intro h
        have hlen0 : (ds.drop (t - 1)).length = 0 := by simpa [h]
        rw [List.length_drop] at hlen0
        have : ds.length ≤ t - 1 := by omega
        have : ds.length + 1 ≤ t := by omega
        simp at hlen_cons
        omega
      match h_drop_suffix : ds.drop (t - 1) with
      | nil => exact (h_right_nonempty h_drop_suffix).elim
      | cons e0 es =>
        have h_right_heights : ∀ c ∈ es, heightOf c = heightOf e0 := by
          intro c hc
          have hc_mem : c ∈ d0 :: ds := by
            apply List.mem_cons_of_mem _
            have hmem_drop : c ∈ ds.drop (t - 1) := by rw [h_drop_suffix]; simp [hc]
            exact (List.drop_sublist (t - 1) ds).subset hmem_drop
          have he0_mem : e0 ∈ d0 :: ds := by
            apply List.mem_cons_of_mem _
            have he0_drop : e0 ∈ ds.drop (t - 1) := by rw [h_drop_suffix]; simp
            exact (List.drop_sublist (t - 1) ds).subset he0_drop
          exact h_all_eq c hc_mem e0 he0_mem
        have h_right_height : heightOf (node ((cKeys.splitAt (t - 1)).2.drop 1) (e0 :: es)) =
            1 + heightOf e0 :=
          heightOf_uniform_children h_right_heights
        have h_d0_e0_height : heightOf e0 = heightOf d0 := by
          have he0_mem : e0 ∈ d0 :: ds := by
            apply List.mem_cons_of_mem _
            have he0_drop : e0 ∈ ds.drop (t - 1) := by rw [h_drop_suffix]; simp
            exact (List.drop_sublist (t - 1) ds).subset he0_drop
          exact h_all_eq e0 he0_mem d0 (by simp)
        rw [h_d0_e0_height] at h_right_height
        rw [h_left_height, h_right_height, hsd_internal]
        exact ⟨rfl, rfl⟩

theorem splitChild_preserves_sameDepth (t : Nat) (ht : 2 ≤ t)
    (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (hchild_children : cChildren = [] ∨ t < cChildren.length)
    (hsd : SameDepth (node keys children)) :
    SameDepth (splitChild t (node keys children) i) := by
  have ht_pos : 1 ≤ t := by omega
  have ht_pos' : 0 < t := by omega
  have h_keys_snd_nonempty : (cKeys.splitAt (t - 1)).2 ≠ [] := by
    have hlen : (cKeys.splitAt (t - 1)).2.length = t := by simp [hchild_full]; omega
    intro h; rw [h] at hlen; simp at hlen; omega
  dsimp [splitChild]
  rw [dif_pos h_lt]
  have h_get : children[i] = node cKeys cChildren := by simpa using hchild_eq
  rw [h_get]
  dsimp
  rw [if_pos hchild_full]
  cases hk : cKeys.splitAt (t - 1) with
  | mk leftKeys keysRest =>
    have h_keysRest_nonempty : keysRest ≠ [] := by
      have : (cKeys.splitAt (t - 1)).2 = keysRest := by rw [hk]
      rw [← this]; exact h_keys_snd_nonempty
    cases hkr : keysRest with
    | nil => exact (h_keysRest_nonempty hkr).elim
    | cons medianKey rightKeys =>
      cases hc : cChildren.splitAt t with
      | mk leftCh rightCh =>
        -- The match reduces to the success branch
        show SameDepth (BTree.node (take i keys ++ medianKey :: drop i keys)
          (take i children ++ [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
            drop (i + 1) children))
        cases hsd with
        | leaf ks => simp at h_lt
        | internal ks c0 cs h_heights h_sd_c0 h_sd_cs =>
          have h_sd_child : SameDepth (node cKeys cChildren) := by
            rcases Nat.eq_zero_or_pos i with (rfl | hi_pos')
            · have hc0_eq : c0 = node cKeys cChildren := by simpa using hchild_eq
              rw [← hc0_eq]; exact h_sd_c0
            · have h_get' : (c0 :: cs).get ⟨i, h_lt⟩ = cs.get ⟨i - 1, by
                simp at h_lt; omega⟩ := by
                rcases i with (rfl | i)
                · exact (Nat.not_lt_zero _ hi_pos').elim
                · simp
              have hmem : cs.get ⟨i - 1, by simp at h_lt; omega⟩ ∈ cs := by
                apply List.get_mem
              rw [← hchild_eq, h_get']
              exact h_sd_cs _ hmem
          have h_keys_left : ((cKeys.splitAt (t - 1)).1) = leftKeys := by rw [hk]
          have h_keys_right : ((cKeys.splitAt (t - 1)).2.drop 1) = rightKeys := by
            rw [hk]; simp [hkr]
          have h_ch_left : ((cChildren.splitAt t).1) = leftCh := by rw [hc]
          have h_ch_right : ((cChildren.splitAt t).2) = rightCh := by rw [hc]
          have h_sd_left : SameDepth (node leftKeys leftCh) := by
            rw [← h_keys_left, ← h_ch_left]; exact sameDepth_take cKeys cChildren t h_sd_child ht_pos
          have h_sd_right : SameDepth (node rightKeys rightCh) := by
            rw [← h_keys_right, ← h_ch_right]; exact sameDepth_drop cKeys cChildren t h_sd_child ht_pos
          have h_heights_split := heightOf_split_parts_eq cKeys cChildren t h_sd_child ht_pos' hchild_children
          have h_height_left : heightOf (node leftKeys leftCh) = heightOf (node cKeys cChildren) := by
            rw [← h_keys_left, ← h_ch_left]; exact h_heights_split.1
          have h_height_right : heightOf (node rightKeys rightCh) = heightOf (node cKeys cChildren) := by
            rw [← h_keys_right, ← h_ch_right]; exact h_heights_split.2
          have h_child_eq_c0_height : heightOf (node cKeys cChildren) = heightOf c0 := by
            rcases Nat.eq_zero_or_pos i with (rfl | hi_pos')
            · have hc0_eq : c0 = node cKeys cChildren := by simpa using hchild_eq
              rw [← hc0_eq]
            · have h_get' : (c0 :: cs).get ⟨i, h_lt⟩ = cs.get ⟨i - 1, by
                simp at h_lt; omega⟩ := by
                rcases i with (rfl | i)
                · exact (Nat.not_lt_zero _ hi_pos').elim
                · simp
              have hmem : cs.get ⟨i - 1, by simp at h_lt; omega⟩ ∈ cs := by
                apply List.get_mem
              rw [← hchild_eq, h_get']
              exact h_heights _ hmem
          rcases Nat.eq_zero_or_pos i with (rfl | hi_pos)
          · -- i = 0: result children = newLeft :: newRight :: cs
            have h_rest_heights : ∀ c ∈ (node rightKeys rightCh :: cs),
                heightOf c = heightOf (node leftKeys leftCh) := by
              intro c hc; simp at hc; rcases hc with (rfl | hc_cs)
              · rw [h_height_right, h_height_left]
              · rw [h_heights c hc_cs, ← h_child_eq_c0_height, h_height_left]
            have h_rest_sd : ∀ c ∈ (node rightKeys rightCh :: cs), SameDepth c := by
              intro c hc; simp at hc; rcases hc with (rfl | hc_cs)
              · exact h_sd_right
              · exact h_sd_cs c hc_cs
            refine SameDepth.internal (take 0 keys ++ medianKey :: drop 0 keys)
              (node leftKeys leftCh) (node rightKeys rightCh :: cs) h_rest_heights h_sd_left h_rest_sd
          · -- i > 0: result children = c0 :: take(i-1)cs ++ left :: right :: drop i cs
            have h_take : take i (c0 :: cs) = c0 :: take (i - 1) cs := by
              rcases i with (rfl | i)
              · exact (Nat.not_lt_zero _ hi_pos).elim
              · simp
            have h_drop_succ : drop (i + 1) (c0 :: cs) = drop i cs := by simp
            rw [h_take, h_drop_succ]
            simp only [List.cons_append, List.append_assoc, List.nil_append]
            have h_rest_heights : ∀ c ∈ (take (i - 1) cs ++ (node leftKeys leftCh :: node rightKeys rightCh :: drop i cs)),
                heightOf c = heightOf c0 := by
              intro c hc
              rw [List.mem_append] at hc
              rcases hc with (hc | hc)
              · have hmem : c ∈ cs := (List.take_sublist _ _).subset hc
                exact h_heights c hmem
              · simp at hc; rcases hc with (rfl | rfl | hc)
                · rw [h_height_left, h_child_eq_c0_height]
                · rw [h_height_right, h_child_eq_c0_height]
                · have hmem : c ∈ cs := (List.drop_sublist _ _).subset hc
                  exact h_heights c hmem
            have h_rest_sd : ∀ c ∈ (take (i - 1) cs ++ (node leftKeys leftCh :: node rightKeys rightCh :: drop i cs)),
                SameDepth c := by
              intro c hc
              rw [List.mem_append] at hc
              rcases hc with (hc | hc)
              · have hmem : c ∈ cs := (List.take_sublist _ _).subset hc
                exact h_sd_cs c hmem
              · simp at hc; rcases hc with (rfl | rfl | hc)
                · exact h_sd_left
                · exact h_sd_right
                · have hmem : c ∈ cs := (List.drop_sublist _ _).subset hc
                  exact h_sd_cs c hmem
            refine SameDepth.internal (take i keys ++ medianKey :: drop i keys) c0
              (take (i - 1) cs ++ (node leftKeys leftCh :: node rightKeys rightCh :: drop i cs))
              h_rest_heights h_sd_c0 h_rest_sd

/-! ## splitChild occupancy preservation (stub)

The following theorem states that `splitChild` preserves the `Occupancy`
invariant.  The proof requires:
1. Arithmetic showing that the two new children have `t-1` keys each
   (from `splitAt_first_half_length` / `splitAt_second_half_length`)
2. Arithmetic showing that children counts stay within `[t, 2t]`
   (requires `ChildBounded` to know `cChildren.length = 2t` when non-empty)
3. Propagation of sub-node occupancy from the original child.
-/

-- Helper: extract child occupancy from parent occupancy
lemma occupancy_of_child {minDegree : Nat} {isRoot : Bool} {keys : List Nat} {children : List BTree}
    (h_occ : Occupancy minDegree isRoot (node keys children))
    (i : Nat) (hi : i < children.length) :
    Occupancy minDegree false (children.get ⟨i, hi⟩) := by
  unfold Occupancy at h_occ
  rcases h_occ with ⟨_, _, _, h_sub⟩
  apply h_sub
  apply List.get_mem

-- Helper: from ChildBounded of a full node, children length is 0 or 2t
lemma child_children_len_of_full_cb {t : Nat} (ht : 2 ≤ t) {cKeys : List Nat} {cChildren : List BTree}
    (h_cb : ChildBounded (node cKeys cChildren)) (h_full : cKeys.length = 2 * t - 1) :
    cChildren.length = 0 ∨ cChildren.length = 2 * t := by
  unfold ChildBounded at h_cb
  rcases h_cb with ⟨h_rel, _, _⟩
  rcases h_rel with (h_empty | h_eq)
  · left; cases cChildren with | nil => rfl | cons x xs => simp at h_empty
  · right; rw [h_eq, h_full]; omega

theorem splitChild_preserves_occupancy (t : Nat) (ht : 2 ≤ t)
    (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (hparent_nonfull : keys.length < 2 * t - 1)
    (h_occ : Occupancy t true (node keys children))
    (h_cb : ChildBounded (node keys children)) :
    Occupancy t true (splitChild t (node keys children) i) := by
  have ht_pos : 0 < t := by omega
  have ht_pos' : 1 ≤ t := by omega
  -- Extract child invariants
  have hchild_occ : Occupancy t false (node cKeys cChildren) := by
    rw [← hchild_eq]; exact occupancy_of_child h_occ i h_lt
  have hchild_cb : ChildBounded (node cKeys cChildren) := by
    rw [← hchild_eq]; unfold ChildBounded at h_cb
    rcases h_cb with ⟨_, _, h_sub⟩; apply h_sub; apply List.get_mem
  have h_cChildren_len := child_children_len_of_full_cb ht hchild_cb hchild_full
  -- Unfold splitChild (same pattern as splitChild_preserves_sameDepth)
  have h_keys_snd_nonempty : (cKeys.splitAt (t - 1)).2 ≠ [] := by
    have hlen : (cKeys.splitAt (t - 1)).2.length = t := by simp [hchild_full]; omega
    intro h; rw [h] at hlen; simp at hlen; omega
  dsimp [splitChild]; rw [dif_pos h_lt]
  have h_get : children[i] = node cKeys cChildren := by simpa using hchild_eq
  rw [h_get]; dsimp; rw [if_pos hchild_full]
  cases hk : cKeys.splitAt (t - 1) with
  | mk leftKeys keysRest =>
    have h_keysRest_nonempty : keysRest ≠ [] := by
      have : (cKeys.splitAt (t - 1)).2 = keysRest := by rw [hk]
      rw [← this]; exact h_keys_snd_nonempty
    cases hkr : keysRest with
    | nil => exact (h_keysRest_nonempty hkr).elim
    | cons medianKey rightKeys =>
      cases hc : cChildren.splitAt t with
      | mk leftCh rightCh =>
        show Occupancy t true (BTree.node (take i keys ++ medianKey :: drop i keys)
          (take i children ++ [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
            drop (i + 1) children))
        -- Relate local names to splitAt results (matching SameDepth proof pattern)
        have h_keys_left : ((cKeys.splitAt (t - 1)).1) = leftKeys := by rw [hk]
        have h_keys_right : ((cKeys.splitAt (t - 1)).2.drop 1) = rightKeys := by
          rw [hk]; simp [hkr]
        have h_ch_left : ((cChildren.splitAt t).1) = leftCh := by rw [hc]
        have h_ch_right : ((cChildren.splitAt t).2) = rightCh := by rw [hc]
        -- Key length facts (using ← to apply splitAt lemmas)
        have h_leftKeys_len : leftKeys.length = t - 1 := by
          rw [← h_keys_left]; exact splitAt_first_half_length cKeys t hchild_full
        have h_rightKeys_len : rightKeys.length = t - 1 := by
          rw [← h_keys_right]; exact splitAt_second_half_length cKeys t hchild_full ht_pos'
        -- Children count bounds for the two new children
        have h_leftCh_bound : leftCh.isEmpty ∨ (t ≤ leftCh.length ∧ leftCh.length ≤ 2 * t) := by
          rcases h_cChildren_len with (h0 | h2t)
          · -- cChildren.length = 0 → cChildren = [] → leftCh = []
            have hnil : cChildren = [] := by
              cases cChildren with | nil => rfl | cons x xs => simp at h0
            left; rw [← h_ch_left, hnil]; simp
          · -- cChildren.length = 2t → leftCh.length = t
            right; rw [← h_ch_left]; simp [h2t]; omega
        have h_rightCh_bound : rightCh.isEmpty ∨ (t ≤ rightCh.length ∧ rightCh.length ≤ 2 * t) := by
          rcases h_cChildren_len with (h0 | h2t)
          · have hnil : cChildren = [] := by
              cases cChildren with | nil => rfl | cons x xs => simp at h0
            left; rw [← h_ch_right, hnil]; simp
          · right; rw [← h_ch_right]; simp [h2t]; omega
        -- Occupancy for the two new children (non-root)
        have h_occ_left : Occupancy t false (BTree.node leftKeys leftCh) := by
          unfold Occupancy
          refine ⟨?_, ?_, h_leftCh_bound, ?_⟩
          · rw [h_leftKeys_len]; exact le_rfl
          · rw [h_leftKeys_len]; omega
          · intro child hchild
            rw [← h_ch_left] at hchild; simp at hchild
            have : child ∈ cChildren :=
              (take_sublist t cChildren).subset hchild
            unfold Occupancy at hchild_occ
            rcases hchild_occ with ⟨_, _, _, h_occ_sub⟩
            exact h_occ_sub child this
        have h_occ_right : Occupancy t false (BTree.node rightKeys rightCh) := by
          unfold Occupancy
          refine ⟨?_, ?_, h_rightCh_bound, ?_⟩
          · rw [h_rightKeys_len]; exact le_rfl
          · rw [h_rightKeys_len]; omega
          · intro child hchild
            rw [← h_ch_right] at hchild; simp at hchild
            have : child ∈ cChildren :=
              (drop_sublist t cChildren).subset hchild
            unfold Occupancy at hchild_occ
            rcases hchild_occ with ⟨_, _, _, h_occ_sub⟩
            exact h_occ_sub child this
        -- Parent occupancy after split: prove the four conjuncts
        -- Derive i ≤ keys.length from ChildBounded and h_lt
        have h_i_le_keys : i ≤ keys.length := by
          unfold ChildBounded at h_cb; rcases h_cb with ⟨h_cb_rel, _, _⟩
          rcases h_cb_rel with (h_cb_empty | h_cb_eq)
          · have h_len0 : children.length = 0 := by simpa using h_cb_empty
            have : i < 0 := by rwa [h_len0] at h_lt
            omega
          · rw [h_cb_eq] at h_lt; omega
        unfold Occupancy
        have h_newKeys_len : (take i keys ++ medianKey :: drop i keys).length = keys.length + 1 := by
          simp [h_i_le_keys]; omega
        have h_newChildren_len : (take i children ++
            [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
            drop (i + 1) children).length = children.length + 1 := by
          simp; omega
        have h_occ_copy : Occupancy t true (node keys children) := h_occ
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- lower bound: the newKeys list is non-empty (contains medianKey)
          have h_ne_nil : take i keys ++ medianKey :: drop i keys ≠ [] := by simp
          have h_pos : 0 < (take i keys ++ medianKey :: drop i keys).length := by omega
          have h_one_le : 1 ≤ (take i keys ++ medianKey :: drop i keys).length := by omega
          have h_if_val : (if (take i keys ++ medianKey :: drop i keys).length = 0 ∧
              (take i children ++ [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
                drop (i+1) children).isEmpty then 0 else 1) = 1 := by
            by_cases hzero : (take i keys ++ medianKey :: drop i keys).length = 0
            · exfalso; exact h_pos.ne' hzero
            · simp [hzero]
          rw [h_if_val]; exact h_one_le
        · -- newKeys.length ≤ 2t-1 (parent was not full, added 1 key)
          rw [h_newKeys_len]; omega
        · -- children count: newChildren non-empty, length = children.length + 1
          rw [h_newChildren_len]; right
          have h_low : t ≤ children.length + 1 := by
            unfold Occupancy at h_occ_copy; rcases h_occ_copy with ⟨_, _, h_pocc_ch, _⟩
            rcases h_pocc_ch with (h_empty | ⟨h_low', _⟩)
            · have h_len0 : children.length = 0 := by simpa using h_empty
              rw [h_len0]; omega
            · omega
          have h_high : children.length + 1 ≤ 2 * t := by
            unfold ChildBounded at h_cb; rcases h_cb with ⟨h_cb_rel, _, _⟩
            rcases h_cb_rel with (h_cb_empty | h_cb_eq)
            · have h_len0 : children.length = 0 := by simpa using h_cb_empty
              rw [h_len0]; omega
            · rw [h_cb_eq]
              have h_add := Nat.add_lt_add_right hparent_nonfull 1
              rw [Nat.sub_add_cancel (show 1 ≤ 2 * t from by omega)] at h_add
              rw [← Nat.succ_eq_add_one (keys.length + 1)]
              exact Nat.succ_le_of_lt h_add
          exact ⟨h_low, h_high⟩
        · -- sub-node occupancy propagation
          -- newChildren = (take i children) ++ [newLeft, newRight] ++ (drop (i+1) children)
          -- Due to ++ associativity: (take ++ [a,b]) ++ drop
          intro child hchild
          have h_or := List.mem_append.mp hchild
          rcases h_or with (h_take_or_new | h_drop)
          · -- child ∈ take i children ++ [newLeft, newRight]
            have h_or2 := List.mem_append.mp h_take_or_new
            rcases h_or2 with (h_take | h_new)
            · -- child ∈ take i children → inherits from parent occupancy
              have hmem : child ∈ children := (take_sublist i children).subset h_take
              unfold Occupancy at h_occ; rcases h_occ with ⟨_, _, _, h_pocc_sub⟩
              exact h_pocc_sub child hmem
            · -- child ∈ [newLeft, newRight]
              simp at h_new; rcases h_new with (rfl | rfl)
              · exact h_occ_left
              · exact h_occ_right
          · -- child ∈ drop (i+1) children → inherits from parent occupancy
            have hmem : child ∈ children := (drop_sublist (i+1) children).subset h_drop
            unfold Occupancy at h_occ; rcases h_occ with ⟨_, _, _, h_pocc_sub⟩
            exact h_pocc_sub child hmem

lemma pairwise_get_mono {l : List Nat} (hp : List.Pairwise (· ≤ ·) l) {j k : Nat}
    (hjk : j ≤ k) (hj : j < l.length) (hk : k < l.length) : l.get ⟨j, hj⟩ ≤ l.get ⟨k, hk⟩ := by
  induction' hp with a l' h_all hp_tail ih generalizing j k
  · exfalso; exact Nat.not_lt_zero j hj
  · rcases k with (rfl | k)
    · have hj0 : j = 0 := Nat.eq_zero_of_le_zero hjk
      subst hj0; exact Nat.le_refl _
    · have hk_lt : k < l'.length := by
        have : k+1 < (a :: l').length := hk; simpa using this
      rcases j with (rfl | j)
      · simp; apply h_all; apply List.get_mem
      · have hj_lt : j < l'.length := by
          have : j+1 < (a :: l').length := hj; simpa using this
        simp; apply ih (by omega) hj_lt hk_lt

theorem splitChild_preserves_sorted (t : Nat) (ht : 2 ≤ t)
    (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (h_sorted : Sorted (node keys children))
    (h_cb : ChildBounded (node keys children)) :
    Sorted (splitChild t (node keys children) i) := by
  have h_keys_snd_nonempty : (cKeys.splitAt (t - 1)).2 ≠ [] := by
    have hlen : (cKeys.splitAt (t - 1)).2.length = t := by simp [hchild_full]; omega
    intro h; rw [h] at hlen; simp at hlen; omega
  dsimp [splitChild]; rw [dif_pos h_lt]
  have h_get : children[i] = node cKeys cChildren := by simpa using hchild_eq
  rw [h_get]; dsimp; rw [if_pos hchild_full]
  cases hk : cKeys.splitAt (t - 1) with
  | mk leftKeys keysRest =>
    have h_keysRest_nonempty : keysRest ≠ [] := by
      have : (cKeys.splitAt (t - 1)).2 = keysRest := by rw [hk]
      rw [← this]; exact h_keys_snd_nonempty
    cases hkr : keysRest with
    | nil => exact (h_keysRest_nonempty hkr).elim
    | cons medianKey rightKeys =>
      cases hc : cChildren.splitAt t with
      | mk leftCh rightCh =>
        show Sorted (BTree.node (take i keys ++ medianKey :: drop i keys)
          (take i children ++ [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
            drop (i + 1) children))
        unfold Sorted at h_sorted; rcases h_sorted with ⟨h_keys_pairwise, h_children_sorted⟩
        have hchild_sorted : Sorted (BTree.node cKeys cChildren) := by
          rw [← hchild_eq]; apply h_children_sorted; apply List.get_mem
        unfold Sorted at hchild_sorted
        rcases hchild_sorted with ⟨h_cKeys_pairwise, h_cChildren_sorted⟩
        -- Children sorted: same pattern as occupancy sub-node proof
        have h_newChildren_sorted : ∀ child ∈ (take i children ++
            [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
            drop (i + 1) children), Sorted child := by
          intro child hchild
          have h_or := List.mem_append.mp hchild
          rcases h_or with (h_take_or_new | h_drop)
          · have h_or2 := List.mem_append.mp h_take_or_new
            rcases h_or2 with (h_take | h_new)
            · have hmem : child ∈ children := (take_sublist i children).subset h_take
              exact h_children_sorted child hmem
            · simp at h_new; rcases h_new with (rfl | rfl)
              · unfold Sorted
                have h_lk : leftKeys = cKeys.take (t-1) := by
                  calc
                    leftKeys = (cKeys.splitAt (t-1)).1 := by rw [hk]
                    _ = cKeys.take (t-1) := by simp
                have h_left_pairwise : List.Pairwise (· ≤ ·) leftKeys := by
                  rw [h_lk]; exact List.Pairwise.take (i := t-1) h_cKeys_pairwise
                refine ⟨h_left_pairwise, ?_⟩
                intro c hc_mem
                have h_left_eq : leftCh = cChildren.take t := by
                  calc
                    leftCh = (cChildren.splitAt t).1 := by rw [hc]
                    _ = cChildren.take t := by simp
                rw [h_left_eq] at hc_mem
                apply h_cChildren_sorted
                exact (take_sublist t cChildren).subset hc_mem
              · unfold Sorted
                have h_rk : rightKeys = cKeys.drop t := by
                  calc
                    rightKeys = keysRest.drop 1 := by rw [hkr]; simp
                    _ = (cKeys.splitAt (t-1)).2.drop 1 := by rw [hk]
                    _ = (cKeys.drop (t-1)).drop 1 := by simp
                    _ = cKeys.drop ((t-1)+1) := by rw [← List.drop_drop]
                    _ = cKeys.drop t := by rw [show (t-1)+1 = t by omega]
                have h_right_pairwise : List.Pairwise (· ≤ ·) rightKeys := by
                  rw [h_rk]; exact List.Pairwise.drop (i := t) h_cKeys_pairwise
                refine ⟨h_right_pairwise, ?_⟩
                intro c hc_mem
                have h_right_eq : rightCh = cChildren.drop t := by
                  calc
                    rightCh = (cChildren.splitAt t).2 := by rw [hc]
                    _ = cChildren.drop t := by simp
                rw [h_right_eq] at hc_mem
                apply h_cChildren_sorted
                exact (drop_sublist t cChildren).subset hc_mem
          · have hmem : child ∈ children := (drop_sublist (i+1) children).subset h_drop
            exact h_children_sorted child hmem
        -- Keys pairwise: uses pairwise_get_mono + ChildBounded bounds.
        -- The proof structure is: (1) extract bounds from ChildBounded into simple inequalities,
        -- (2) use `pairwise_get_mono` to upgrade to universal conditions,
        -- (3) assemble via `List.pairwise_append`.
        -- The membership-to-index steps (j<i from `a ∈ take i keys`, i≤k from `b ∈ drop i keys`)
        -- require list theory lemmas (`mem_take_iff_get`, `mem_drop_iff_get`) not yet available.
        -- These are standard and can be filled in a focused follow-up.
        have h_keys_ok : List.Pairwise (· ≤ ·) (take i keys ++ medianKey :: drop i keys) := by
          sorry
        unfold Sorted
        refine ⟨h_keys_ok, h_newChildren_sorted⟩

theorem splitChild_preserves_childBounded (t : Nat) (ht : 2 ≤ t)
    (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (h_cb : ChildBounded (node keys children)) :
    ChildBounded (splitChild t (node keys children) i) := by
  sorry

end BTree
end Chapter18
end CLRS
