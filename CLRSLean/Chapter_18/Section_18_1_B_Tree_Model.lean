import Mathlib

/-!
# CLRS Section 18.1 - B-tree model

Defines the B-tree data type, key membership, and the full structural invariants
(`Sorted`, `ChildBounded`, `Occupancy`, `SameDepth`).  Proves that the
`B-TREE-SPLIT-CHILD` operation preserves every invariant:
`splitChild_preserves_sorted`, `splitChild_preserves_childBounded`,
`splitChild_preserves_occupancy`, and `splitChild_preserves_sameDepth`, combined
into `splitChild_preserves_wellFormed` (all with 0 `sorry`).
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
        -- Keys pairwise: proved using pairwise_get_mono + ChildBounded bounds + pairwise_append.
        have h_keys_ok : List.Pairwise (· ≤ ·) (take i keys ++ medianKey :: drop i keys) := by
          -- pairwise properties of the two parts
          have h_take_pw : List.Pairwise (· ≤ ·) (take i keys) :=
            List.Pairwise.take (i := i) h_keys_pairwise
          have h_drop_pw : List.Pairwise (· ≤ ·) (drop i keys) :=
            List.Pairwise.drop (i := i) h_keys_pairwise
          -- cross-bound from original pairwise
          have h_keys_eq : take i keys ++ drop i keys = keys := by simp
          have h_pw_app : List.Pairwise (· ≤ ·) (take i keys ++ drop i keys) := by
            rw [h_keys_eq]; exact h_keys_pairwise
          have h_full := (List.pairwise_append (l₁ := take i keys) (l₂ := drop i keys)).mp h_pw_app
          rcases h_full with ⟨_, _, h_cross⟩
          -- medianKey is in cKeys (from the split)
          have h_median_in_cKeys : medianKey ∈ cKeys := by
            have h_cKeys_eq : cKeys = leftKeys ++ medianKey :: rightKeys := by
              calc
                cKeys = cKeys.take (t-1) ++ cKeys.drop (t-1) := by simp
                _ = (cKeys.splitAt (t-1)).1 ++ (cKeys.splitAt (t-1)).2 := by simp
                _ = leftKeys ++ keysRest := by rw [hk]
                _ = leftKeys ++ (medianKey :: rightKeys) := by rw [hkr]
            rw [h_cKeys_eq]; simp
          have h_median_mem : medianKey ∈ keysOf (BTree.node cKeys cChildren) := by
            unfold keysOf; simp [h_median_in_cKeys]
          -- Extract ChildBounded bounds (unfold once, using REPL-proven pattern)
          unfold ChildBounded at h_cb
          rcases h_cb with ⟨h_cb_rel, h_cb_bounds, _⟩
          have h_ilen : children.length = keys.length + 1 := by
            rcases h_cb_rel with (h_empty | h_eq)
            · exfalso
              have hlen0 : children.length = 0 := by simpa using h_empty
              rw [hlen0] at h_lt; exact Nat.not_lt_zero i h_lt
            · exact h_eq
          rcases h_cb_bounds i h_lt with ⟨h_lo_raw, h_hi_raw⟩
          have hi_le : i ≤ keys.length := by rw [h_ilen] at h_lt; omega
          have hchild_eq_get : children[i] = BTree.node cKeys cChildren := by simpa using hchild_eq
          -- lower bound (when i>0): keys[i-1] ≤ medianKey
          have h_lower (hi_pos : 0 < i) (hi_sub : i-1 < keys.length) :
              keys.get ⟨i-1, hi_sub⟩ ≤ medianKey := by
            rcases h_lo_raw with (hi0 | h_lo_match)
            · exact (Nat.ne_of_gt hi_pos hi0).elim
            · simp [hi_sub] at h_lo_match
              rw [hchild_eq_get] at h_lo_match
              exact h_lo_match medianKey h_median_mem
          -- Two cases: i < keys.length or i = keys.length
          by_cases hi_len : i < keys.length
          · -- i < keys.length: the upper bound keys[i] exists
            have h_upper_val : medianKey ≤ keys.get ⟨i, hi_len⟩ := by
              simp [hi_len] at h_hi_raw
              rw [hchild_eq_get] at h_hi_raw
              exact h_hi_raw medianKey h_median_mem
            -- Build take i keys ++ [medianKey] pairwise
            have h_take_le : ∀ a ∈ take i keys, a ≤ medianKey := by
              intro a ha
              rcases List.mem_iff_get.mp ha with ⟨n, h_eq⟩
              -- n : Fin (take i keys).length, so n.val < i (since length ≤ i)
              have hn_val_lt_i : n.val < i :=
                calc n.val < (take i keys).length := n.isLt
                _ ≤ i := by simp
              have hn_len : n.val < keys.length :=
                calc n.val < (take i keys).length := n.isLt
                _ ≤ keys.length := by simp
              -- (take i keys).get n = keys.get ⟨n.val, hn_len⟩
              have h_val : a = keys.get ⟨n.val, hn_len⟩ := by
                calc a = (take i keys).get n := by rw [h_eq]
                _ = keys.get ⟨n.val, hn_len⟩ := by simp
              rw [h_val]
              -- keys[j] ≤ keys[i-1] (pairwise, j < i) ≤ medianKey (h_lower)
              by_cases hi0 : i = 0
              · subst hi0; omega
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
                have hi_sub : i-1 < keys.length := by omega
                have h_pw : keys.get ⟨n.val, hn_len⟩ ≤ keys.get ⟨i-1, hi_sub⟩ :=
                  pairwise_get_mono h_keys_pairwise (by omega) hn_len hi_sub
                exact Nat.le_trans h_pw (h_lower hi_pos hi_sub)
            -- Build medianKey ≤ ∀ b ∈ drop i keys
            have h_drop_le : ∀ b ∈ drop i keys, medianKey ≤ b := by
              intro b hb
              rcases List.mem_iff_get.mp hb with ⟨n, h_eq⟩
              -- n : Fin (drop i keys).length
              -- (drop i keys).get n = keys.get ⟨i + n.val, ...⟩
              have hn_total_len : i + n.val < keys.length := by
                have : (drop i keys).length = keys.length - i := by simp
                have : n.val < keys.length - i := by
                  rw [← this]; exact n.isLt
                omega
              have h_val : b = keys.get ⟨i + n.val, hn_total_len⟩ := by
                calc b = (drop i keys).get n := by rw [h_eq]
                _ = keys.get ⟨i + n.val, hn_total_len⟩ := by simp
              rw [h_val]
              -- medianKey ≤ keys[i] (h_upper_val) ≤ keys[i + n.val] (pairwise, i ≤ i+n.val)
              have h_pw : keys.get ⟨i, hi_len⟩ ≤ keys.get ⟨i + n.val, hn_total_len⟩ :=
                pairwise_get_mono h_keys_pairwise (by omega) hi_len hn_total_len
              exact Nat.le_trans h_upper_val h_pw
            -- Assemble with pairwise_append
            have h_singleton : List.Pairwise (· ≤ ·) [medianKey] := by simp
            have h_prefix : List.Pairwise (· ≤ ·) (take i keys ++ [medianKey]) :=
              (List.pairwise_append (l₁ := take i keys) (l₂ := [medianKey])).mpr
                ⟨h_take_pw, h_singleton, λ a ha b hb => by
                  simp at hb; subst hb; exact h_take_le a ha⟩
            -- Need to rewrite the goal to match pairwise_append's l₁ ++ l₂ pattern
            have h_assoc : take i keys ++ medianKey :: drop i keys = (take i keys ++ [medianKey]) ++ drop i keys := by simp
            rw [h_assoc]
            exact ((List.pairwise_append (l₁ := take i keys ++ [medianKey]) (l₂ := drop i keys)).mpr
              ⟨h_prefix, h_drop_pw, λ a ha b hb => by
                rw [List.mem_append] at ha; rcases ha with (ha | ha)
                · exact h_cross a ha b hb
                · simp at ha; subst ha; exact h_drop_le b hb⟩)
          · -- i = keys.length: no upper bound key, drop i keys = []
            have hi_eq : i = keys.length := by omega
            have h_drop_empty : drop i keys = [] := by rw [hi_eq]; simp
            rw [h_drop_empty]
            -- Goal: List.Pairwise (· ≤ ·) (take i keys ++ medianKey :: [])
            -- medianKey :: [] = [medianKey]
            have h_cons_nil : medianKey :: [] = [medianKey] := by simp
            rw [h_cons_nil]
            -- Goal: List.Pairwise (· ≤ ·) (take i keys ++ [medianKey])
            -- Same as the h_prefix proof above, but we use h_take_pw from the outer scope
            have h_take_le : ∀ a ∈ take i keys, a ≤ medianKey := by
              intro a ha
              rcases List.mem_iff_get.mp ha with ⟨n, h_eq⟩
              have hn_len : n.val < keys.length :=
                Nat.lt_of_lt_of_le n.isLt (by simp)
              have h_val : a = keys.get ⟨n.val, hn_len⟩ := by
                calc a = (take i keys).get n := by rw [h_eq]
                _ = keys.get ⟨n.val, hn_len⟩ := by simp
              rw [h_val]
              by_cases hi0 : i = 0
              · subst hi0; omega
              · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi0
                have hi_sub : i-1 < keys.length := by omega
                have h_pw : keys.get ⟨n.val, hn_len⟩ ≤ keys.get ⟨i-1, hi_sub⟩ :=
                  pairwise_get_mono h_keys_pairwise (by omega) hn_len hi_sub
                exact Nat.le_trans h_pw (h_lower hi_pos hi_sub)
            have h_singleton : List.Pairwise (· ≤ ·) [medianKey] := by simp
            exact (List.pairwise_append (l₁ := take i keys) (l₂ := [medianKey])).mpr
              ⟨h_take_pw, h_singleton, λ a ha b hb => by simp at hb; subst hb; exact h_take_le a ha⟩
        unfold Sorted
        refine ⟨h_keys_ok, h_newChildren_sorted⟩

/-! ## ChildBounded preservation infrastructure

The proof of `splitChild_preserves_childBounded` relies on:
- `keysOf_node_subset`: the keys of a node built from sublists is a subset.
- `childBounded_node_nil`: a node with no children is trivially bounded.
- `keysOf_take_le_pivot` / `keysOf_drop_ge_pivot`: the median key sandwiches the
  two new children (this is the ordering content that needs `Sorted`).
- `childBounded_take_of_full` / `childBounded_drop_of_full`: `ChildBounded`
  survives truncating a full node's keys/children to a prefix/suffix.
-/

/-- If `ks ⊆ ks'` and `cs ⊆ cs'`, then the flattened keys of `node ks cs` are a
subset of those of `node ks' cs'`.  This is the user-suggested `keysOf_subset`
lemma, phrased for arbitrary sublists (used for both the left and right split
children). -/
lemma keysOf_node_subset {ks ks' : List Nat} {cs cs' : List BTree}
    (hk : ks ⊆ ks') (hc : cs ⊆ cs') :
    keysOf (node ks cs) ⊆ keysOf (node ks' cs') := by
  intro x hx
  simp only [keysOf, List.mem_append, List.mem_flatMap] at hx ⊢
  rcases hx with hxk | ⟨c, hcm, hxc⟩
  · exact Or.inl (hk hxk)
  · exact Or.inr ⟨c, hc hcm, hxc⟩

/-- A node with no children is trivially `ChildBounded`. -/
lemma childBounded_node_nil (ks : List Nat) : ChildBounded (node ks []) := by
  unfold ChildBounded
  refine ⟨Or.inl (by simp), ?_, ?_⟩
  · intro j hj; simp at hj
  · intro c hc; simp at hc

/-- Every key beneath the left split node `node (ks.take m) (cs.take (m+1))` is
`≤ ks[m]` (the median key).  Uses sortedness of `ks` and the child's own
`ChildBounded` upper bounds. -/
lemma keysOf_take_le_pivot {ks : List Nat} {cs : List BTree} {m : Nat}
    (h_pw : List.Pairwise (· ≤ ·) ks)
    (h_cb : ChildBounded (node ks cs))
    (hm : m < ks.length) :
    ∀ k ∈ keysOf (node (ks.take m) (cs.take (m + 1))), k ≤ ks[m] := by
  intro k hk
  simp only [keysOf, List.mem_append, List.mem_flatMap] at hk
  rcases hk with hk | ⟨c, hc, hkc⟩
  · -- key from the truncated key list: monotone since `ks` is sorted
    rcases List.mem_iff_get.mp hk with ⟨n, h_eq⟩
    have hn_m : n.val < m := Nat.lt_of_lt_of_le n.isLt (List.length_take_le m ks)
    have hn_ks : n.val < ks.length := by omega
    have h_val : k = ks.get ⟨n.val, hn_ks⟩ := by
      calc k = (ks.take m).get n := by rw [h_eq]
        _ = ks.get ⟨n.val, hn_ks⟩ := by simp
    rw [h_val]
    exact pairwise_get_mono h_pw (by omega) hn_ks hm
  · -- key from a child subtree: bounded by `ks[n] ≤ ks[m]`
    rcases List.mem_iff_get.mp hc with ⟨n, h_eq⟩
    have hn_m1 : n.val < m + 1 := Nat.lt_of_lt_of_le n.isLt (List.length_take_le (m + 1) cs)
    have hn_cs : n.val < cs.length := Nat.lt_of_lt_of_le n.isLt (List.length_take_le' (m + 1) cs)
    have hn_ks : n.val < ks.length := by omega
    have hc_eq : c = cs.get ⟨n.val, hn_cs⟩ := by
      calc c = (cs.take (m + 1)).get n := by rw [h_eq]
        _ = cs.get ⟨n.val, hn_cs⟩ := by simp
    unfold ChildBounded at h_cb
    rcases h_cb with ⟨_, h_bounds, _⟩
    have hub := (h_bounds n.val hn_cs).2
    simp only [List.getElem?_eq_getElem hn_ks] at hub
    rw [← hc_eq] at hub
    have h1 : k ≤ ks[n.val] := hub k hkc
    have h2 := pairwise_get_mono h_pw (show n.val ≤ m by omega) hn_ks hm
    simp only [List.get_eq_getElem] at h2
    exact le_trans h1 h2

/-- Every key beneath the right split node `node (ks.drop (m+1)) (cs.drop (m+1))`
is `≥ ks[m]` (the median key).  Symmetric to `keysOf_take_le_pivot`. -/
lemma keysOf_drop_ge_pivot {ks : List Nat} {cs : List BTree} {m : Nat}
    (h_pw : List.Pairwise (· ≤ ·) ks)
    (h_cb : ChildBounded (node ks cs))
    (hm : m < ks.length) :
    ∀ k ∈ keysOf (node (ks.drop (m + 1)) (cs.drop (m + 1))), ks[m] ≤ k := by
  intro k hk
  simp only [keysOf, List.mem_append, List.mem_flatMap] at hk
  rcases hk with hk | ⟨c, hc, hkc⟩
  · -- key from the truncated key list
    rcases List.mem_iff_get.mp hk with ⟨n, h_eq⟩
    have hn_len : (m + 1) + n.val < ks.length := by
      have h : n.val < ks.length - (m + 1) := by rw [← List.length_drop]; exact n.isLt
      omega
    have h_val : k = ks.get ⟨(m + 1) + n.val, hn_len⟩ := by
      calc k = (ks.drop (m + 1)).get n := by rw [h_eq]
        _ = ks.get ⟨(m + 1) + n.val, hn_len⟩ := by simp
    rw [h_val]
    exact pairwise_get_mono h_pw (by omega) hm hn_len
  · -- key from a child subtree: bounded by `ks[m] ≤ ks[(m+1)+n-1]`
    rcases List.mem_iff_get.mp hc with ⟨n, h_eq⟩
    have hn_cs : (m + 1) + n.val < cs.length := by
      have h : n.val < cs.length - (m + 1) := by rw [← List.length_drop]; exact n.isLt
      omega
    unfold ChildBounded at h_cb
    rcases h_cb with ⟨h_rel, h_bounds, _⟩
    have h_len : cs.length = ks.length + 1 := by
      rcases h_rel with h_empty | h_len
      · have hnil : cs = [] := List.isEmpty_iff.mp h_empty
        have hlen0 : cs.length = 0 := by simp [hnil]
        omega
      · exact h_len
    have hidx : (m + 1) + n.val - 1 < ks.length := by omega
    have hc_eq : c = cs.get ⟨(m + 1) + n.val, hn_cs⟩ := by
      calc c = (cs.drop (m + 1)).get n := by rw [h_eq]
        _ = cs.get ⟨(m + 1) + n.val, hn_cs⟩ := by simp
    have hlb := (h_bounds ((m + 1) + n.val) hn_cs).1
    rcases hlb with h0 | hlbmatch
    · omega
    · simp only [List.getElem?_eq_getElem hidx] at hlbmatch
      rw [← hc_eq] at hlbmatch
      have h1 : ks[(m + 1) + n.val - 1] ≤ k := hlbmatch k hkc
      have h2 := pairwise_get_mono h_pw (show m ≤ (m + 1) + n.val - 1 by omega) hm hidx
      simp only [List.get_eq_getElem] at h2
      exact le_trans h2 h1

/-- `ChildBounded` survives truncating a node's keys to `take m` and children to
`take (m+1)` (the left result of a split). -/
lemma childBounded_take_of_full {ks : List Nat} {cs : List BTree} {m : Nat}
    (h_cb : ChildBounded (node ks cs)) (hm : m < ks.length) :
    ChildBounded (node (ks.take m) (cs.take (m + 1))) := by
  have h_cb' := h_cb
  unfold ChildBounded at h_cb'
  rcases h_cb' with ⟨h_rel, h_bounds, h_sub⟩
  rcases h_rel with h_empty | h_len
  · have hcs : cs = [] := by cases cs with | nil => rfl | cons x xs => simp at h_empty
    subst hcs
    simpa using childBounded_node_nil (ks.take m)
  · unfold ChildBounded
    refine ⟨?_, ?_, ?_⟩
    · right; rw [List.length_take, List.length_take]; omega
    · intro j hj
      have hj_cs : j < cs.length := by have := hj; rw [List.length_take] at this; omega
      have hchild : (cs.take (m + 1)).get ⟨j, hj⟩ = cs.get ⟨j, hj_cs⟩ := by simp
      refine ⟨?_, ?_⟩
      · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
        · exact Or.inl hj0
        · right
          have hj1_m : j - 1 < m := by have := hj; rw [List.length_take] at this; omega
          have hj1_ks : j - 1 < ks.length := by omega
          rw [List.getElem?_take_of_lt hj1_m, List.getElem?_eq_getElem hj1_ks]
          have hlb := (h_bounds j hj_cs).1
          rcases hlb with h0 | hlbmatch
          · omega
          · simp only [List.getElem?_eq_getElem hj1_ks] at hlbmatch
            intro k hk; rw [hchild] at hk; exact hlbmatch k hk
      · by_cases hj_m : j < m
        · have hj_ks : j < ks.length := by omega
          rw [List.getElem?_take_of_lt hj_m, List.getElem?_eq_getElem hj_ks]
          have hub := (h_bounds j hj_cs).2
          simp only [List.getElem?_eq_getElem hj_ks] at hub
          intro k hk; rw [hchild] at hk; exact hub k hk
        · have hnone : (ks.take m)[j]? = none := by
            apply List.getElem?_eq_none; rw [List.length_take]; omega
          rw [hnone]; exact trivial
    · intro c hc
      exact h_sub c ((List.take_subset (m + 1) cs) hc)

/-- `ChildBounded` survives dropping `d` keys and `d` children (the right result
of a split, with `d = t`). -/
lemma childBounded_drop_of_full {ks : List Nat} {cs : List BTree} {d : Nat}
    (h_cb : ChildBounded (node ks cs)) (hd : 0 < d) (hd_cs : d < cs.length) :
    ChildBounded (node (ks.drop d) (cs.drop d)) := by
  have h_cb' := h_cb
  unfold ChildBounded at h_cb'
  rcases h_cb' with ⟨h_rel, h_bounds, h_sub⟩
  have h_len : cs.length = ks.length + 1 := by
    rcases h_rel with h_empty | h_len
    · have hnil : cs = [] := by cases cs with | nil => rfl | cons x xs => simp at h_empty
      rw [hnil] at hd_cs; simp at hd_cs
    · exact h_len
  unfold ChildBounded
  refine ⟨?_, ?_, ?_⟩
  · right; rw [List.length_drop, List.length_drop]; omega
  · intro j hj
    have hj_len : j < cs.length - d := by have := hj; rw [List.length_drop] at this; exact this
    have hdj_cs : d + j < cs.length := by omega
    have hchild : (cs.drop d).get ⟨j, hj⟩ = cs.get ⟨d + j, hdj_cs⟩ := by simp
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · exact Or.inl hj0
      · right
        have hidx : d + j - 1 < ks.length := by omega
        have heq_idx : d + (j - 1) = d + j - 1 := by omega
        rw [List.getElem?_drop, heq_idx, List.getElem?_eq_getElem hidx]
        have hlb := (h_bounds (d + j) hdj_cs).1
        rcases hlb with h0 | hlbmatch
        · omega
        · simp only [List.getElem?_eq_getElem hidx] at hlbmatch
          intro k hk; rw [hchild] at hk; exact hlbmatch k hk
    · by_cases hdj : d + j < ks.length
      · rw [List.getElem?_drop, List.getElem?_eq_getElem hdj]
        have hub := (h_bounds (d + j) hdj_cs).2
        simp only [List.getElem?_eq_getElem hdj] at hub
        intro k hk; rw [hchild] at hk; exact hub k hk
      · have hnone : (ks.drop d)[j]? = none := by
          rw [List.getElem?_drop]; apply List.getElem?_eq_none; omega
        rw [hnone]; exact trivial
  · intro c hc
    exact h_sub c ((List.drop_subset d cs) hc)

/--
**`B-TREE-SPLIT-CHILD` preserves `ChildBounded`.**  Splitting a full child of a
non-full node keeps the key-range invariant: the promoted median key becomes a
new separator that sandwiches the two halves, and every other separator/child
relation is inherited from the original tree.
-/
theorem splitChild_preserves_childBounded (t : Nat) (ht : 2 ≤ t)
    (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (h_cb : ChildBounded (node keys children))
    (h_sorted : Sorted (node keys children)) :
    ChildBounded (splitChild t (node keys children) i) := by
  -- Extract the parent's ChildBounded components.
  have h_cb' := h_cb
  unfold ChildBounded at h_cb'
  obtain ⟨h_cb_rel, h_cb_bounds, h_cb_sub⟩ := h_cb'
  have h_ch_len : children.length = keys.length + 1 := by
    rcases h_cb_rel with h_empty | h_eq
    · have hnil : children = [] := List.isEmpty_iff.mp h_empty
      have : children.length = 0 := by simp [hnil]
      omega
    · exact h_eq
  have h_i_le_keys : i ≤ keys.length := by omega
  -- Unfold `splitChild` (same pattern as `splitChild_preserves_sorted`).
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
        show ChildBounded (BTree.node (take i keys ++ medianKey :: drop i keys)
          (take i children ++ [BTree.node leftKeys leftCh, BTree.node rightKeys rightCh] ++
            drop (i + 1) children))
        -- Relate the local split names to `take`/`drop` of the child's keys/children.
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
        have h_left_eq : leftCh = cChildren.take t := by
          calc leftCh = (cChildren.splitAt t).1 := by rw [hc]
            _ = cChildren.take t := by simp
        have h_right_eq : rightCh = cChildren.drop t := by
          calc rightCh = (cChildren.splitAt t).2 := by rw [hc]
            _ = cChildren.drop t := by simp
        have h_t1_lt : t - 1 < cKeys.length := by omega
        have h_median : cKeys[t - 1]? = some medianKey := by
          have hh : (cKeys.drop (t - 1))[0]? = some medianKey := by
            rw [← h_keysRest_eq, hkr]; rfl
          rw [List.getElem?_drop] at hh; simpa using hh
        have h_median_eq : medianKey = cKeys[t - 1] := by
          rw [List.getElem?_eq_getElem h_t1_lt] at h_median
          injection h_median with h_median; exact h_median.symm
        -- Child invariants.
        have h_child_cb : ChildBounded (node cKeys cChildren) := by
          rw [← hchild_eq]; apply h_cb_sub; apply List.get_mem
        have h_cKeys_pw : List.Pairwise (· ≤ ·) cKeys := by
          have h_cs : Sorted (node cKeys cChildren) := by
            rw [← hchild_eq]
            unfold Sorted at h_sorted; rcases h_sorted with ⟨_, h_sc⟩
            apply h_sc; apply List.get_mem
          unfold Sorted at h_cs; exact h_cs.1
        have h_cChildren_len := child_children_len_of_full_cb ht h_child_cb hchild_full
        -- The median key sandwiches the two new children.
        have h_left_le : ∀ k ∈ keysOf (node leftKeys leftCh), k ≤ medianKey := by
          intro k hk
          rw [h_lk, h_left_eq] at hk
          rw [h_median_eq]
          have hp := keysOf_take_le_pivot h_cKeys_pw h_child_cb h_t1_lt
          rw [show (t - 1) + 1 = t from by omega] at hp
          exact hp k hk
        have h_right_ge : ∀ k ∈ keysOf (node rightKeys rightCh), medianKey ≤ k := by
          intro k hk
          rw [h_rk, h_right_eq] at hk
          rw [h_median_eq]
          have hp := keysOf_drop_ge_pivot h_cKeys_pw h_child_cb h_t1_lt
          rw [show (t - 1) + 1 = t from by omega] at hp
          exact hp k hk
        -- The two new children are themselves ChildBounded.
        have h_cb_left : ChildBounded (node leftKeys leftCh) := by
          have hh := childBounded_take_of_full h_child_cb h_t1_lt
          rw [show (t - 1) + 1 = t from by omega] at hh
          rw [h_lk, h_left_eq]; exact hh
        have h_cb_right : ChildBounded (node rightKeys rightCh) := by
          rcases h_cChildren_len with h0 | h2t
          · have hnil : cChildren = [] := by
              cases cChildren with | nil => rfl | cons x xs => simp at h0
            have hrc : rightCh = [] := by rw [h_right_eq, hnil]; simp
            rw [hrc]; exact childBounded_node_nil rightKeys
          · have hd_cs : t < cChildren.length := by rw [h2t]; omega
            have hh := childBounded_drop_of_full h_child_cb (by omega) hd_cs
            rw [h_rk, h_right_eq]; exact hh
        -- `newKeys[·]?` computed by position relative to the inserted median.
        have h_P_len : (take i keys).length = i := by rw [List.length_take]; omega
        have hNK_lt : ∀ j', j' < i →
            (take i keys ++ medianKey :: drop i keys)[j']? = keys[j']? := by
          intro j' hj'
          rw [List.getElem?_append_left (by rw [h_P_len]; exact hj'), List.getElem?_take_of_lt hj']
        have hNK_eq : (take i keys ++ medianKey :: drop i keys)[i]? = some medianKey := by
          rw [List.getElem?_append_right (le_of_eq h_P_len), h_P_len]; simp
        have hNK_gt : ∀ j', i < j' →
            (take i keys ++ medianKey :: drop i keys)[j']? = keys[j' - 1]? := by
          intro j' hj'
          rw [List.getElem?_append_right (by rw [h_P_len]; omega), h_P_len,
              show j' - i = (j' - i - 1) + 1 from by omega, List.getElem?_cons_succ,
              List.getElem?_drop, show i + (j' - i - 1) = j' - 1 from by omega]
        unfold ChildBounded
        refine ⟨?_, ?_, ?_⟩
        · -- Count relation.
          right
          simp only [List.length_append, List.length_cons, List.length_nil,
            List.length_take, List.length_drop]
          omega
        · -- Parent key-range bounds.
          have h_A_len : (take i children).length = i := by rw [List.length_take]; omega
          have h_AB_len : (take i children ++
              [node leftKeys leftCh, node rightKeys rightCh]).length = i + 2 := by
            simp [List.length_append, h_A_len]
          have h_nc_len : (take i children ++
              [node leftKeys leftCh, node rightKeys rightCh] ++ drop (i + 1) children).length
              = children.length + 1 := by
            simp only [List.length_append, List.length_cons, List.length_nil,
              List.length_take, List.length_drop]
            omega
          have hsub_left : keysOf (node leftKeys leftCh) ⊆ keysOf (node cKeys cChildren) :=
            keysOf_node_subset (by rw [h_lk]; exact List.take_subset _ _)
              (by rw [h_left_eq]; exact List.take_subset _ _)
          have hsub_right : keysOf (node rightKeys rightCh) ⊆ keysOf (node cKeys cChildren) :=
            keysOf_node_subset (by rw [h_rk]; exact List.drop_subset _ _)
              (by rw [h_right_eq]; exact List.drop_subset _ _)
          intro j hj
          have hj' : j < children.length + 1 := h_nc_len ▸ hj
          rcases Nat.lt_trichotomy j i with hlt | heq | hgt
          · -- Region 1: `j < i` — unchanged left children.
            have hj_ch : j < children.length := by omega
            have hlt_AB : j < (take i children ++
                [node leftKeys leftCh, node rightKeys rightCh]).length := by rw [h_AB_len]; omega
            have hlt_A : j < (take i children).length := by rw [h_A_len]; omega
            have hchild : (take i children ++ [node leftKeys leftCh, node rightKeys rightCh] ++
                drop (i + 1) children).get ⟨j, hj⟩ = children.get ⟨j, hj_ch⟩ := by
              simp only [List.get_eq_getElem]
              rw [List.getElem_append_left hlt_AB, List.getElem_append_left hlt_A]; simp
            refine ⟨?_, ?_⟩
            · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
              · exact Or.inl hj0
              · right
                rw [hNK_lt (j - 1) (by omega), hchild]
                rcases (h_cb_bounds j hj_ch).1 with h0 | hbmatch
                · omega
                · exact hbmatch
            · rw [hNK_lt j hlt, hchild]
              exact (h_cb_bounds j hj_ch).2
          · -- Region 2: `j = i` — the new left child.
            have hlt_AB : j < (take i children ++
                [node leftKeys leftCh, node rightKeys rightCh]).length := by rw [h_AB_len]; omega
            have hge_A : (take i children).length ≤ j := by rw [h_A_len]; omega
            have hchild : (take i children ++ [node leftKeys leftCh, node rightKeys rightCh] ++
                drop (i + 1) children).get ⟨j, hj⟩ = node leftKeys leftCh := by
              simp only [List.get_eq_getElem]
              rw [List.getElem_append_left hlt_AB, List.getElem_append_right hge_A]
              simp [h_A_len, show j - i = 0 from by omega]
            refine ⟨?_, ?_⟩
            · rcases Nat.eq_zero_or_pos j with hj0 | hjpos
              · exact Or.inl hj0
              · right
                rw [hNK_lt (j - 1) (by omega), hchild, show j - 1 = i - 1 from by omega]
                have hb := (h_cb_bounds i h_lt).1
                rw [hchild_eq] at hb
                rcases hb with h0 | hbmatch
                · omega
                · revert hbmatch
                  cases keys[i - 1]? with
                  | none => intro _; trivial
                  | some lo => intro hbmatch; exact fun k hk => hbmatch k (hsub_left hk)
            · have hjk : (take i keys ++ medianKey :: drop i keys)[j]? = some medianKey := by
                rw [show j = i from heq]; exact hNK_eq
              rw [hjk, hchild]; exact h_left_le
          · rcases Nat.lt_or_ge j (i + 2) with hj2 | hj2
            · -- Region 3: `j = i + 1` — the new right child.
              have hlt_AB : j < (take i children ++
                  [node leftKeys leftCh, node rightKeys rightCh]).length := by rw [h_AB_len]; omega
              have hge_A : (take i children).length ≤ j := by rw [h_A_len]; omega
              have hchild : (take i children ++ [node leftKeys leftCh, node rightKeys rightCh] ++
                  drop (i + 1) children).get ⟨j, hj⟩ = node rightKeys rightCh := by
                simp only [List.get_eq_getElem]
                rw [List.getElem_append_left hlt_AB, List.getElem_append_right hge_A]
                simp [h_A_len, show j - i = 1 from by omega]
              refine ⟨?_, ?_⟩
              · right
                rw [show j - 1 = i from by omega, hNK_eq, hchild]
                exact h_right_ge
              · rw [hNK_gt j (by omega), show j - 1 = i from by omega, hchild]
                have hb := (h_cb_bounds i h_lt).2
                rw [hchild_eq] at hb
                revert hb
                cases keys[i]? with
                | none => intro _; trivial
                | some hi => intro hb; exact fun k hk => hb k (hsub_right hk)
            · -- Region 4: `j ≥ i + 2` — unchanged right children (shifted by one).
              have hj1_ch : j - 1 < children.length := by omega
              have hge_AB : (take i children ++
                  [node leftKeys leftCh, node rightKeys rightCh]).length ≤ j := by
                rw [h_AB_len]; omega
              have hchild : (take i children ++ [node leftKeys leftCh, node rightKeys rightCh] ++
                  drop (i + 1) children).get ⟨j, hj⟩ = children.get ⟨j - 1, hj1_ch⟩ := by
                simp only [List.get_eq_getElem]
                rw [List.getElem_append_right hge_AB]
                simp only [h_AB_len, List.getElem_drop,
                  show (i + 1) + (j - (i + 2)) = j - 1 from by omega]
              refine ⟨?_, ?_⟩
              · right
                rw [hNK_gt (j - 1) (by omega), hchild]
                rcases (h_cb_bounds (j - 1) hj1_ch).1 with h0 | hbmatch
                · omega
                · exact hbmatch
              · rw [hNK_gt j (by omega), hchild]
                exact (h_cb_bounds (j - 1) hj1_ch).2
        · -- Recursive ChildBounded of every new child.
          intro child hchild
          rcases List.mem_append.mp hchild with h_take_new | h_drop
          · rcases List.mem_append.mp h_take_new with h_take | h_new
            · exact h_cb_sub child ((List.take_subset i children) h_take)
            · simp at h_new; rcases h_new with rfl | rfl
              · exact h_cb_left
              · exact h_cb_right
          · exact h_cb_sub child ((List.drop_subset (i + 1) children) h_drop)

/--
**`B-TREE-SPLIT-CHILD` preserves `WellFormed`.**  Splitting a full child `i` of a
non-full node keeps all four structural invariants simultaneously.  This is the
capstone that combines `splitChild_preserves_sorted`,
`splitChild_preserves_childBounded`, `splitChild_preserves_occupancy`, and
`splitChild_preserves_sameDepth`.  The side condition
`cChildren = [] ∨ t < cChildren.length` needed by the `SameDepth` lemma is
derived from the child's own `ChildBounded` invariant.
-/
theorem splitChild_preserves_wellFormed (t : Nat) (ht : 2 ≤ t)
    (keys : List Nat) (children : List BTree)
    (cKeys : List Nat) (cChildren : List BTree) (i : Nat)
    (h_lt : i < children.length)
    (hchild_eq : children.get ⟨i, h_lt⟩ = node cKeys cChildren)
    (hchild_full : cKeys.length = 2 * t - 1)
    (hparent_nonfull : keys.length < 2 * t - 1)
    (h_wf : WellFormed t (node keys children)) :
    WellFormed t (splitChild t (node keys children) i) := by
  obtain ⟨h_sorted, h_cb, h_occ, h_sd⟩ := h_wf
  -- The split child is itself `ChildBounded`, so its child count is `0` or `2t`.
  have h_child_cb : ChildBounded (node cKeys cChildren) := by
    rw [← hchild_eq]
    have hcb := h_cb
    unfold ChildBounded at hcb; rcases hcb with ⟨_, _, h_sub⟩
    apply h_sub; apply List.get_mem
  have hchild_children : cChildren = [] ∨ t < cChildren.length := by
    rcases child_children_len_of_full_cb ht h_child_cb hchild_full with h0 | h2t
    · left; cases cChildren with | nil => rfl | cons x xs => simp at h0
    · right; rw [h2t]; omega
  exact ⟨splitChild_preserves_sorted t ht keys children cKeys cChildren i h_lt hchild_eq
            hchild_full h_sorted h_cb,
         splitChild_preserves_childBounded t ht keys children cKeys cChildren i h_lt hchild_eq
            hchild_full h_cb h_sorted,
         splitChild_preserves_occupancy t ht keys children cKeys cChildren i h_lt hchild_eq
            hchild_full hparent_nonfull h_occ h_cb,
         splitChild_preserves_sameDepth t ht keys children cKeys cChildren i h_lt hchild_eq
            hchild_full hchild_children h_sd⟩

end BTree
end Chapter18
end CLRS
