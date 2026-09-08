import CLRSLean.Chapter_14.Section_14_3_Interval_Trees

/-!
# Complete-key interval insertion

Generic augmented red-black insertion preserves membership when comparator ties
imply key equality. Balancing preserves the exact inorder key list, so insertion
also preserves any compatible transitive ordering relation. The interval
instance uses strict lexicographic order on both endpoints, and separately
preserves the weak low-endpoint ordering required by the static search proof.
-/

namespace CLRS.Chapter14.AugmentedRBTree
open CLRS.Chapter13 (Color)

variable {α β : Type} [Inhabited β] (aug : Augmentation α β)

omit [Inhabited β] in
/-- Root repainting preserves the full inorder key list. -/
@[simp] theorem keys_repaintBlack_generic (t : AugmentedRBTree α β) :
    keys (repaintBlack t) = keys t := by cases t <;> rfl

/-- Left insertion balancing preserves the full inorder key list. -/
@[simp] theorem keys_balanceLeft_generic (l : AugmentedRBTree α β) (k : α) (r) :
    keys (balanceLeft aug l k r) = keys l ++ [k] ++ keys r := by
  unfold balanceLeft
  split <;> simp [mk, keys, List.append_assoc]

/-- Right insertion balancing preserves the full inorder key list. -/
@[simp] theorem keys_balanceRight_generic (l : AugmentedRBTree α β) (k : α) (r) :
    keys (balanceRight aug l k r) = keys l ++ [k] ++ keys r := by
  unfold balanceRight
  split <;> simp [mk, keys, List.append_assoc]

/-- Fixup inserts the requested complete key and preserves all old keys. -/
theorem mem_keys_insertFixup_of_compare (lt : α → α → Bool)
    (hsep : ∀ x y, lt x y ≠ true → lt y x ≠ true → x = y)
    (x y : α) (t : AugmentedRBTree α β) :
    y ∈ keys (insertFixup aug lt x t) ↔ y = x ∨ y ∈ keys t := by
  induction t with
  | empty => simp [insertFixup, mk, keys]
  | node c l k a r ihl ihr =>
    simp only [insertFixup]
    split
    · split <;> simp only [keys_balanceLeft_generic, keys_mk, List.mem_append,
        List.mem_singleton, ihl, keys] <;> tauto
    · rename_i hx
      split
      · split <;> simp only [keys_balanceRight_generic, keys_mk, List.mem_append,
          List.mem_singleton, ihr, keys] <;> tauto
      · rename_i hk
        have he := hsep x k hx hk
        subst x
        simp only [keys, List.mem_append, List.mem_singleton]
        tauto

/-- Comparator ties must identify equal keys for set insertion membership. -/
theorem mem_keys_insert_of_compare (lt : α → α → Bool)
    (hsep : ∀ x y, lt x y ≠ true → lt y x ≠ true → x = y)
    (x y : α) (t : AugmentedRBTree α β) :
    y ∈ keys (insert aug lt x t) ↔ y = x ∨ y ∈ keys t := by
  simpa [insert] using mem_keys_insertFixup_of_compare aug lt hsep x y t

private theorem pairwise_middle (rel : α → α → Prop) (htrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z) (L R : List α) (k : α) :
    (L ++ [k] ++ R).Pairwise (fun x y => rel x y) ↔
      L.Pairwise (fun x y => rel x y) ∧
      R.Pairwise (fun x y => rel x y) ∧
      (∀ x ∈ L, rel x k) ∧ (∀ y ∈ R, rel k y) := by
  simp only [List.pairwise_append, List.pairwise_singleton, List.mem_append, List.mem_singleton]
  constructor
  · rintro ⟨⟨hL, _, hLk⟩, hR, hcross⟩
    exact ⟨hL, hR, fun x hx => hLk x hx k rfl, fun y hy => hcross k (Or.inr rfl) y hy⟩
  · rintro ⟨hL, hR, hLk, hkR⟩
    refine ⟨⟨hL, trivial, ?_⟩, hR, ?_⟩
    · rintro x hx y rfl
      exact hLk x hx
    · rintro x (hx | rfl) y hy
      · exact htrans (hLk x hx) (hkR y hy)
      · exact hkR y hy

/-- All inorder keys satisfy a supplied ordering relation. -/
def Ordered (rel : α → α → Prop) (t : AugmentedRBTree α β) : Prop :=
  (keys t).Pairwise (fun x y => rel x y)

omit [Inhabited β] in
/-- A transitive inorder relation is equivalent to the recursive BST bounds. -/
theorem ordered_node (rel : α → α → Prop) (htrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z) (c l k a r) :
    Ordered rel (.node c l k a r : AugmentedRBTree α β) ↔
      Ordered rel l ∧ Ordered rel r ∧
      (∀ x ∈ keys l, rel x k) ∧ (∀ y ∈ keys r, rel k y) :=
  pairwise_middle rel htrans (keys l) (keys r) k

/-- Fixup preserves any transitive relation compatible with comparison. -/
theorem ordered_insertFixup (lt : α → α → Bool)
    (hsep : ∀ x y, lt x y ≠ true → lt y x ≠ true → x = y)
    (rel : α → α → Prop) (htrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z) (hcompat : ∀ x y, lt x y = true → rel x y)
    (x : α) {t : AugmentedRBTree α β} (ht : Ordered rel t) :
    Ordered rel (insertFixup aug lt x t) := by
  induction t with
  | empty => simp [insertFixup, Ordered, mk, keys]
  | node c l k a r ihl ihr =>
    obtain ⟨hl, hr, hLk, hkR⟩ := (ordered_node rel htrans c l k a r).mp ht
    simp only [insertFixup]
    split
    · rename_i hx
      have hnew : (keys (insertFixup aug lt x l) ++ [k] ++ keys r).Pairwise
          (fun u v => rel u v) := by
        apply (pairwise_middle rel htrans _ _ _).mpr
        refine ⟨ihl hl, hr, ?_, hkR⟩
        intro y hy
        rcases (mem_keys_insertFixup_of_compare aug lt hsep x y l).mp hy with rfl | hy
        · exact hcompat y k hx
        · exact hLk y hy
      split <;> simpa only [Ordered, keys_balanceLeft_generic, keys_mk] using hnew
    · split
      · rename_i hx
        have hnew : (keys l ++ [k] ++ keys (insertFixup aug lt x r)).Pairwise
            (fun u v => rel u v) := by
          apply (pairwise_middle rel htrans _ _ _).mpr
          refine ⟨hl, ihr hr, hLk, ?_⟩
          intro y hy
          rcases (mem_keys_insertFixup_of_compare aug lt hsep x y r).mp hy with rfl | hy
          · exact hcompat k y hx
          · exact hkR y hy
        split <;> simpa only [Ordered, keys_balanceRight_generic, keys_mk] using hnew
      · exact ht

/-- Complete insertion preserves the supplied BST ordering. -/
theorem ordered_insert (lt : α → α → Bool)
    (hsep : ∀ x y, lt x y ≠ true → lt y x ≠ true → x = y)
    (rel : α → α → Prop) (htrans : ∀ ⦃x y z⦄, rel x y → rel y z → rel x z) (hcompat : ∀ x y, lt x y = true → rel x y)
    (x : α) {t : AugmentedRBTree α β} (ht : Ordered rel t) :
    Ordered rel (insert aug lt x t) := by
  simpa only [insert, Ordered, keys_repaintBlack_generic] using
    ordered_insertFixup aug lt hsep rel htrans hcompat x ht

/-- Equal comparison keys are exactly equal intervals, including high endpoints. -/
theorem intervalLt_separates (i j : Interval)
    (hij : intervalLt i j ≠ true) (hji : intervalLt j i ≠ true) : i = j := by
  simp only [intervalLt, ne_eq, decide_eq_true_eq, Interval.low, Interval.high] at hij hji
  apply Prod.ext <;> omega

/-- The interval comparator is the strict lexicographic order. -/
theorem intervalLt_trans : ∀ ⦃i j k⦄, intervalLt i j = true → intervalLt j k = true → intervalLt i k = true := by
  intro i j k hij hjk
  simp only [intervalLt, decide_eq_true_eq, Interval.low, Interval.high] at *
  omega

/-- Lexicographic ordering implies the weak low-endpoint ordering used by search. -/
theorem intervalLt_low_le {i j : Interval} (h : intervalLt i j = true) : i.low ≤ j.low := by
  simp only [intervalLt, decide_eq_true_eq] at h
  omega

/-- Strict lexicographic BST ordering of the complete interval keys. -/
def IntervalBST (t : AugmentedRBTree Interval Nat) : Prop :=
  Ordered (fun i j => intervalLt i j = true) t

/-- The weaker ordering needed by the static interval-search algorithm. -/
def LowOrdered (t : AugmentedRBTree Interval Nat) : Prop :=
  Ordered (fun i j : Interval => i.low ≤ j.low) t

/-- Interval insertion retains all old intervals and adds the complete new interval. -/
theorem mem_keys_interval_insert (q i : Interval) (t : AugmentedRBTree Interval Nat) :
    i ∈ keys (insert IntervalTree.maxHighAug intervalLt q t) ↔ i = q ∨ i ∈ keys t :=
  mem_keys_insert_of_compare IntervalTree.maxHighAug intervalLt intervalLt_separates q i t

/-- Insertion preserves strict lexicographic interval BST ordering. -/
theorem intervalBST_insert (q : Interval) {t : AugmentedRBTree Interval Nat} (ht : IntervalBST t) :
    IntervalBST (insert IntervalTree.maxHighAug intervalLt q t) :=
  ordered_insert IntervalTree.maxHighAug intervalLt intervalLt_separates _ intervalLt_trans
    (fun _ _ h => h) q ht

/-- Weak low ordering is preserved even for inputs not strictly lexicographically ordered. -/
theorem lowOrdered_insert (q : Interval) {t : AugmentedRBTree Interval Nat} (ht : LowOrdered t) :
    LowOrdered (insert IntervalTree.maxHighAug intervalLt q t) :=
  ordered_insert IntervalTree.maxHighAug intervalLt intervalLt_separates (fun i j : Interval => i.low ≤ j.low)
    (fun _ _ _ h₁ h₂ => le_trans h₁ h₂) (fun _ _ h => intervalLt_low_le h) q ht

/-- A lexicographic interval BST satisfies the ordering used by interval search. -/
theorem IntervalBST.lowOrdered {t : AugmentedRBTree Interval Nat} (ht : IntervalBST t) : LowOrdered t :=
  List.Pairwise.imp (fun h => intervalLt_low_le h) ht

end CLRS.Chapter14.AugmentedRBTree
