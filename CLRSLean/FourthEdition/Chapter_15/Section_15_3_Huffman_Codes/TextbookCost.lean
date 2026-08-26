import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes

/-!
# Huffman textbook cost

CLRS equation (15.4) defines the cost of a prefix-code tree as the sum of each
character's frequency times its depth.  The core development uses the
equivalent internal-node-frequency recurrence.  This module proves the bridge.
-/

open scoped BigOperators

namespace CLRS.HuffmanV2

/-- CLRS equation (15.4): `B(T) = ∑ c.freq * d_T(c)`. -/
def textbookCost (t : HuffTree) : Nat :=
  ∑ s ∈ alphabet t, freqOf s t * (depthOf s t).getD 0

theorem rootFreq_eq_sum_freqOf (t : HuffTree) (hcons : consistent t) :
    rootFreq t = ∑ s ∈ alphabet t, freqOf s t := by
  induction t with
  | htLeaf s f => simp [rootFreq, alphabet, freqOf]
  | htInner l r ihl ihr =>
      rcases hcons with ⟨hcl, hcr, hdisj⟩
      have hleft :
          (∑ s ∈ alphabet l, freqOf s (HuffTree.htInner l r)) =
            ∑ s ∈ alphabet l, freqOf s l := by
        apply Finset.sum_congr rfl
        intro s hs
        have hnot : s ∉ alphabet r := Finset.disjoint_left.mp hdisj hs
        simp [freqOf, freqOf_eq_zero_of_not_mem s r hnot]
      have hright :
          (∑ s ∈ alphabet r, freqOf s (HuffTree.htInner l r)) =
            ∑ s ∈ alphabet r, freqOf s r := by
        apply Finset.sum_congr rfl
        intro s hs
        have hnot : s ∉ alphabet l := Finset.disjoint_right.mp hdisj hs
        simp [freqOf, freqOf_eq_zero_of_not_mem s l hnot]
      rw [rootFreq, alphabet, Finset.sum_union hdisj, hleft, hright,
        ← ihl hcl, ← ihr hcr]

private theorem textbookCost_inner
    (l r : HuffTree) (hcl : consistent l) (hcr : consistent r)
    (hdisj : Disjoint (alphabet l) (alphabet r)) :
    textbookCost (HuffTree.htInner l r) =
      textbookCost l + textbookCost r + rootFreq l + rootFreq r := by
  have hleft :
      (∑ s ∈ alphabet l,
          freqOf s (HuffTree.htInner l r) *
            (depthOf s (HuffTree.htInner l r)).getD 0) =
        textbookCost l + rootFreq l := by
    calc
      _ = ∑ s ∈ alphabet l,
          (freqOf s l * (depthOf s l).getD 0 + freqOf s l) := by
            apply Finset.sum_congr rfl
            intro s hs
            have hnot : s ∉ alphabet r := Finset.disjoint_left.mp hdisj hs
            rw [depthOf_getD_inner_of_mem_left hs]
            simp [freqOf, freqOf_eq_zero_of_not_mem s r hnot,
              Nat.mul_add]
      _ = (∑ s ∈ alphabet l, freqOf s l * (depthOf s l).getD 0) +
          ∑ s ∈ alphabet l, freqOf s l := Finset.sum_add_distrib
      _ = textbookCost l + rootFreq l := by
          rw [rootFreq_eq_sum_freqOf l hcl]
          rfl
  have hright :
      (∑ s ∈ alphabet r,
          freqOf s (HuffTree.htInner l r) *
            (depthOf s (HuffTree.htInner l r)).getD 0) =
        textbookCost r + rootFreq r := by
    calc
      _ = ∑ s ∈ alphabet r,
          (freqOf s r * (depthOf s r).getD 0 + freqOf s r) := by
            apply Finset.sum_congr rfl
            intro s hs
            have hnot : s ∉ alphabet l := Finset.disjoint_right.mp hdisj hs
            rw [depthOf_getD_inner_of_mem_right hs hnot]
            simp [freqOf, freqOf_eq_zero_of_not_mem s l hnot,
              Nat.mul_add]
      _ = (∑ s ∈ alphabet r, freqOf s r * (depthOf s r).getD 0) +
          ∑ s ∈ alphabet r, freqOf s r := Finset.sum_add_distrib
      _ = textbookCost r + rootFreq r := by
          rw [rootFreq_eq_sum_freqOf r hcr]
          rfl
  rw [textbookCost, alphabet, Finset.sum_union hdisj, hleft, hright]
  omega

/--
The internal-node recurrence used by the executable development is exactly
CLRS equation (15.4) on every consistent prefix-code tree.
-/
theorem textbookCost_eq_cost (t : HuffTree) (hcons : consistent t) :
    textbookCost t = cost t := by
  induction t with
  | htLeaf s f => simp [textbookCost, alphabet, freqOf, depthOf, cost]
  | htInner l r ihl ihr =>
      rcases hcons with ⟨hcl, hcr, hdisj⟩
      rw [textbookCost_inner l r hcl hcr hdisj, cost, ihl hcl, ihr hcr]

/-- The public Huffman optimum theorem can be read directly with equation (15.4). -/
theorem huffmanOfFreqs_textbookCost_le (xs : List (Nat × Nat))
    (h_nodup : (xs.map Prod.fst).Nodup)
    (h_pos : ∀ p ∈ xs, p.2 > 0)
    (h_nonempty : xs ≠ [])
    (u : HuffTree) (h_cons_u : consistent u)
    (h_same : sameFreqs (huffmanOfFreqs xs) u) :
    textbookCost (huffmanOfFreqs xs) ≤ textbookCost u := by
  have hopt := optimum_huffman_freqs xs h_nodup h_pos h_nonempty
  rw [textbookCost_eq_cost _ hopt.1, textbookCost_eq_cost _ h_cons_u]
  exact hopt.2.2 u h_cons_u h_same

end CLRS.HuffmanV2
