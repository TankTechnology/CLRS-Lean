import CLRSLean.FourthEdition.Chapter_28.Section_28_1_Linear_Equations.ExecutableLUP.Pivot

/-!
# CLRS Section 28.1 - Costed direct elimination

The pointwise execution is identified with multiplication by the existing
Gaussian-elimination matrix and its field-operation sum is bounded.
-/

namespace CLRS
namespace Chapter28

open Matrix

variable {F : Type} [Field F]

private theorem elimination_mul_row_zero {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0)
    (j : Fin (n + 1)) :
    (elimination B h * B) 0 j = B 0 j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [elimination]
  · intro k _hk hk0
    have h0k : (0 : Fin (n + 1)) ≠ k := by exact Ne.symm hk0
    simp [elimination, h0k, hk0]
  · simp

private theorem elimination_mul_row_succ {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0)
    (i j : Fin (n + 1)) (hi : i ≠ 0) :
    (elimination B h * B) i j = B i j - (B i 0 / B 0 0) * B 0 j := by
  rw [Matrix.mul_apply]
  let S : Finset (Fin (n + 1)) := {i, 0}
  have hsubset : S ⊆ Finset.univ := by intro k _hk; simp
  have hsubsum :
      (∑ k ∈ S, elimination B h i k * B k j) =
        ∑ k : Fin (n + 1), elimination B h i k * B k j := by
    refine Finset.sum_subset hsubset ?_
    intro k _hk hnot
    have hne : k ≠ i ∧ k ≠ 0 := by
      simpa [S, eq_comm] using hnot
    have hik : i ≠ k := Ne.symm hne.1
    simp [elimination, hik, hne.2]
  rw [← hsubsum]
  have hpair : ({i, 0} : Finset (Fin (n + 1))) = insert i {0} := by
    ext k
    simp [eq_comm]
  dsimp [S]
  rw [hpair, Finset.sum_insert (by simpa using hi), Finset.sum_singleton]
  simp [elimination, hi]
  ring

/-- Erasing the entry counters gives multiplication by the existing
elimination matrix. -/
theorem eliminateWithCost_value {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0) :
    (eliminateWithCost B h).value = elimination B h * B := by
  ext i j
  by_cases hi : i = 0
  · subst i
    simp only [eliminateWithCost, eliminateEntryWithCost, ↓reduceIte]
    exact (elimination_mul_row_zero B h j).symm
  · simp only [eliminateWithCost, eliminateEntryWithCost, hi, ↓reduceIte]
    exact (elimination_mul_row_succ B h i j hi).symm

/-- The direct elimination execution zeroes column zero below the pivot. -/
theorem eliminateWithCost_col_zero {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0)
    (i : Fin n) : (eliminateWithCost B h).value (Fin.succ i) 0 = 0 := by
  rw [eliminateWithCost_value]
  exact elimination_mul_col_zero B h i

/-- At most three field operations are charged for each matrix entry. -/
theorem eliminateWithCost_work_le {n : Nat}
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (h : B 0 0 ≠ 0) :
    (eliminateWithCost B h).work ≤ 3 * (n + 1) ^ 2 := by
  unfold eliminateWithCost
  simp only
  calc
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (eliminateEntryWithCost B h i j).work)
        ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), 3 := by
          apply Finset.sum_le_sum
          intro i _hi
          apply Finset.sum_le_sum
          intro j _hj
          by_cases hi0 : i = 0
          · simp [eliminateEntryWithCost, hi0]
          · simp [eliminateEntryWithCost, hi0]
    _ = 3 * (n + 1) ^ 2 := by simp [pow_two]; ring

end Chapter28
end CLRS
