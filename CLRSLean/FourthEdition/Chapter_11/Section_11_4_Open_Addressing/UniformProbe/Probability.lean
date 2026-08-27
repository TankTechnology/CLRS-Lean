import CLRSLean.FourthEdition.Chapter_11.Section_11_4_Open_Addressing.UniformProbe.Counting
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# CLRS Section 11.4 - Uniform permutation probabilities

The counting result is converted to the without-replacement product already
used by the chapter.  Finite-expectation linearity then identifies the concrete
probe-count expectation with the existing tail sum and transports CLRS
Theorems 11.6--11.8 to the explicit sample space.
-/

namespace CLRS
namespace Chapter11

open Probability

/-- The without-replacement product is the quotient of descending
factorials. -/
theorem probeTail_eq_descFactorial_div (m n i : Nat) (hi : i ≤ m) :
    probeTail m n i = (n.descFactorial i : Real) / (m.descFactorial i : Real) := by
  by_cases hin : i ≤ n
  · rw [probeTail, Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range,
      Finset.prod_div_distrib]
    congr 1
    · rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Nat.cast_sub]
      exact Nat.le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hin)
    · rw [Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [Nat.cast_sub]
      exact Nat.le_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hi)
  · have hni : n < i := Nat.lt_of_not_ge hin
    have hnmem : n ∈ Finset.range i := Finset.mem_range.mpr hni
    have hnum : n.descFactorial i = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hni
    rw [probeTail, Finset.prod_eq_zero hnmem (by simp), hnum, Nat.cast_zero, zero_div]

/-- The explicit event probability is its satisfying-permutation count divided
by {lit}`m!`. -/
theorem uniformProbeTailProbability_eq_card {m i : Nat}
    (occupied : Finset (Fin m)) :
    uniformProbeTailProbability occupied i =
      ((occupiedPrefixPermutations occupied i).card : Real) / (m.factorial : Real) := by
  classical
  unfold uniformProbeTailProbability Probability.fintypeExpect
  rw [show (∑ σ : Equiv.Perm (Fin m), firstProbesOccupiedIndicator occupied i σ) =
      ((occupiedPrefixPermutations occupied i).card : Real) by
    simp [firstProbesOccupiedIndicator, indicator, occupiedPrefixPermutations]]
  simp [Fintype.card_perm]

/-- The probability of an occupied prefix under a uniform slot permutation is
exactly the chapter's without-replacement product {lit}`probeTail`. -/
theorem uniformProbeTailProbability_eq_probeTail {m i : Nat}
    (occupied : Finset (Fin m)) (hi : i ≤ m) :
    uniformProbeTailProbability occupied i = probeTail m occupied.card i := by
  rw [uniformProbeTailProbability_eq_card, firstProbesOccupied_card occupied hi]
  have hfactorial : ((m.factorial : Nat) : Real) =
      ((m - i).factorial : Real) * (m.descFactorial i : Real) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hi).symm
  have hrest : ((m - i).factorial : Real) ≠ 0 := by positivity
  have hprefix : ((m.descFactorial i : Nat) : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hi))
  rw [hfactorial, probeTail_eq_descFactorial_div m occupied.card i hi]
  push_cast
  field_simp

/-- The expected concrete unsuccessful-search probe count is the existing
tail-sum model. -/
theorem uniformUnsuccessfulExpectedProbes_eq {m : Nat}
    (occupied : Finset (Fin m)) :
    fintypeExpect (fun σ : Equiv.Perm (Fin m) =>
      (uniformUnsuccessfulProbeCount occupied σ : Real)) =
      expectedUnsuccessfulProbes m occupied.card := by
  calc
    fintypeExpect (fun σ : Equiv.Perm (Fin m) =>
        (uniformUnsuccessfulProbeCount occupied σ : Real)) =
        fintypeExpect (fun σ : Equiv.Perm (Fin m) =>
          ∑ i ∈ Finset.range (m + 1), firstProbesOccupiedIndicator occupied i σ) := by
            apply congrArg fintypeExpect
            funext σ
            exact uniformUnsuccessfulProbeCount_cast occupied σ
    _ = ∑ i ∈ Finset.range (m + 1),
        fintypeExpect (firstProbesOccupiedIndicator occupied i) := by
          exact fintypeExpect_sum (Finset.range (m + 1))
            (fun i σ => firstProbesOccupiedIndicator occupied i σ)
    _ = ∑ i ∈ Finset.range (m + 1), probeTail m occupied.card i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact uniformProbeTailProbability_eq_probeTail occupied
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = expectedUnsuccessfulProbes m occupied.card := rfl

/-- Explicit-sample-space form of CLRS Theorem 11.6. -/
theorem uniformUnsuccessfulExpectedProbes_le {m : Nat}
    (occupied : Finset (Fin m)) (hnotFull : occupied.card < m) :
    fintypeExpect (fun σ : Equiv.Perm (Fin m) =>
      (uniformUnsuccessfulProbeCount occupied σ : Real)) ≤
      1 / (1 - openLoadFactor m occupied.card) := by
  rw [uniformUnsuccessfulExpectedProbes_eq]
  exact expectedUnsuccessfulProbes_le m occupied.card hnotFull

/-- Explicit-sample-space form of CLRS Corollary 11.7 for insertion. -/
theorem uniformInsertionExpectedProbes_le {m : Nat}
    (occupied : Finset (Fin m)) (hnotFull : occupied.card < m) :
    fintypeExpect (fun σ : Equiv.Perm (Fin m) =>
      (uniformUnsuccessfulProbeCount occupied σ : Real)) ≤
      1 / (1 - openLoadFactor m occupied.card) :=
  uniformUnsuccessfulExpectedProbes_le occupied hnotFull

/-- The explicit successful-search average agrees with the chapter's insertion-
time average. -/
theorem uniformSuccessfulExpectedProbes_eq (m n : Nat) (hn : n ≤ m) :
    uniformSuccessfulExpectedProbes m n = expectedSuccessfulProbes m n := by
  unfold uniformSuccessfulExpectedProbes expectedSuccessfulProbes
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [uniformUnsuccessfulExpectedProbes_eq, canonicalOccupied_card]
  exact le_trans (Nat.le_of_lt (Finset.mem_range.mp hj)) hn

/-- Explicit-sample-space logarithmic form of CLRS Theorem 11.8. -/
theorem uniformSuccessfulExpectedProbes_le_ln (m n : Nat)
    (hn : n < m) (hnpos : 0 < n) :
    uniformSuccessfulExpectedProbes m n ≤
      (1 / openLoadFactor m n) * Real.log (1 / (1 - openLoadFactor m n)) := by
  rw [uniformSuccessfulExpectedProbes_eq m n (le_of_lt hn)]
  exact expectedSuccessfulProbes_le_ln m n hn hnpos

end Chapter11
end CLRS
