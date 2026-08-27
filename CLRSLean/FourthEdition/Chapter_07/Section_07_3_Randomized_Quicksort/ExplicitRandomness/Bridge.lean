import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort
import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.ExplicitRandomness.Execution

/-!
# Expectation bridge for executable random-priority quicksort

The natural-number comparison counter from `Execution` is averaged over the
explicit finite sample space `Equiv.Perm (Fin n)`.  Its pointwise indicator
decomposition, finite linearity of expectation, and the proved permutation
symmetry for each pair yield the existing CLRS pairwise-probability sum.  The
already-proved algebraic sum theorem then supplies the closed form and the
`Theta(n log n)` result.
-/

namespace CLRS
namespace Chapter07

open CLRS.Probability
open Chapter03

/-- Expected comparison count of the executable random-priority model. -/
noncomputable def explicitRandomizedQuicksortExpectedComparisons (n : Nat) : Real :=
  fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
    (randomizedQuicksortComparisonCount priority : Real))

/-- The expectation of the executable comparison counter is the CLRS sum of
pairwise comparison probabilities.  No independence assumption is used:
finite linearity of expectation suffices. -/
theorem explicitRandomizedQuicksortExpectedComparisons_eq_pairSum (n : Nat) :
    explicitRandomizedQuicksortExpectedComparisons n =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        if i < j then (2 : Real) / ((j - i + 1 : Nat) : Real) else 0 := by
  unfold explicitRandomizedQuicksortExpectedComparisons
  rw [show (fun priority : Equiv.Perm (Fin n) =>
      (randomizedQuicksortComparisonCount priority : Real)) =
      (fun priority : Equiv.Perm (Fin n) =>
        ∑ i : Fin n, ∑ j : Fin n,
          if hij : i.val < j.val then
            @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
              (Classical.propDecidable _)
          else 0) by
    funext priority
    exact randomizedQuicksortComparisonCount_cast priority]
  calc
    fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
        ∑ i : Fin n, ∑ j : Fin n,
          if hij : i.val < j.val then
            @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
              (Classical.propDecidable _)
          else 0) =
        ∑ i : Fin n, fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
          ∑ j : Fin n,
            if hij : i.val < j.val then
              @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
                (Classical.propDecidable _)
            else 0) := by
      simpa using
        (fintypeExpect_sum (Ω := Equiv.Perm (Fin n))
          (Finset.univ : Finset (Fin n))
          (fun i priority =>
            ∑ j : Fin n,
              if hij : i.val < j.val then
                @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
                  (Classical.propDecidable _)
              else 0))
    _ = ∑ i : Fin n, ∑ j : Fin n,
          fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
            if hij : i.val < j.val then
              @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
                (Classical.propDecidable _)
            else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using
        (fintypeExpect_sum (Ω := Equiv.Perm (Fin n))
          (Finset.univ : Finset (Fin n))
          (fun j priority =>
            if hij : i.val < j.val then
              @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
                (Classical.propDecidable _)
            else 0))
    _ = ∑ i : Fin n, ∑ j : Fin n,
          if i.val < j.val then
            (2 : Real) / ((j.val - i.val + 1 : Nat) : Real)
          else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i.val < j.val
      · simp only [dif_pos hij, if_pos hij]
        exact comparedIndicator_expectation n i j hij
      · simp [hij, fintypeExpect]
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          if i < j then (2 : Real) / ((j - i + 1 : Nat) : Real) else 0 := by
      have hinner (i : Fin n) :
          (∑ j : Fin n,
            if i.val < j.val then
              (2 : Real) / ((j.val - i.val + 1 : Nat) : Real)
            else 0) =
          ∑ j ∈ Finset.range n,
            if i.val < j then
              (2 : Real) / ((j - i.val + 1 : Nat) : Real)
            else 0 := by
        rw [Fin.sum_univ_eq_sum_range
          (fun j : Nat =>
            if i.val < j then
              (2 : Real) / ((j - i.val + 1 : Nat) : Real)
            else 0) n]
      simp_rw [hinner]
      rw [Fin.sum_univ_eq_sum_range
        (fun i : Nat =>
          ∑ j ∈ Finset.range n,
            if i < j then
              (2 : Real) / ((j - i + 1 : Nat) : Real)
            else 0) n]

/-- The explicit finite execution has exactly the previously proved CLRS
expected-comparison closed form. -/
theorem explicitRandomizedQuicksortExpectedComparisons_eq (n : Nat) :
    explicitRandomizedQuicksortExpectedComparisons n = expectedComparisonsReal n := by
  rw [explicitRandomizedQuicksortExpectedComparisons_eq_pairSum]
  have h := sum_compared_prob_eq_expectedComparisons n
  dsimp [expectedComparisonsReal]
  rw [← h]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp [hij]
  · simp [hij]

/-- The executable finite model inherits the existing textbook
`Theta(n log n)` theorem through the exact expectation bridge. -/
theorem explicitRandomizedQuicksortExpectedComparisons_isBigTheta_nlogn :
    isBigTheta explicitRandomizedQuicksortExpectedComparisons
      (fun n : Nat => (n : Real) * Real.log (n : Real)) := by
  have hfun : explicitRandomizedQuicksortExpectedComparisons = expectedComparisonsReal := by
    funext n
    exact explicitRandomizedQuicksortExpectedComparisons_eq n
  rw [hfun]
  exact expectedComparisons_isBigTheta_nlogn

end Chapter07
end CLRS
