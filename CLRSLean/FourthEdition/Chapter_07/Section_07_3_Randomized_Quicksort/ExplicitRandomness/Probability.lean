import CLRSLean.FourthEdition.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability
import CLRSLean.Probability.FiniteExpectation

/-!
# Uniform random priorities for quicksort

A permutation of `Fin n` assigns a distinct random priority to every rank:
`pos pi x` is the priority of rank `x`.  The pivot of any recursive subproblem
is the rank of minimum priority in that subproblem.  This single finite sample
space couples all recursive pivot choices.

The expectation proof below uses linearity, so it does not require pairwise
independence of comparison indicators.  The symmetry actually needed by the
algorithm -- every member of a nonempty subproblem is equally likely to have
minimum priority -- is proved by the transposition bijection in
`Comparison_Probability` and exposed here in `fintypeExpect` form.
-/

namespace CLRS
namespace Chapter07

open CLRS.Probability

/-- The expectation of a uniform finite event indicator is its filtered-card
ratio. -/
theorem uniformEvent_expectation_eq_filterRatio {Omega : Type}
    [Fintype Omega] [DecidableEq Omega] (event : Omega -> Prop)
    [DecidablePred event] :
    fintypeExpect (fun sample : Omega => indicator (event sample)) =
      (((Finset.univ : Finset Omega).filter event).card : Real) /
        (Fintype.card Omega : Real) := by
  unfold fintypeExpect indicator
  congr 1
  simp

/-- In the uniform-priority model, every rank in a nonempty recursive
subproblem is equally likely to be selected as its pivot. -/
theorem priorityPivot_uniform {n : Nat} (subproblem : Finset (Fin n))
    (hne : subproblem.Nonempty) (pivot : Fin n) (hpivot : pivot ∈ subproblem) :
    fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
      @indicator (IsFirstIn subproblem pivot priority)
        (Classical.propDecidable _)) =
      1 / (subproblem.card : Real) := by
  rw [uniformEvent_expectation_eq_filterRatio]
  simpa [Fintype.card_perm, Fintype.card_fin] using
    isFirst_prob subproblem hne pivot hpivot

/-- The indicator expectation for one rank pair is the comparison probability
proved by the permutation-symmetry argument. -/
theorem comparedIndicator_expectation (n : Nat) (i j : Fin n)
    (hij : i.val < j.val) :
    fintypeExpect (fun priority : Equiv.Perm (Fin n) =>
      @indicator (comparedInQuicksort n i.val j.val hij j.isLt priority)
        (Classical.propDecidable _)) =
      (2 : Real) / ((j.val - i.val + 1 : Nat) : Real) := by
  rw [uniformEvent_expectation_eq_filterRatio]
  simpa [Fintype.card_perm, Fintype.card_fin] using
    compared_prob n i.val j.val hij j.isLt

end Chapter07
end CLRS
