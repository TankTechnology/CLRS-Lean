import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Hiring.RecordProbability

/-!
# Expected record count of RANDOMIZED-HIRE-ASSISTANT

The executable counter is first rewritten as a finite sum of prefix-record
indicators.  Finite linearity of expectation and the `1/(i+1)` record
probability then give the harmonic sum.  No independence between record events
is assumed or needed.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-- Casting the executable hire count gives the real-valued sum of its record
indicators. -/
theorem hireAssistant_permutationRanks_cast {n : Nat}
    (sigma : Equiv.Perm (Fin n)) :
    (hireAssistant (permutationRanks sigma) : Real) =
      ∑ i : Fin n, indicator (permutationPrefixRecordAt sigma i) := by
  rw [hireAssistant_permutationRanks_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hrecord : permutationPrefixRecordAt sigma i
  · simp [CLRS.Chapter05.indicator, CLRS.Probability.indicator, hrecord]
  · simp [CLRS.Chapter05.indicator, CLRS.Probability.indicator, hrecord]

/-- The executable record counter over uniform permutations has harmonic
expectation. -/
theorem uniformPermutationExpectedHires_eq_harmonic (n : Nat) :
    uniformPermutationExpectedHires n = harmonic n := by
  unfold uniformPermutationExpectedHires
  rw [show (fun sigma : Equiv.Perm (Fin n) =>
      (hireAssistant (permutationRanks sigma) : Real)) =
      (fun sigma : Equiv.Perm (Fin n) =>
        ∑ i : Fin n, indicator (permutationPrefixRecordAt sigma i)) by
    funext sigma
    exact hireAssistant_permutationRanks_cast sigma]
  calc
    fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
        ∑ i : Fin n, indicator (permutationPrefixRecordAt sigma i)) =
        ∑ i : Fin n, fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
          indicator (permutationPrefixRecordAt sigma i)) := by
      simpa using fintypeExpect_sum (Finset.univ : Finset (Fin n))
        (fun (i : Fin n) (sigma : Equiv.Perm (Fin n)) =>
          indicator (permutationPrefixRecordAt sigma i))
    _ = ∑ i : Fin n, 1 / ((i.val + 1 : Nat) : Real) := by
      apply Finset.sum_congr rfl
      intro i _
      exact prefixRecord_probability i
    _ = harmonic n := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i : Nat => 1 / ((i + 1 : Nat) : Real)) n]
      simp [harmonic]

/-- The former open bridge is now inhabited by the finite permutation proof. -/
theorem hiringExpectationBridge : HiringExpectationBridge := by
  intro n
  rw [uniformPermutationExpectedHires_eq_harmonic,
    expectedHires_eq_harmonic]

/-- The expected number of hires of the randomized executable is exactly the
textbook recurrence value. -/
theorem randomizedExpectedHires_eq (n : Nat) :
    randomizedExpectedHires n = expectedHires n := by
  rw [randomizedExpectedHires_eq_uniform]
  exact hiringExpectationBridge n

/-- The randomized executable has exactly the analytic expected hiring cost,
with no bridge premise. -/
theorem randomizedExpectedHiringCost_eq (hireCost : Real) (n : Nat) :
    randomizedExpectedHiringCost hireCost n = expectedHiringCost hireCost n :=
  randomizedExpectedHiringCost_eq_of_bridge hiringExpectationBridge hireCost n

/-- RANDOMIZED-HIRE-ASSISTANT has logarithmic expected hiring cost. -/
theorem randomizedExpectedHiringCost_isBigO_log
    (hireCost : Real) (hcost : 0 <= hireCost) :
    Chapter03.isBigO (randomizedExpectedHiringCost hireCost)
      (fun n : Nat => Real.log (n : Real)) :=
  randomizedExpectedHiringCost_isBigO_log_of_bridge
    hiringExpectationBridge hireCost hcost

end Chapter05
end CLRS
