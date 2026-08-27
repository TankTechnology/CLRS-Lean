import CLRSLean.FourthEdition.Chapter_05.Section_05_1_Hiring_Problem
import CLRSLean.FourthEdition.Chapter_05.Section_05_3_Randomized_Algorithms

/-!
# 5.3. RANDOMIZED-HIRE-ASSISTANT

This file joins the executable `hireAssistant` loop to the uniform
randomization interface from Section 5.3.  It also packages the textbook
expected hiring-cost calculation without conflating two distinct facts:

* randomization transports the execution expectation to the uniform
  permutation space;
* the rank-symmetry calculation identifies the latter with `expectedHires`.

The second fact is represented by `HiringExpectationBridge`.  Keeping it
explicit makes the remaining execution-to-analysis boundary auditable.
-/

namespace CLRS
namespace Chapter05

open Filter
open CLRS.Probability

/-- Read a permutation as the list of candidate ranks in interview order. -/
def permutationRanks {n : Nat} (sigma : Equiv.Perm (Fin n)) : List Nat :=
  (List.finRange n).map (fun i => (sigma i : Nat))

/-- **RANDOMIZED-HIRE-ASSISTANT.** Randomize the interview order, then run
the executable hiring loop on the resulting rank list. -/
noncomputable def randomizedHireAssistant {n : Nat} (choices : ChoiceVector n) : Nat :=
  hireAssistant (permutationRanks (randomizeInPlace choices))

/-- Expected hiring cost in the finite rank-symmetry analysis. -/
noncomputable def expectedHiringCost (hireCost : Real) (n : Nat) : Real :=
  hireCost * expectedHires n

/-- The expected hiring cost is the hiring-cost constant times the harmonic
number. -/
theorem expectedHiringCost_eq_harmonic (hireCost : Real) (n : Nat) :
    expectedHiringCost hireCost n = hireCost * harmonic n := by
  rw [expectedHiringCost, expectedHires_eq_harmonic]

/-- Scaling the expected number of hires by a fixed nonnegative hiring cost
preserves its logarithmic upper bound. -/
theorem expectedHiringCost_isBigO_log (hireCost : Real) (_hcost : 0 <= hireCost) :
    Chapter03.isBigO (expectedHiringCost hireCost)
      (fun n : Nat => Real.log (n : Real)) := by
  unfold expectedHiringCost Chapter03.isBigO
  exact expectedHires_isBigTheta_log.1.const_mul_left hireCost

/-- Expected number of hires after running the randomized executable. -/
noncomputable def randomizedExpectedHires (n : Nat) : Real :=
  fintypeExpect (fun choices : ChoiceVector n => (randomizedHireAssistant choices : Real))

/-- Expected number of hires when the permutation itself is sampled uniformly. -/
noncomputable def uniformPermutationExpectedHires (n : Nat) : Real :=
  fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
    (hireAssistant (permutationRanks sigma) : Real))

/-- Uniform randomization transports the executable hire count exactly to the
uniform-permutation sample space. -/
theorem randomizedExpectedHires_eq_uniform (n : Nat) :
    randomizedExpectedHires n = uniformPermutationExpectedHires n := by
  simpa [randomizedExpectedHires, uniformPermutationExpectedHires,
    randomizedHireAssistant, randomizeInPlace] using
    (fintypeExpect_equiv (randomizeInPlace_equiv n)
      (fun sigma : Equiv.Perm (Fin n) =>
        (hireAssistant (permutationRanks sigma) : Real)))

/-- The actual expected cost of the randomized executable. -/
noncomputable def randomizedExpectedHiringCost (hireCost : Real) (n : Nat) : Real :=
  fintypeExpect (fun choices : ChoiceVector n =>
    hireCost * (randomizedHireAssistant choices : Real))

/-- Expected cost over a directly sampled uniform permutation. -/
noncomputable def uniformPermutationExpectedHiringCost (hireCost : Real) (n : Nat) : Real :=
  fintypeExpect (fun sigma : Equiv.Perm (Fin n) =>
    hireCost * (hireAssistant (permutationRanks sigma) : Real))

/-- Randomization transports the expected execution cost exactly to the
uniform-permutation model. -/
theorem randomizedExpectedHiringCost_eq_uniform (hireCost : Real) (n : Nat) :
    randomizedExpectedHiringCost hireCost n =
      uniformPermutationExpectedHiringCost hireCost n := by
  simpa [randomizedExpectedHiringCost, uniformPermutationExpectedHiringCost,
    randomizedHireAssistant, randomizeInPlace] using
    (fintypeExpect_equiv (randomizeInPlace_equiv n)
      (fun sigma : Equiv.Perm (Fin n) =>
        hireCost * (hireAssistant (permutationRanks sigma) : Real)))

/-- The remaining textbook bridge: the expectation of the executable record
counter over uniform permutations agrees with the rank-symmetry recurrence. -/
def HiringExpectationBridge : Prop :=
  forall n, uniformPermutationExpectedHires n = expectedHires n

/-- Under the explicit execution-to-analysis bridge, the randomized
executable has the analytic expected hiring cost. -/
theorem randomizedExpectedHiringCost_eq (hbridge : HiringExpectationBridge)
    (hireCost : Real) (n : Nat) :
    randomizedExpectedHiringCost hireCost n = expectedHiringCost hireCost n := by
  rw [randomizedExpectedHiringCost_eq_uniform]
  unfold uniformPermutationExpectedHiringCost expectedHiringCost
  unfold fintypeExpect
  have hb := hbridge n
  unfold uniformPermutationExpectedHires fintypeExpect at hb
  calc
    (Finset.univ.sum fun sigma : Equiv.Perm (Fin n) =>
        hireCost * (hireAssistant (permutationRanks sigma) : Real)) /
        (Fintype.card (Equiv.Perm (Fin n)) : Real) =
      (hireCost * (Finset.univ.sum fun sigma : Equiv.Perm (Fin n) =>
        (hireAssistant (permutationRanks sigma) : Real))) /
        (Fintype.card (Equiv.Perm (Fin n)) : Real) := by
          rw [Finset.mul_sum]
    _ = hireCost *
        ((Finset.univ.sum fun sigma : Equiv.Perm (Fin n) =>
          (hireAssistant (permutationRanks sigma) : Real)) /
            (Fintype.card (Equiv.Perm (Fin n)) : Real)) := by ring
    _ = hireCost * expectedHires n := by rw [hb]

/-- RANDOMIZED-HIRE-ASSISTANT has logarithmic expected hiring cost once the
uniform-permutation record-count bridge is supplied. -/
theorem randomizedExpectedHiringCost_isBigO_log
    (hbridge : HiringExpectationBridge) (hireCost : Real) (hcost : 0 <= hireCost) :
    Chapter03.isBigO (randomizedExpectedHiringCost hireCost)
      (fun n : Nat => Real.log (n : Real)) := by
  have heq : randomizedExpectedHiringCost hireCost = expectedHiringCost hireCost := by
    funext n
    exact randomizedExpectedHiringCost_eq hbridge hireCost n
  rw [heq]
  exact expectedHiringCost_isBigO_log hireCost hcost

end Chapter05
end CLRS
