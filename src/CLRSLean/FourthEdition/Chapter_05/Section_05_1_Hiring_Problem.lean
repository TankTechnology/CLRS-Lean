import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions
import CLRSLean.Probability.FiniteExpectation
import Mathlib

open Finset
open Filter
open scoped BigOperators

/-!
# 5.1. The Hiring Problem

This file proves the finite symmetry calculation behind the CLRS hiring
problem.  At step {lit}`n+1`, the new candidate is hired exactly when the best among
the first {lit}`n+1` candidates is in the new candidate's position.  Under the
uniform rank model, that event has probability {lit}`1/(n+1)`.  Summing these
indicator expectations gives the harmonic number.

Main result:

- Theorem {lit}`CLRS.Chapter05.uniformAverage_indicator_singleton`: a singleton
  event in a finite uniform space has probability {lit}`1/m`.
- Theorem {lit}`CLRS.Chapter05.hireProbability_eq`: the hire probability at
  step {lit}`n+1` is {lit}`1/(n+1)`.
- Theorem {lit}`CLRS.Chapter05.expectedHiresByIndicators_eq_harmonic`: summing
  the indicator expectations gives the harmonic number.
- Theorem {lit}`CLRS.Chapter05.expectedHires_eq_harmonic`: the equivalent
  recurrence solution equals the harmonic number.
- Theorem {lit}`CLRS.Chapter05.expectedHires_isBigTheta_log`: expected hires
  grow logarithmically.

Status: `proved` for the finite rank-symmetry hiring model, including the
executable HIRE-ASSISTANT pseudocode ({lit}`CLRS.Chapter05.hireAssistant`).

Probability model: uses {lit}`CLRS.Probability.uniformAverage` from the shared
finite-expectation toolkit ({lit}`CLRSLean/Probability/FiniteExpectation.lean`);
uniform random-permutation sampling is supplied by Section 5.3
({lit}`CLRS.Chapter05.randomizeInPlace_uniform`, Lemma 5.4).

The executable layer below formalizes the HIRE-ASSISTANT pseudocode: the
first candidate is always hired, and each later candidate is hired exactly
when their rank is a new left-to-right maximum.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

/-! ## Finite uniform expectation model -/

/-- Uniform average over the finite sample space {lit}`{0, ..., m-1}`.
This is an alias for {lit}`CLRS.Probability.uniformAverage` for backward
compatibility. -/
noncomputable def uniformAverageRange (m : ℕ) (X : ℕ → ℝ) : ℝ :=
  uniformAverage m X

/-- A {lit}`0/1` indicator as a real-valued random variable.
Alias for {lit}`CLRS.Probability.indicator`. -/
def indicator (P : Prop) [Decidable P] : ℝ :=
  CLRS.Probability.indicator P

/-- In a finite uniform space of size {lit}`m`, a singleton event has probability {lit}`1/m`. -/
theorem uniformAverage_indicator_singleton {m j : ℕ} (hj : j ∈ range m) :
    uniformAverageRange m (fun i => indicator (i = j)) = 1 / (m : ℝ) := by
  unfold uniformAverageRange indicator
  rw [CLRS.Probability.uniformAverage_indicator_singleton hj]

/-! ## Hiring probabilities from symmetry -/

/--
At step {lit}`n+1`, index {lit}`n` is the new candidate's position in a rank-symmetry
sample space of size {lit}`n+1`.
-/
def newCandidateIsBest (n rankOfBest : ℕ) : Prop :=
  rankOfBest = n

instance newCandidateIsBestDecidable (n rankOfBest : ℕ) :
    Decidable (newCandidateIsBest n rankOfBest) :=
  inferInstanceAs (Decidable (rankOfBest = n))

/-- The probability that the new candidate is the best among the first {lit}`n+1`. -/
noncomputable def hireProbability (n : ℕ) : ℝ :=
  uniformAverageRange (n + 1) (fun rankOfBest => indicator (rankOfBest = n))

/-- The single-step hiring probability is {lit}`1/(n+1)` by finite symmetry. -/
theorem hireProbability_eq (n : ℕ) :
    hireProbability n = 1 / ((n : ℝ) + 1) := by
  classical
  have hn_mem : n ∈ range (n + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_self n
  have hsingleton :=
    uniformAverage_indicator_singleton (m := n + 1) (j := n) hn_mem
  simpa [hireProbability, Nat.cast_add, Nat.cast_one] using hsingleton

/-! ## Harmonic numbers -/

/-- The {lit}`n`-th harmonic number, written as {lit}`Σ_{i=0}^{n-1} 1/(i+1)`. -/
noncomputable def harmonic (n : ℕ) : ℝ :=
  ∑ i ∈ range n, 1 / ((i : ℝ) + 1)

@[simp] lemma harmonic_zero : harmonic 0 = 0 := by
  simp [harmonic]

/-- Successor recurrence for harmonic numbers. -/
lemma harmonic_succ (n : ℕ) :
    harmonic (n + 1) = harmonic n + 1 / ((n : ℝ) + 1) := by
  simp [harmonic, sum_range_succ]

/-- Harmonic numbers are positive once the index is positive. -/
lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < harmonic n := by
  refine Finset.sum_pos (fun i _ => div_pos (by norm_num) (by positivity)) ?_
  rw [Finset.nonempty_range_iff]
  exact Nat.ne_of_gt hn

/-! ## Expected number of hires -/

/-- Expected hires as a sum of indicator expectations. -/
noncomputable def expectedHiresByIndicators (n : ℕ) : ℝ :=
  ∑ i ∈ range n, hireProbability i

/-- Linearity of expectation reduces the hiring problem to the harmonic sum. -/
theorem expectedHiresByIndicators_eq_harmonic (n : ℕ) :
    expectedHiresByIndicators n = harmonic n := by
  unfold expectedHiresByIndicators harmonic
  refine Finset.sum_congr rfl ?_
  intro i _hi
  exact hireProbability_eq i

/--
Expected number of hires from {lit}`n` candidates, assuming the CLRS recurrence
obtained from the finite rank-symmetry argument.
-/
noncomputable def expectedHires : ℕ → ℝ
  | 0 => 0
  | n + 1 => expectedHires n + 1 / ((n : ℝ) + 1)

/-- The expected-hire recurrence has the harmonic-number closed form. -/
theorem expectedHires_eq_harmonic (n : ℕ) : expectedHires n = harmonic n := by
  induction' n with n ih
  · simp [expectedHires]
  · rw [expectedHires, harmonic_succ, ih]

/-- The recurrence and indicator-sum views of the expected hires agree. -/
theorem expectedHires_eq_expectedHiresByIndicators (n : ℕ) :
    expectedHires n = expectedHiresByIndicators n := by
  rw [expectedHires_eq_harmonic, expectedHiresByIndicators_eq_harmonic]

/-! ## Asymptotic growth -/

/--
The real harmonic sum used in this section agrees with Mathlib's rational
harmonic numbers after casting to {lit}`ℝ`.
-/
theorem harmonic_eq_mathlib_harmonic (n : ℕ) :
    harmonic n = (_root_.harmonic n : ℝ) := by
  simp [harmonic, _root_.harmonic, one_div]

/-- The real harmonic sum in this section has logarithmic growth. -/
theorem harmonic_isBigTheta_log :
    Chapter03.isBigTheta (fun n : ℕ => harmonic n) (fun n : ℕ => Real.log (n : ℝ)) := by
  have heq :
      (fun n : ℕ => harmonic n) =ᶠ[atTop] (fun n : ℕ => (_root_.harmonic n : ℝ)) := by
    filter_upwards with n
    exact harmonic_eq_mathlib_harmonic n
  have hO :
      Chapter03.isBigO (fun n : ℕ => harmonic n) (fun n : ℕ => Real.log (n : ℝ)) := by
    unfold Chapter03.isBigO
    exact heq.trans_isBigO Chapter03.isBigTheta_harmonic_log.1
  have hΩ :
      Chapter03.isBigOmega (fun n : ℕ => harmonic n) (fun n : ℕ => Real.log (n : ℝ)) := by
    unfold Chapter03.isBigOmega
    exact Chapter03.isBigTheta_harmonic_log.2.trans_eventuallyEq heq.symm
  exact ⟨hO, hΩ⟩

/-- The CLRS expected number of hires is logarithmic: {lit}`E[X] = Θ(log n)`. -/
theorem expectedHires_isBigTheta_log :
    Chapter03.isBigTheta expectedHires (fun n : ℕ => Real.log (n : ℝ)) := by
  have heq : expectedHires =ᶠ[atTop] harmonic := by
    filter_upwards with n
    exact expectedHires_eq_harmonic n
  have hExpectedHarmonic : Chapter03.isBigTheta expectedHires harmonic := by
    unfold Chapter03.isBigTheta Chapter03.isBigO Chapter03.isBigOmega
    exact ⟨heq.isBigO, heq.symm.isBigO⟩
  exact Chapter03.isBigTheta_trans hExpectedHarmonic harmonic_isBigTheta_log

/-! ## Executable HIRE-ASSISTANT (pseudocode execution) -/

/--
Count the records among `rest` given the best rank `best` seen so far: each rank
strictly greater than `best` is a new hire and becomes the running best.  This is
the inner loop of HIRE-ASSISTANT.
-/
def recordsFrom (best : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rest => if best < r then 1 + recordsFrom r rest else recordsFrom best rest

/--
**HIRE-ASSISTANT.**  The number of candidates hired when the interview order is
the rank sequence `ranks`: the first candidate is always hired, and each later
candidate is hired exactly when their rank exceeds every rank seen so far (they
are a left-to-right maximum).  The empty list hires nobody.
-/
def hireAssistant : List ℕ → ℕ
  | [] => 0
  | r :: rest => 1 + recordsFrom r rest

/-- One accumulator step adds a hire exactly when the new rank exceeds the
running best, and it advances the running best to the maximum. -/
theorem recordsFrom_step (best r : ℕ) (rest : List ℕ) :
    recordsFrom best (r :: rest) =
      (if best < r then 1 else 0) + recordsFrom (max best r) rest := by
  by_cases h : best < r
  · have hm : max best r = r := by omega
    simp [recordsFrom, h, hm]
  · have hm : max best r = best := by omega
    simp [recordsFrom, h, hm]

/-- The first candidate is always hired. -/
theorem hireAssistant_cons (r : ℕ) (rest : List ℕ) :
    hireAssistant (r :: rest) = 1 + recordsFrom r rest := rfl

/-- The accumulator counts at most one hire per candidate. -/
theorem recordsFrom_le_length (best : ℕ) : ∀ xs : List ℕ, recordsFrom best xs ≤ xs.length
  | [] => by simp [recordsFrom]
  | r :: rest => by
      simp [recordsFrom]
      split
      · have h := recordsFrom_le_length r rest
        omega
      · have h := recordsFrom_le_length best rest
        omega

/-- HIRE-ASSISTANT hires at most one candidate per interviewed candidate. -/
theorem hireAssistant_le_length : ∀ xs : List ℕ, hireAssistant xs ≤ xs.length
  | [] => by simp [hireAssistant]
  | r :: rest => by
      simp [hireAssistant]
      have h := recordsFrom_le_length r rest
      omega

/-- HIRE-ASSISTANT always hires at least one candidate when there is at least
one candidate. -/
theorem hireAssistant_pos {r : ℕ} {rest : List ℕ} : 0 < hireAssistant (r :: rest) := by
  simp [hireAssistant]

end Chapter05
end CLRS
