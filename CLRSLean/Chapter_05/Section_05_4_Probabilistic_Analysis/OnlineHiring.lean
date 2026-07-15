import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# CLRS §5.4.4 — The On-line Hiring Problem

We model the on-line hiring problem (CLRS §5.4.4).  {lit}`n` candidates arrive
in random order (uniform over all {lit}`n!` permutations).  After each interview
the algorithm must decide immediately whether to hire the current candidate and
stop, or to continue.  The goal is to maximize the probability of hiring the
**best** candidate.

The threshold strategy interviews the first {lit}`k` applicants without hiring
(the *observation phase*), then hires the first applicant who is better than
every applicant seen so far.

**Status:** The finite record-selection strategy is executable and comes with
exact {lit}`some` and {lit}`none` contracts.  The harmonic closed form for its
success probability and the asymptotic {lit}`1/e` result are **deferred**.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

namespace OnlineHiring

/-! ## Model

The sample space is the uniform distribution over {lit}`Equiv.Perm (Fin n)`.
Candidate {lit}`i` has **score** {lit}`π i` ({lit}`0` = best, {lit}`n-1` =
worst).  The absolute best candidate is the one with score {lit}`0`.
-/

/--
The absolute best candidate: the one mapped to {lit}`0` (smallest score) by
the permutation.
-/
def isAbsoluteBest {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (π i).val = 0

/--
Candidate {lit}`j` is a record when its score is better (numerically smaller)
than every earlier candidate's score.
-/
def isRecordAt {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : Prop :=
  ∀ i : Fin n, i.val < j.val → (π j).val < (π i).val

instance {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    Decidable (isRecordAt π j) := by
  unfold isRecordAt
  infer_instance

/--
The record positions at or after the natural-number observation threshold.
-/
def eligiblePositions {n : ℕ} (k : ℕ)
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => k ≤ j.val ∧ isRecordAt π j

/-- The executable threshold strategy selects the earliest eligible record. -/
def hiringStrategy {n : ℕ} (k : ℕ)
    (π : Equiv.Perm (Fin n)) : Option (Fin n) :=
  let eligible := eligiblePositions k π
  if h : eligible.Nonempty then some (eligible.min' h) else none

/-- Membership in the executable candidate set is exactly the threshold and
record condition. -/
theorem mem_eligiblePositions_iff {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n} :
    j ∈ eligiblePositions k π ↔ k ≤ j.val ∧ isRecordAt π j := by
  simp [eligiblePositions]

/-- Exact contract for a successful threshold selection: the returned
position is an eligible record and is no later than any other eligible record.
-/
theorem hiringStrategy_some_iff {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n} :
    hiringStrategy k π = some j ↔
      k ≤ j.val ∧ isRecordAt π j ∧
        ∀ i : Fin n, k ≤ i.val → isRecordAt π i → j ≤ i := by
  classical
  unfold hiringStrategy
  dsimp only
  split_ifs with hne
  · constructor
    · intro h
      have hj : (eligiblePositions k π).min' hne = j := Option.some.inj h
      subst j
      have hmem : (eligiblePositions k π).min' hne ∈ eligiblePositions k π :=
        Finset.min'_mem _ hne
      have helig := mem_eligiblePositions_iff.mp hmem
      refine ⟨helig.1, helig.2, ?_⟩
      intro i hi hrecord
      exact Finset.min'_le _ i (mem_eligiblePositions_iff.mpr ⟨hi, hrecord⟩)
    · rintro ⟨hj, hrecord, hleast⟩
      apply congrArg some
      apply le_antisymm
      · exact Finset.min'_le _ j (mem_eligiblePositions_iff.mpr ⟨hj, hrecord⟩)
      · have hminmem :
            (eligiblePositions k π).min' hne ∈ eligiblePositions k π :=
          Finset.min'_mem _ hne
        have hmin := mem_eligiblePositions_iff.mp hminmem
        exact hleast _ hmin.1 hmin.2
  · constructor
    · intro h
      simp at h
    · rintro ⟨hj, hrecord, _⟩
      exact False.elim (hne ⟨j, mem_eligiblePositions_iff.mpr ⟨hj, hrecord⟩⟩)

/-- Exact contract for failure: there is no record position at or after the
observation threshold. -/
theorem hiringStrategy_none_iff {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} :
    hiringStrategy k π = none ↔
      ∀ j : Fin n, k ≤ j.val → ¬ isRecordAt π j := by
  classical
  constructor
  · intro hnone j hj hrecord
    have hne : (eligiblePositions k π).Nonempty :=
      ⟨j, mem_eligiblePositions_iff.mpr ⟨hj, hrecord⟩⟩
    simp [hiringStrategy, hne] at hnone
  · intro hnone
    have hempty : ¬ (eligiblePositions k π).Nonempty := by
      rintro ⟨j, hjmem⟩
      have hj := mem_eligiblePositions_iff.mp hjmem
      exact hnone j hj.1 hj.2
    simp [hiringStrategy, hempty]

/-- A successful hire occurs at or after the observation threshold. -/
theorem hiringStrategy_after_observation {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n}
    (h : hiringStrategy k π = some j) : k ≤ j.val :=
  (hiringStrategy_some_iff.mp h).1

/-- A successfully hired candidate is a record at their interview position. -/
theorem hiringStrategy_record {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n}
    (h : hiringStrategy k π = some j) : isRecordAt π j :=
  (hiringStrategy_some_iff.mp h).2.1

/-- Finite success probability of the threshold strategy under the uniform
distribution on permutations of the candidate positions. -/
noncomputable def probHireBest (n k : ℕ) : ℝ := by
  classical
  exact fintypeExpect fun π : Equiv.Perm (Fin n) =>
    match hiringStrategy k π with
    | some i => if isAbsoluteBest π i then 1 else 0
    | none => 0

end OnlineHiring

end Chapter05
end CLRS
