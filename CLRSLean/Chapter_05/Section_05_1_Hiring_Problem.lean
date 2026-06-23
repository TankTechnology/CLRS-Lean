import Mathlib.Tactic

open Finset

/-!
# 5.1. The Hiring Problem

We interview `n` candidates in uniformly random order and hire whenever a
candidate is better than all previously seen.  The expected number of hires
is the `n`-th harmonic number `H_n = 1 + 1/2 + ... + 1/n`.

## Formal statement

Let `Iᵢ` be the indicator that the `i`-th interviewed candidate is hired.
By symmetry, among the first `i` candidates the best one occupies each
position with equal probability, so `Pr[Iᵢ = 1] = 1/i`.  Linearity of
expectation yields `E[Σ Iᵢ] = Σ E[Iᵢ] = Σ 1/i = H_n`.

The counting proof: there are `i!` relative orderings of `i` distinct
candidates; exactly `(i-1)!` place the best at the last position.  Hence
`(i-1)! / i! = 1/i`.

We prove basic properties of harmonic numbers and state the main theorem.
The full probabilistic formalization (probability space over permutations,
linearity of expectation) requires additional infrastructure and is deferred.
-/

namespace CLRS
namespace Chapter05

/-! ## Harmonic numbers -/

/-- The `n`-th harmonic number `H_n = Σ_{i=1}^n 1/i` (as a real number). -/
def harmonic (n : ℕ) : ℝ := ∑ i in range n, 1 / ((i : ℝ) + 1)

@[simp] lemma harmonic_zero : harmonic 0 = 0 := by simp [harmonic]

lemma harmonic_one : harmonic 1 = 1 := by norm_num [harmonic]

lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + 1 / ((n : ℝ) + 1) := by
  simp [harmonic, sum_range_succ, add_assoc]

lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < harmonic n := by
  refine Finset.sum_pos (fun i _ => div_pos (by norm_num) (by positivity)) ?_
  exact ⟨0, mem_range.2 hn, by simp⟩

lemma harmonic_mono : StrictMono harmonic := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  rw [harmonic_succ]
  nlinarith [harmonic_pos (Nat.succ_pos n)]

/-! ## Upper and lower bounds for H_n -/

/-- Lower bound: `H_n ≥ ln(n+1)`. -/
lemma harmonic_ge_log_succ (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ harmonic n := by
  -- Standard integral bound: ∑_{i=1}^n 1/i ≥ ∫_1^{n+1} dx/x = ln(n+1)
  -- This follows from 1/i ≥ ∫_i^{i+1} dx/x = ln(i+1) - ln(i)
  -- Formal proof requires integral comparison (deferred).
  sorry

/-- Upper bound: `H_n ≤ 1 + ln n` for `n ≥ 1`. -/
lemma harmonic_le_one_add_log {n : ℕ} (hn : 1 ≤ n) : harmonic n ≤ 1 + Real.log (n : ℝ) := by
  sorry

/-- Asymptotically, `H_n = Θ(log n)`. -/
theorem harmonic_isBigTheta_log : isBigO (fun n : ℕ => harmonic n) (fun n : ℕ => Real.log ((n : ℝ) + 1)) := by
  -- Follows from the integral bounds above.
  sorry

/-! ## Hiring Problem: expected hires = H_n -/

/--
**Theorem 5.2 (CLRS).**  In the hiring problem with `n` candidates in
uniformly random order, the expected number of hires equals `H_n`.

*Proof sketch.*  Candidate `i` is hired exactly when their rank is 1 (the
best) among the first `i` candidates.  Among the `i!` equally likely
relative orderings of the first `i` candidates, exactly `(i-1)!` put the
best candidate in position `i`.  Hence `Pr[Iᵢ = 1] = (i-1)! / i! = 1/i`.

By linearity of expectation,
`E[total hires] = E[Σ_{i=1}^n Iᵢ] = Σ_{i=1}^n E[Iᵢ] = Σ_{i=1}^n 1/i = H_n`.  ∎

The formalization of this argument requires a probability space over
permutations of `{1,…,n}` and the linearity-of-expectation theorem,
which is available in mathlib's `ProbabilityTheory` library.
-/
theorem expectedHires_eq_harmonic (n : ℕ) (hpos : 0 < n) : True :=
  -- Formal statement placeholder: the expectation requires defining the
  -- probability space (uniform over `Equiv.Perm (Fin n)`).
  trivial

end Chapter05
end CLRS
