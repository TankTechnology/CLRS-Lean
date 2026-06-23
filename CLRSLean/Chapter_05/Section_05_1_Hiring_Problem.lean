import Mathlib

open Finset
open Filter
open Asymptotics

/-!
# 5.1. The Hiring Problem

We prove that the expected number of hires when interviewing `n` candidates
in uniformly random order equals the n-th harmonic number `H_n = Σ_{i=1}^n 1/i`.

## Method

Define `h(n)`, the expected hires from `n` candidates.  When we add the
`(n+1)`-st candidate in a random position among the first `n+1`, the
probability the new candidate is the best among all `n+1` and therefore hired
is `1/(n+1)` (by symmetry: in a random permutation of `n+1` distinct elements,
each position is equally likely to contain the maximum).  Hence

    h(n+1) = h(n) + 1/(n+1)

with `h(0) = 0`.  The unique solution is `h(n) = H_n`.

## Formalization

We define `h(n)` directly by the recurrence and prove `h(n) = H_n` by
induction.  The probabilistic *interpretation* of `h(n)` as expected hires
follows from the symmetry argument above (not formalized here — it requires
building a probability space over `Equiv.Perm`, available in mathlib's
`ProbabilityTheory`).
-/

namespace CLRS
namespace Chapter05

/-! ## Harmonic numbers -/

def harmonic (n : ℕ) : ℝ := ∑ i in range n, 1 / ((i : ℝ) + 1)

@[simp] lemma harmonic_zero : harmonic 0 = 0 := by simp [harmonic]
lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + 1 / ((n : ℝ) + 1) := by
  simp [harmonic, sum_range_succ, add_assoc]

lemma harmonic_pos {n : ℕ} (hn : 0 < n) : 0 < harmonic n := by
  refine Finset.sum_pos (fun i _ => div_pos (by norm_num) (by positivity)) ?_
  exact ⟨0, mem_range.2 hn, by simp⟩

/-! ## Expected number of hires -/

/-- Expected number of hires from `n` candidates, defined by the recurrence
`h(0) = 0`, `h(n+1) = h(n) + 1/(n+1)`.

**Why this recurrence.**  In a random permutation of `n+1` distinct elements,
the element at the last position is the maximum (equivalently, the interviewed
candidate is the best among the first `n+1`) with probability `1/(n+1)`, since
each of the `n+1` positions is equally likely to contain the best element.
If the last candidate is hired, she contributes 1 extra hire; the remaining
`n` candidates contribute `h(n)` expected hires.  Hence the recurrence. -/
def expectedHires : ℕ → ℝ
  | 0 => 0
  | n+1 => expectedHires n + 1 / ((n : ℝ) + 1)

/-- Expected hires equals the harmonic number: both satisfy the same recurrence. -/
theorem expectedHires_eq_harmonic (n : ℕ) : expectedHires n = harmonic n := by
  induction' n with n IH
  · rfl
  · rw [expectedHires, harmonic_succ, IH]

/-! ## Logarithm bounds for harmonic numbers -/

lemma log_one_add_x_le_x {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  have hpos : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

lemma x_div_one_add_x_le_log_one_add_x {x : ℝ} (hx : -1 < x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have hy_gt_neg_one : -1 < -x / (1 + x) := by
    have : x / (1 + x) < 1 := (div_lt_one hpos).mpr (by linarith)
    linarith
  have h_upper := log_one_add_x_le_x hy_gt_neg_one
  have h_simp : 1 + (-x / (1 + x)) = (1 : ℝ) / (1 + x) := by
    field_simp [hpos.ne']; ring
  rw [h_simp] at h_upper
  have h_log_inv : Real.log ((1 : ℝ) / (1 + x)) = -Real.log (1 + x) := by
    rw [Real.log_div (by norm_num) hpos.ne', Real.log_one, sub_zero]; ring
  rw [h_log_inv] at h_upper
  linarith

lemma telescoping_log_sum (m : ℕ) : ∑ k in range m,
    (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) = Real.log ((m : ℝ) + 1) := by
  induction' m with m IH
  · simp
  · rw [sum_range_succ, IH]
    have hlog : Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) =
        Real.log ((m : ℝ) + 2) - Real.log ((m : ℝ) + 1) := by
      rw [Real.log_div (by positivity) (by positivity)]
    rw [← hlog]
    have hdiv : ((m : ℝ) + 2) / ((m : ℝ) + 1) = 1 + 1 / ((m : ℝ) + 1) := by field_simp; ring
    rw [hdiv]
    -- log(1 + 1/(m+1)) + log(m+1) = log((1+1/(m+1))·(m+1)) = log(m+2)
    rw [← Real.log_mul (by positivity) (by positivity)]
    field_simp; ring

lemma harmonic_ge_log_succ (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ harmonic n := by
  rw [← telescoping_log_sum n]
  have h_eq : ∑ k in range n, (Real.log ((k : ℝ) + 2) - Real.log ((k : ℝ) + 1)) =
      ∑ k in range n, Real.log (1 + 1 / ((k : ℝ) + 1)) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Real.log_div (by positivity) (by positivity)]
    field_simp; ring
  rw [h_eq]
  refine Finset.sum_le_sum (fun i _ => ?_)
  apply log_one_add_x_le_x
  positivity

lemma harmonic_le_one_add_log {n : ℕ} (hn : 1 ≤ n) : harmonic n ≤ 1 + Real.log (n : ℝ) := by
  rcases n with (rfl | n)
  · exact (Nat.not_lt.mpr hn (by norm_num)).elim
  · have hsum : harmonic (Nat.succ n) = 1 + ∑ k in range n, 1 / ((k : ℝ) + 2) := by
      simp [harmonic, sum_range_succ, add_assoc]
    rw [hsum]
    have h_bound : ∀ k : ℕ, 1 / ((k : ℝ) + 2) ≤ Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
      intro k
      calc
        1 / ((k : ℝ) + 2) = (1 / ((k : ℝ) + 1)) / (1 + 1 / ((k : ℝ) + 1)) := by field_simp; ring
        _ ≤ Real.log (1 + 1 / ((k : ℝ) + 1)) :=
          x_div_one_add_x_le_log_one_add_x (by positivity)
        _ = Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by field_simp; ring
    have h_telescope : (∑ k in range n, Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1))) =
        Real.log ((Nat.succ n : ℝ)) := by
      induction' n with m IH
      · simp
      · rw [sum_range_succ, IH]
        rw [← Real.log_mul (by positivity) (by positivity)]
        field_simp; ring
    calc
      1 + ∑ k in range n, 1 / ((k : ℝ) + 2) ≤ 1 + ∑ k in range n,
          Real.log (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by gcongr
      _ = 1 + Real.log ((Nat.succ n : ℝ)) := by rw [h_telescope]

/-- `H_n = Θ(log n)`.  Upper bound by induction with C=2; lower bound via `harmonic_ge_log_succ`. -/
theorem harmonic_isBigTheta_log :
    isBigTheta (fun n : ℕ => harmonic n) (fun n : ℕ => Real.log ((n : ℝ) + 1)) := by
  have h_upper : ∀ n : ℕ, harmonic n ≤ 2 * Real.log ((n : ℝ) + 1) := by
    -- Prove by induction using the recurrence and log(1+x) ≥ x/2 for x≤1
    intro n
    induction' n with n IH
    · simp
    · rw [harmonic_succ (n+1)]
      -- harmonic(n+1) = harmonic n + 1/(n+1)
      -- ≤ 2·log(n+1) + 1/(n+1)  (by IH)
      -- ≤ 2·log(n+1) + 2·log(1 + 1/(n+1)) = 2·log((n+1)·(1+1/(n+1))) = 2·log(n+2)
      -- The middle inequality uses x/2 ≤ log(1+x) for x = 1/(n+1) ≤ 1.
      -- We proved x/(1+x) ≤ log(1+x).  For x ≤ 1: x/2 ≤ x/(1+x) ≤ log(1+x).
      let x := 1 / (((n : ℕ).succ : ℝ) + 1)
      have hx_nonneg : 0 ≤ x := by positivity
      have hx_le_one : x ≤ 1 := by
        refine (one_div_le_one_div (by positivity) (by positivity)).mpr ?_
        norm_num
      have h_log_bound : x / 2 ≤ Real.log (1 + x) := by
        -- x/2 ≤ x/(1+x) since x ≤ 1, and x/(1+x) ≤ log(1+x) by our lemma
        have h1 : x / 2 ≤ x / (1 + x) := by
          refine (div_le_div_right (by positivity)).mpr ?_
          nlinarith
        have h2 : x / (1 + x) ≤ Real.log (1 + x) :=
          x_div_one_add_x_le_log_one_add_x (by positivity : -1 < x)
        nlinarith
      have h_step : 1 / ((Nat.succ n : ℝ) + 1) ≤ 2 * Real.log (1 + x) := by
        dsimp [x]
        field_simp
        nlinarith
      calc
        harmonic (Nat.succ n) = harmonic n + 1 / ((Nat.succ n : ℝ) + 1) := by
          rw [harmonic_succ]
        _ ≤ 2 * Real.log ((Nat.succ n : ℝ) + 1) + 1 / ((Nat.succ n : ℝ) + 1) := by gcongr
        _ ≤ 2 * (Real.log ((Nat.succ n : ℝ) + 1) + Real.log (1 + x)) := by
          have : 1 / ((Nat.succ n : ℝ) + 1) ≤ 2 * Real.log (1 + x) := h_step
          nlinarith
        _ = 2 * Real.log (((Nat.succ n : ℝ) + 1) * (1 + x)) := by rw [Real.log_mul (by positivity) (by positivity)]
        _ = 2 * Real.log (((Nat.succ n : ℝ) + 1) + 1) := by
          dsimp [x]; field_simp; ring
        _ = 2 * Real.log (((Nat.succ n).succ : ℝ) + 1) := by ring

  refine ⟨?_, ?_⟩
  · -- O-bound via isBigO_of_le' with norm handling
    have h_norm : ∀ n, ‖harmonic n‖ ≤ 2 * ‖Real.log ((n : ℝ) + 1)‖ := by
      intro n
      simp [Real.norm_eq_abs, abs_of_nonneg (by
        by_cases hn : n = 0; · subst n; rfl; · exact le_of_lt (harmonic_pos (Nat.pos_of_ne_zero hn))),
        abs_of_nonneg (Real.log_nonneg (by positivity : 1 ≤ (n : ℝ) + 1)), h_upper n]
    exact isBigO_of_le' _ h_norm
  · -- Ω-bound via isBigO_of_le' with reversed roles
    have h_norm : ∀ n, ‖Real.log ((n : ℝ) + 1)‖ ≤ 2 * ‖harmonic n‖ := by
      intro n
      simp [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by positivity : 1 ≤ (n : ℝ) + 1)),
        abs_of_nonneg (by
          by_cases hn : n = 0; · subst n; rfl; · exact le_of_lt (harmonic_pos (Nat.pos_of_ne_zero hn)))]
      nlinarith [harmonic_ge_log_succ n]
    exact isBigO_of_le' _ h_norm

end Chapter05
end CLRS
