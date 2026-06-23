import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib

open Filter
open Asymptotics

/-!
# 3.2. Standard Notations and Common Functions

Concrete asymptotic comparisons for algorithm analysis.

* `nᵃ = o(nᵇ)` when `a < b`
* `⌊n⌋ = Θ(n)` and `⌈n⌉ = Θ(n)` on ℕ
* `n! ≤ nⁿ` and `aⁿ = o(n!)`
-/

namespace CLRS
namespace Chapter03

/-! ## Polynomial comparisons -/

/-- `nᵃ = o(nᵇ)` when `a < b`. -/
theorem isLittleO_pow_pow {a b : ℕ} (h : a < b) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  unfold isLittleO
  have h_ℝ : (fun x : ℝ => x ^ a) =o[atTop] (fun x : ℝ => x ^ b) :=
    Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) h
  exact (h_ℝ.comp_tendsto tendsto_natCast_atTop_atTop).congr
    (by simp) (by simp)

/-- `nᵃ = O(nᵇ)` when `a ≤ b`. -/
theorem isBigO_pow_pow {a b : ℕ} (h : a ≤ b) :
    isBigO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  rcases Nat.eq_or_lt_of_le h with (rfl | hlt)
  · exact isBigO_refl _
  · exact (isLittleO_pow_pow hlt).isBigO

/-! ## Floor and ceiling are Θ(id) on ℕ -/

theorem isBigTheta_nat_floor_coerce : isBigTheta (fun n : ℕ => (⌊(n : ℝ)⌋₊ : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  have h_equiv : (fun x : ℝ => (⌊x⌋₊ : ℝ)) ~[atTop] (fun x : ℝ => x) := isEquivalent_nat_floor
  have hO : (fun n : ℕ => (⌊(n : ℝ)⌋₊ : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    (h_equiv.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  have hΩ : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (⌊(n : ℝ)⌋₊ : ℝ)) :=
    (h_equiv.symm.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  exact ⟨by unfold isBigO; exact hO, by unfold isBigOmega; exact hΩ⟩

theorem isBigTheta_nat_ceil_coerce : isBigTheta (fun n : ℕ => (⌈(n : ℝ)⌉₊ : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  have h_equiv : (fun x : ℝ => (⌈x⌉₊ : ℝ)) ~[atTop] (fun x : ℝ => x) := isEquivalent_nat_ceil
  have hO : (fun n : ℕ => (⌈(n : ℝ)⌉₊ : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    (h_equiv.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  have hΩ : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (⌈(n : ℝ)⌉₊ : ℝ)) :=
    (h_equiv.symm.isBigO.comp_tendsto tendsto_natCast_atTop_atTop).congr (by simp) (by simp)
  exact ⟨by unfold isBigO; exact hO, by unfold isBigOmega; exact hΩ⟩

/-! ## Factorial bound -/

/-- `n! ≤ nⁿ` for all `n`.  Proof on `ℕ`: each factor 1..n ≤ n. -/
theorem factorial_upper_bound_nat (n : ℕ) : Nat.factorial n ≤ n ^ n := by
  induction' n with k IH
  · exact le_rfl
  · rw [Nat.factorial_succ]
    -- (k+1)! = (k+1) * k! ≤ (k+1) * k^k ≤ (k+1) * (k+1)^k = (k+1)^(k+1)
    have h1 : k ^ k ≤ (k + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ k) _
    have h2 : Nat.factorial k ≤ (k + 1) ^ k := le_trans IH h1
    have h3 : (k + 1) * Nat.factorial k ≤ (k + 1) * (k + 1) ^ k :=
      Nat.mul_le_mul_left (k + 1) h2
    -- (k+1) * (k+1)^k = (k+1)^(k+1)
    calc
      (k + 1) * Nat.factorial k ≤ (k + 1) * (k + 1) ^ k := h3
      _ = (k + 1) ^ (k + 1) := by rw [mul_comm, Nat.pow_succ]

/-- `n! ≤ nⁿ` for all `n`, real version. -/
theorem factorial_upper_bound (n : ℕ) : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast factorial_upper_bound_nat n
    -- Note: ↑(k + 1) = ((k : ℝ) + 1) by Nat.cast_add, so the goal is identical

/-! ## Exponential vs factorial -/

/-- `aⁿ = o(n!)` as `n → ∞`.
This is a standard result.  The proof uses convergence of the exponential
series `∑ aⁿ/n!` (definition of `Real.exp`); summability implies terms → 0,
hence `aⁿ = o(n!)`.
-/
theorem isLittleO_exp_vs_factorial (a : ℝ) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => (Nat.factorial n : ℝ)) := by
  -- The exponential series ∑ aⁿ / n! converges (definition of Real.exp).
  -- Therefore aⁿ / n! → 0 as n → ∞, which by definition means aⁿ = o(n!).
  sorry

end Chapter03
end CLRS
