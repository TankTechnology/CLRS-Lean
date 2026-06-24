import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Filter
open Asymptotics
open scoped Topology

/-!
# 3.2. Standard Notations and Common Functions

Concrete asymptotic comparisons for algorithm analysis.

* `nᵃ = o(nᵇ)` when `a < b`
* `nᵃ = o(cⁿ)` when `1 < c`
* `log n = o(nʳ)` when `0 < r`
* `aⁿ = o(bⁿ)` when `0 ≤ a < b`
* the harmonic numbers satisfy `Hₙ ~ log n` and `Hₙ = Θ(log n)`
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

/-! ## Polynomial, logarithmic, and exponential comparisons -/

/-- For any natural exponent `a` and real base `c > 1`, `nᵃ = o(cⁿ)`. -/
theorem isLittleO_pow_const_exp {a : ℕ} {c : ℝ} (hc : 1 < c) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => c ^ n) := by
  unfold isLittleO
  exact isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) a hc

/-- For every positive real exponent `r`, `log n = o(nʳ)`. -/
theorem isLittleO_log_rpow {r : ℝ} (hr : 0 < r) :
    isLittleO (fun n : ℕ => Real.log (n : ℝ)) (fun n : ℕ => (n : ℝ) ^ r) := by
  unfold isLittleO
  exact (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop

/-- If `0 ≤ a < b`, then `aⁿ = o(bⁿ)`. -/
theorem isLittleO_exp_exp_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => b ^ n) := by
  unfold isLittleO
  exact isLittleO_pow_pow_of_lt_left ha hab

/-! ## Harmonic numbers -/

/-- The harmonic numbers are asymptotic to `log n`. -/
theorem isEquivalent_harmonic_log :
    (fun n : ℕ => (harmonic n : ℝ)) ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
  have hdiffO :
      (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ)) =O[atTop]
        (fun _ : ℕ => (1 : ℝ)) := by
    exact Filter.Tendsto.isBigO_one (F := ℝ) Real.tendsto_harmonic_sub_log
  have hconst :
      (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
    exact Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  exact hdiffO.trans_isLittleO hconst

/-- The harmonic numbers have logarithmic growth, `Hₙ = Θ(log n)`. -/
theorem isBigTheta_harmonic_log :
    isBigTheta (fun n : ℕ => (harmonic n : ℝ)) (fun n : ℕ => Real.log (n : ℝ)) := by
  have htheta :
      (fun n : ℕ => (harmonic n : ℝ)) =Θ[atTop]
        (fun n : ℕ => Real.log (n : ℝ)) :=
    isEquivalent_harmonic_log.isTheta
  exact ⟨by unfold isBigO; exact htheta.1, by unfold isBigOmega; exact htheta.2⟩

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

/-- `aⁿ = o(n!)` as `n → ∞`.  Follows from `FloorSemiring.tendsto_pow_div_factorial_atTop`,
the standard lemma that `cⁿ / n! → 0` for any real `c`. -/
theorem isLittleO_exp_vs_factorial (a : ℝ) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => (Nat.factorial n : ℝ)) := by
  -- The key lemma: a^n / n! → 0 as n → ∞ (standard result in mathlib)
  have h_tendsto : Tendsto (fun n : ℕ => a ^ n / ((Nat.factorial n : ℕ) : ℝ)) atTop (𝓝 0) := by
    -- FloorSemiring.tendsto_pow_div_factorial_atTop gives a^n / n! → 0 in ℝ
    -- where n! is the ℝ factorial via the factorial notation `n !`
    simpa using FloorSemiring.tendsto_pow_div_factorial_atTop (K := ℝ) a
  -- Use isLittleO_iff_tendsto: f =o[atTop] g  ↔  f/g → 0  (when g=0 → f=0)
  have h_cond : ∀ n : ℕ, ((Nat.factorial n : ℝ) = 0) → a ^ n = 0 := by
    intro n hn
    have hpos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    linarith
  unfold isLittleO
  rw [isLittleO_iff_tendsto h_cond]
  exact h_tendsto

end Chapter03
end CLRS
