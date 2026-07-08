import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Stirling

open Filter
open Asymptotics
open Real
open Stirling
open scoped Topology

/-!
# 3.2. Standard Notations and Common Functions

Concrete asymptotic comparisons for algorithm analysis.

* {lit}`nᵃ = o(nᵇ)` when {lit}`a < b`
* {lit}`nᵃ = o(cⁿ)` when {lit}`1 < c`
* {lit}`log n = o(nʳ)` when {lit}`0 < r`
* {lit}`(log n)ᵃ = o(nʳ)` when {lit}`0 < r`
* {lit}`aⁿ = o(bⁿ)` when {lit}`0 ≤ a < b`
* the harmonic numbers satisfy {lit}`Hₙ ~ log n` and {lit}`Hₙ = Θ(log n)`
* {lit}`⌊n⌋ = Θ(n)` and {lit}`⌈n⌉ = Θ(n)` on ℕ
* {lit}`⌊n/2⌋ = Θ(n)` and {lit}`⌈n/2⌉ = Θ(n)` on ℕ
* lower and upper factorial bounds
* {lit}`aⁿ = o(n!)` and {lit}`n! = o(nⁿ)`
-/

namespace CLRS
namespace Chapter03

/-! ## Polynomial comparisons -/

/-- {lit}`nᵃ = o(nᵇ)` when {lit}`a < b`. -/
theorem isLittleO_pow_pow {a b : ℕ} (h : a < b) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  unfold isLittleO
  have h_ℝ : (fun x : ℝ => x ^ a) =o[atTop] (fun x : ℝ => x ^ b) :=
    Asymptotics.isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) h
  exact (h_ℝ.comp_tendsto tendsto_natCast_atTop_atTop).congr
    (by simp) (by simp)

/-- {lit}`nᵃ = O(nᵇ)` when {lit}`a ≤ b`. -/
theorem isBigO_pow_pow {a b : ℕ} (h : a ≤ b) :
    isBigO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  rcases Nat.eq_or_lt_of_le h with (rfl | hlt)
  · exact isBigO_refl _
  · exact (isLittleO_pow_pow hlt).isBigO

/-! ## Polynomial, logarithmic, and exponential comparisons -/

/-- For any natural exponent {lit}`a` and real base {lit}`c > 1`, {lit}`nᵃ = o(cⁿ)`. -/
theorem isLittleO_pow_const_exp {a : ℕ} {c : ℝ} (hc : 1 < c) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => c ^ n) := by
  unfold isLittleO
  exact isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) a hc

/-- For every positive real exponent {lit}`r`, {lit}`log n = o(nʳ)`. -/
theorem isLittleO_log_rpow {r : ℝ} (hr : 0 < r) :
    isLittleO (fun n : ℕ => Real.log (n : ℝ)) (fun n : ℕ => (n : ℝ) ^ r) := by
  unfold isLittleO
  exact (isLittleO_log_rpow_atTop hr).comp_tendsto tendsto_natCast_atTop_atTop

/-- For every fixed natural exponent {lit}`a` and positive real exponent {lit}`r`,
{lit}`(log n)ᵃ = o(nʳ)`. -/
theorem isLittleO_log_pow_rpow {a : ℕ} {r : ℝ} (hr : 0 < r) :
    isLittleO (fun n : ℕ => Real.log (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ r) := by
  unfold isLittleO
  have hreal :
      (fun x : ℝ => Real.log x ^ (a : ℝ)) =o[atTop] (fun x : ℝ => x ^ r) :=
    isLittleO_log_rpow_rpow_atTop (a : ℝ) hr
  simpa [Function.comp_def, Real.rpow_natCast] using
    hreal.comp_tendsto tendsto_natCast_atTop_atTop

/-- Weak {lit}`O` form of {lit}`isLittleO_log_pow_rpow`. -/
theorem isBigO_log_pow_rpow {a : ℕ} {r : ℝ} (hr : 0 < r) :
    isBigO (fun n : ℕ => Real.log (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ r) :=
  (isLittleO_log_pow_rpow (a := a) hr).isBigO

/-- If {lit}`0 ≤ a < b`, then {lit}`aⁿ = o(bⁿ)`. -/
theorem isLittleO_exp_exp_of_lt {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => b ^ n) := by
  unfold isLittleO
  exact isLittleO_pow_pow_of_lt_left ha hab

/-! ## Harmonic numbers -/

/-- The harmonic numbers are asymptotic to {lit}`log n`. -/
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

/-- The harmonic numbers have logarithmic growth, {lit}`Hₙ = Θ(log n)`. -/
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

private theorem self_le_four_mul_div_two_nat {n : ℕ} (hn : 2 ≤ n) :
    n ≤ 4 * (n / 2) := by
  have hpos : 0 < n / 2 := Nat.div_pos hn (by decide)
  have hmod_lt : n % 2 < 2 := Nat.mod_lt n (by decide)
  have hdecomp : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
  omega

private theorem ceil_half_le_self_nat {n : ℕ} (hn : 1 ≤ n) :
    (n + 1) / 2 ≤ n := by
  omega

private theorem self_le_two_mul_ceil_half_nat (n : ℕ) :
    n ≤ 2 * ((n + 1) / 2) := by
  have hmod_lt : (n + 1) % 2 < 2 := Nat.mod_lt (n + 1) (by decide)
  have hdecomp : 2 * ((n + 1) / 2) + (n + 1) % 2 = n + 1 :=
    Nat.div_add_mod (n + 1) 2
  omega

/-- Natural-number floor half-scale: {lit}`⌊n/2⌋ = Θ(n)`. -/
theorem isBigTheta_nat_floor_half_coerce :
    isBigTheta (fun n : ℕ => ((n / 2 : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  constructor
  · rw [isBigO_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n _hn
    have hnat : n / 2 ≤ n := Nat.div_le_self n 2
    have hreal : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    simpa using hreal
  · change isBigO (fun n : ℕ => (n : ℝ)) (fun n : ℕ => ((n / 2 : ℕ) : ℝ))
    rw [isBigO_iff]
    refine ⟨4, by norm_num, 2, ?_⟩
    intro n hn
    have hnat : n ≤ 4 * (n / 2) := self_le_four_mul_div_two_nat hn
    have hreal : (n : ℝ) ≤ 4 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa using hreal

/-- Natural-number ceiling half-scale, represented as {lit}`(n+1)/2`: {lit}`⌈n/2⌉ = Θ(n)`. -/
theorem isBigTheta_nat_ceil_half_coerce :
    isBigTheta (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  constructor
  · rw [isBigO_iff]
    refine ⟨1, by norm_num, 1, ?_⟩
    intro n hn
    have hnat : (n + 1) / 2 ≤ n := ceil_half_le_self_nat hn
    have hreal : (((n + 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    simpa using hreal
  · change isBigO (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (((n + 1) / 2 : ℕ) : ℝ))
    rw [isBigO_iff]
    refine ⟨2, by norm_num, 0, ?_⟩
    intro n _hn
    have hnat : n ≤ 2 * ((n + 1) / 2) := self_le_two_mul_ceil_half_nat n
    have hreal : (n : ℝ) ≤ 2 * ((((n + 1) / 2 : ℕ) : ℝ)) := by exact_mod_cast hnat
    simpa using hreal

/-! ## Factorial bound -/

/-- {lit}`n! ≤ nⁿ` for all {lit}`n`.  Proof on {lit}`ℕ`: each factor 1..n ≤ n. -/
theorem factorial_upper_bound_nat (n : ℕ) : Nat.factorial n ≤ n ^ n := by
  exact Nat.factorial_le_pow n

/-- {lit}`n! ≤ nⁿ` for all {lit}`n`, real version. -/
theorem factorial_upper_bound (n : ℕ) : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast factorial_upper_bound_nat n

/--
For any offset {lit}`m`, the last {lit}`k` factors in {lit}`(m+k)!` are each at least {lit}`m+1`,
so {lit}`(m+1)^k ≤ (m+k)!`.
-/
theorem factorial_lower_bound_offset_nat (m k : ℕ) :
    (m + 1) ^ k ≤ Nat.factorial (m + k) := by
  have h := Nat.factorial_mul_pow_le_factorial (m := m) (n := k)
  have hle : (m + 1) ^ k ≤ Nat.factorial m * (m + 1) ^ k :=
    Nat.le_mul_of_pos_left ((m + 1) ^ k) (Nat.factorial_pos m)
  exact le_trans hle h

/-- Real-valued version of {lit}`factorial_lower_bound_offset_nat`. -/
theorem factorial_lower_bound_offset (m k : ℕ) :
    ((m + 1 : ℕ) : ℝ) ^ k ≤ (Nat.factorial (m + k) : ℝ) := by
  exact_mod_cast factorial_lower_bound_offset_nat m k

/--
A CLRS-style half-scale lower bound: the upper half of the factors in {lit}`n!`
contributes at least {lit}`(⌊n/2⌋+1)^(n-⌊n/2⌋)`.
-/
theorem factorial_lower_bound_half_pow_nat (n : ℕ) :
    (n / 2 + 1) ^ (n - n / 2) ≤ Nat.factorial n := by
  have h := factorial_lower_bound_offset_nat (m := n / 2) (k := n - n / 2)
  have hsum : n / 2 + (n - n / 2) = n :=
    Nat.add_sub_of_le (Nat.div_le_self n 2)
  simpa [hsum] using h

/-- Real-valued version of {lit}`factorial_lower_bound_half_pow_nat`. -/
theorem factorial_lower_bound_half_pow (n : ℕ) :
    (((n / 2 + 1 : ℕ) : ℝ) ^ (n - n / 2)) ≤ (Nat.factorial n : ℝ) := by
  exact_mod_cast factorial_lower_bound_half_pow_nat n

/-! ## Exponential vs factorial -/

/-- {lit}`aⁿ = o(n!)` as {lit}`n → ∞`.  Follows from {lit}`FloorSemiring.tendsto_pow_div_factorial_atTop`,
the standard lemma that {lit}`cⁿ / n! → 0` for any real {lit}`c`. -/
theorem isLittleO_exp_vs_factorial (a : ℝ) :
    isLittleO (fun n : ℕ => a ^ n) (fun n : ℕ => (Nat.factorial n : ℝ)) := by
  -- The key lemma: a^n / n! → 0 as n → ∞ (standard result in mathlib)
  have h_tendsto : Tendsto (fun n : ℕ => a ^ n / ((Nat.factorial n : ℕ) : ℝ)) atTop (𝓝 0) := by
    -- FloorSemiring.tendsto_pow_div_factorial_atTop gives a^n / n! → 0 in ℝ
    -- where n! is the ℝ factorial via the factorial notation {lit}`n !`
    simpa using FloorSemiring.tendsto_pow_div_factorial_atTop (K := ℝ) a
  -- Use isLittleO_iff_tendsto: f =o[atTop] g  ↔  f/g → 0  (when g=0 → f=0)
  have h_cond : ∀ n : ℕ, ((Nat.factorial n : ℝ) = 0) → a ^ n = 0 := by
    intro n hn
    have hpos : 0 < (Nat.factorial n : ℝ) := by exact_mod_cast Nat.factorial_pos n
    linarith
  unfold isLittleO
  rw [isLittleO_iff_tendsto h_cond]
  exact h_tendsto

/--
CLRS standard growth-table fact: {lit}`n! = o(nⁿ)`.
-/
theorem isLittleO_factorial_pow_self :
    isLittleO (fun n : ℕ => (Nat.factorial n : ℝ)) (fun n : ℕ => (n : ℝ) ^ n) := by
  have h_tendsto :
      Tendsto (fun n : ℕ => (Nat.factorial n : ℝ) / ((n : ℝ) ^ n)) atTop (𝓝 0) := by
    simpa using tendsto_factorial_div_pow_self_atTop
  have h_cond : ∀ n : ℕ, ((n : ℝ) ^ n = 0) → (Nat.factorial n : ℝ) = 0 := by
    intro n hn
    exfalso
    have hpow_pos : 0 < (n : ℝ) ^ n := by
      cases n with
      | zero => norm_num
      | succ k => positivity
    exact (ne_of_gt hpow_pos) hn
  unfold isLittleO
  rw [isLittleO_iff_tendsto h_cond]
  exact h_tendsto

/-! ## Log-factorial asymptotics (Stirling) -/

/--
**Theorem (log-factorial is Θ(n log n)).**  {lit}`log(n!) = Θ(n log n)`.
CLRS equation (3.19).  Upper bound: {lit}`n! ≤ n^n`.  Lower bound: Mathlib's
Stirling approximation {lit}`le_log_factorial_stirling`.
-/
theorem isBigTheta_log_factorial :
    isBigTheta (fun n : ℕ => Real.log (Nat.factorial n : ℝ))
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  constructor
  · rw [isBigO_iff]
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n _
    by_cases hn : n = 0
    · subst n; simp
    · have h_fact_le : (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ n := by
        exact_mod_cast factorial_upper_bound_nat n
      have h_log : Real.log (Nat.factorial n : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h_fact_le
      rw [Real.log_pow] at h_log
      have h_nonneg : 0 ≤ Real.log (Nat.factorial n : ℝ) :=
        Real.log_nonneg (by exact_mod_cast Nat.factorial_pos n)
      calc
        |Real.log (Nat.factorial n : ℝ)| = Real.log (Nat.factorial n : ℝ) := abs_of_nonneg h_nonneg
        _ ≤ (n : ℝ) * Real.log (n : ℝ) := h_log
        _ = 1 * |(n : ℝ) * Real.log (n : ℝ)| := by
          have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
          have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (Nat.one_le_of_lt (Nat.pos_of_ne_zero hn)))
          rw [abs_mul, abs_of_nonneg hn_nonneg, abs_of_nonneg hlog_nonneg]; ring
  · rw [isBigOmega_iff]
    refine ⟨1/2, by norm_num, 8, ?_⟩
    intro n hn8
    have hn0 : n ≠ 0 := by omega
    have hstirling := le_log_factorial_stirling hn0
    have h_log_n_ge_two : (2 : ℝ) ≤ Real.log (n : ℝ) := by
      have h_exp2_lt_8 : Real.exp (2 : ℝ) < 8 := by
        calc
          Real.exp (2 : ℝ) = Real.exp ((1 : ℝ) + (1 : ℝ)) := by norm_num
          _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
          _ < 2.7182818286 * 2.7182818286 := by
            nlinarith [Real.exp_one_lt_d9, Real.exp_one_gt_d9]
          _ < 8 := by norm_num
      have h_log_exp2_lt_log8 : Real.log (Real.exp (2 : ℝ)) < Real.log (8 : ℝ) :=
        Real.log_lt_log (Real.exp_pos _) h_exp2_lt_8
      rw [Real.log_exp (2 : ℝ)] at h_log_exp2_lt_log8
      have hlog8le : Real.log (8 : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn8)
      linarith
    have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have h_log_nonneg : 0 ≤ Real.log (n : ℝ) := by linarith
    have h_fact_ge_one : 1 ≤ (Nat.factorial n : ℝ) := by
      have h : 1 ≤ Nat.factorial n := Nat.succ_le_of_lt (Nat.factorial_pos n)
      exact_mod_cast h
    calc
      |Real.log (Nat.factorial n : ℝ)| = Real.log (Nat.factorial n : ℝ) :=
        abs_of_nonneg (Real.log_nonneg h_fact_ge_one)
      _ ≥ (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (n : ℝ) / 2 +
          Real.log (2 * Real.pi) / 2 := hstirling
      _ ≥ (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) := by
        have h_rem_nonneg : 0 ≤ Real.log (n : ℝ) / 2 + Real.log (2 * Real.pi) / 2 := by
          have h1 : 0 ≤ Real.log (n : ℝ) / 2 := div_nonneg (by linarith) (by norm_num)
          have h2 : 0 ≤ Real.log (2 * Real.pi) / 2 := by
            have h2pi_ge_one : 1 ≤ 2 * Real.pi := by
              have hpi_gt_one : (1 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
              nlinarith
            exact div_nonneg (Real.log_nonneg h2pi_ge_one) (by norm_num)
          linarith
        linarith
      _ ≥ ((n : ℝ) * Real.log (n : ℝ)) / 2 := by
        have : (n : ℝ) ≤ ((n : ℝ) * Real.log (n : ℝ)) / 2 := by nlinarith
        linarith
      _ = (1/2 : ℝ) * |(n : ℝ) * Real.log (n : ℝ)| := by
        rw [abs_mul, abs_of_nonneg hn_nonneg, abs_of_nonneg h_log_nonneg]; ring

/-! ## Logarithm base change -/

/--
Changing the base of a logarithm only changes its value by a constant factor.
For any base {lit}`b > 1`, {lit}`log n = Θ(log_b n)`.
-/
theorem isBigTheta_log_logb {b : ℝ} (hb : 1 < b) :
    isBigTheta (fun n : ℕ => Real.log (n : ℝ))
      (fun n : ℕ => Real.logb b (n : ℝ)) := by
  have hlogb_pos : 0 < Real.log b := Real.log_pos hb
  have hlogb_ne_zero : Real.log b ≠ 0 := by linarith
  constructor
  · rw [isBigO_iff]
    refine ⟨Real.log b, hlogb_pos, 1, ?_⟩
    intro n hn
    have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnpos
    rw [Real.logb, abs_of_nonneg hlog_nonneg,
      abs_of_nonneg (div_nonneg hlog_nonneg hlogb_pos.le)]
    have h : Real.log b * (Real.log (n : ℝ) / Real.log b) = Real.log (n : ℝ) := by
      field_simp [hlogb_ne_zero]
    rw [h]
  · rw [isBigOmega_iff]
    refine ⟨(Real.log b) / 2, half_pos hlogb_pos, 2, ?_⟩
    intro n hn
    have hn1real : (1 : ℝ) ≤ (n : ℝ) := by exact mod_cast (show (1 : ℕ) ≤ n from by omega)
    have hnpos : (0 : ℝ) ≤ Real.log (n : ℝ) := Real.log_nonneg hn1real
    rw [Real.logb, abs_of_nonneg hnpos,
      abs_of_nonneg (div_nonneg hnpos hlogb_pos.le)]
    have h_simp : (Real.log b) / 2 * (Real.log (n : ℝ) / Real.log b) =
        Real.log (n : ℝ) / 2 := by
      field_simp [hlogb_ne_zero]
    rw [h_simp]
    linarith

/-- The logarithm grows without bound: {lit}`1 = o(log n)`. -/
theorem isLittleO_one_log :
    isLittleO (fun _ : ℕ => (1 : ℝ)) (fun n : ℕ => Real.log (n : ℝ)) := by
  unfold isLittleO
  exact (isLittleO_const_log_atTop (c := 1)).comp_tendsto tendsto_natCast_atTop_atTop

end Chapter03
end CLRS
