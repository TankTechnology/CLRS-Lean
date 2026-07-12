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
* {lit}`nᵃ = o(2ⁿ)`, {lit}`2ⁿ = o(n!)`, and {lit}`nᵃ = o(n!)`
* {lit}`n! = Ω(cⁿ)` for every base {lit}`c`
* {lit}`log n = o(n)` and {lit}`log (log n) = o(log n)`
* {lit}`log_b n = Θ(log n)` and {lit}`log_b n = o(nʳ)` for {lit}`0 < r`
* {lit}`(log n)ᵃ = o(cⁿ)` when {lit}`1 < c`
* Fibonacci growth: closed form {lit}`Fₙ = (φⁿ − ψⁿ)/√5`, {lit}`Fₙ = Θ(φⁿ)`, and the
  closest-integer bound {lit}`|φⁿ/√5 − Fₙ| < 1/2`
* the iterated logarithm {lit}`lg* n` with base values, {lit}`lg*(2ⁿ) = 1 + lg* n`,
  monotonicity, {lit}`lg* n ≤ log₂ n + 1`, and the extreme slow growth {lit}`lg* n = o(log n)`
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

/-! ## Completing the CLRS 3.2 comparison table

The lemmas below fill in the remaining adjacent comparisons of the CLRS 3.2
growth hierarchy

{lit}`1 ≺ log (log n) ≺ log n ≺ n ≺ nᵃ ≺ 2ⁿ ≺ n!`,

together with the base-change facts for {lit}`log_b`. -/

/-- Logarithms grow slower than the identity: {lit}`log n = o(n)`.  This is the
{lit}`log n ≺ n` row of the CLRS 3.2 growth hierarchy. -/
theorem isLittleO_log_id :
    isLittleO (fun n : ℕ => Real.log (n : ℝ)) (fun n : ℕ => (n : ℝ)) := by
  unfold isLittleO
  simpa [Function.comp_def, id_eq] using
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop

/-- The doubly-iterated logarithm is dominated by the logarithm:
{lit}`log (log n) = o(log n)`.  This is the {lit}`log (log n) ≺ log n` row of the
CLRS 3.2 hierarchy. -/
theorem isLittleO_loglog_log :
    isLittleO (fun n : ℕ => Real.log (Real.log (n : ℝ)))
      (fun n : ℕ => Real.log (n : ℝ)) := by
  unfold isLittleO
  have h :=
    (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).comp_tendsto
      tendsto_natCast_atTop_atTop
  simpa [Function.comp_def, id_eq] using h

/-- Any fixed polynomial is dominated by the base-2 exponential:
{lit}`nᵃ = o(2ⁿ)`.  The canonical CLRS 3.2 exponential comparison; instance of
{lit}`isLittleO_pow_const_exp` at base {lit}`c = 2`. -/
theorem isLittleO_pow_two_pow (a : ℕ) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (2 : ℝ) ^ n) :=
  isLittleO_pow_const_exp (a := a) (by norm_num : (1 : ℝ) < 2)

/-- The base-2 exponential is dominated by the factorial: {lit}`2ⁿ = o(n!)`.
Equivalently {lit}`n! = ω(2ⁿ)` (CLRS 3.2). -/
theorem isLittleO_two_pow_factorial :
    isLittleO (fun n : ℕ => (2 : ℝ) ^ n) (fun n : ℕ => (Nat.factorial n : ℝ)) :=
  isLittleO_exp_vs_factorial 2

/-- The factorial dominates every exponential in the {lit}`Ω` sense:
{lit}`n! = Ω(cⁿ)` for every base {lit}`c`.  CLRS 3.2 ({lit}`n! = ω(2ⁿ)`). -/
theorem isBigOmega_factorial_exp (c : ℝ) :
    isBigOmega (fun n : ℕ => (Nat.factorial n : ℝ)) (fun n : ℕ => c ^ n) := by
  unfold isBigOmega
  have h : (fun n : ℕ => c ^ n) =o[atTop] (fun n : ℕ => (Nat.factorial n : ℝ)) :=
    isLittleO_exp_vs_factorial c
  exact h.isBigO

/-- Every fixed polynomial is dominated by the factorial: {lit}`nᵃ = o(n!)`.
Obtained by chaining {lit}`nᵃ = o(2ⁿ)` and {lit}`2ⁿ = o(n!)`.  CLRS 3.2. -/
theorem isLittleO_pow_factorial (a : ℕ) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (Nat.factorial n : ℝ)) := by
  have h1 : (fun n : ℕ => (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (2 : ℝ) ^ n) :=
    isLittleO_pow_two_pow a
  have h2 : (fun n : ℕ => (2 : ℝ) ^ n) =o[atTop]
      (fun n : ℕ => (Nat.factorial n : ℝ)) := isLittleO_two_pow_factorial
  unfold isLittleO
  exact h1.trans_isBigO h2.isBigO

/-- Base change is a {lit}`Θ`-preserving operation: {lit}`log_b n = Θ(log n)` for
{lit}`b > 1`.  This is the companion of {lit}`isBigTheta_log_logb` with the two
functions swapped.  CLRS 3.2. -/
theorem isBigTheta_logb_log {b : ℝ} (hb : 1 < b) :
    isBigTheta (fun n : ℕ => Real.logb b (n : ℝ)) (fun n : ℕ => Real.log (n : ℝ)) :=
  isBigTheta_symm (isBigTheta_log_logb hb)

/-- The base-{lit}`b` logarithm is dominated by any positive real power:
{lit}`log_b n = o(nʳ)` for {lit}`b > 1` and {lit}`0 < r`.  CLRS 3.2
({lit}`log_b n` vs {lit}`nᶜ`). -/
theorem isLittleO_logb_rpow {b r : ℝ} (hb : 1 < b) (hr : 0 < r) :
    isLittleO (fun n : ℕ => Real.logb b (n : ℝ)) (fun n : ℕ => (n : ℝ) ^ r) := by
  have hO : (fun n : ℕ => Real.logb b (n : ℝ)) =O[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := (isBigTheta_logb_log hb).1
  have ho : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ r) :=
    isLittleO_log_rpow hr
  unfold isLittleO
  exact hO.trans_isLittleO ho

/-- Every fixed power of the logarithm is dominated by any exponential with base
{lit}`c > 1`: {lit}`(log n)ᵃ = o(cⁿ)`.  Chains {lit}`(log n)ᵃ = o(n)` and
{lit}`n = o(cⁿ)`.  CLRS 3.2 (polylogarithm vs exponential). -/
theorem isLittleO_log_pow_const_exp {a : ℕ} {c : ℝ} (hc : 1 < c) :
    isLittleO (fun n : ℕ => Real.log (n : ℝ) ^ a) (fun n : ℕ => c ^ n) := by
  have h1 : (fun n : ℕ => Real.log (n : ℝ) ^ a) =o[atTop] (fun n : ℕ => (n : ℝ)) := by
    have h := isLittleO_log_pow_rpow (a := a) (r := 1) (by norm_num)
    unfold isLittleO at h
    simpa using h
  have h2 : (fun n : ℕ => (n : ℝ)) =o[atTop] (fun n : ℕ => c ^ n) := by
    have h := isLittleO_pow_const_exp (a := 1) hc
    unfold isLittleO at h
    simpa using h
  unfold isLittleO
  exact h1.trans_isBigO h2.isBigO

/-! ## Fibonacci-number growth (CLRS §3.2)

CLRS §3.2 closes with the Fibonacci numbers and two growth facts: the golden-ratio
closed form eq (3.25) and eq (3.26), which states that {lit}`Fₙ` is the closest
integer to {lit}`φⁿ/√5`, hence {lit}`Fₙ = Θ(φⁿ)`.  Mathlib supplies Binet's formula
{name}`Real.coe_fib_eq` and the golden-ratio arithmetic; the lemmas below restate them
under the CLRS asymptotic wrappers.  Here {lit}`φ = (1+√5)/2` is {name}`Real.goldenRatio`
and {lit}`ψ = (1−√5)/2` is {name}`Real.goldenConj`. -/

private theorem sqrt5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)

private theorem two_lt_sqrt5 : (2 : ℝ) < Real.sqrt 5 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

private theorem sqrt5_le_nine_quarters : Real.sqrt 5 ≤ 9 / 4 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]

/-- The conjugate golden ratio satisfies {lit}`|ψ| ≤ 1`, hence {lit}`|ψⁿ| ≤ 1`. -/
private theorem abs_goldenConj_pow_le_one (n : ℕ) : |Real.goldenConj ^ n| ≤ 1 := by
  rw [abs_pow]
  apply pow_le_one₀ (abs_nonneg _)
  rw [abs_le]
  exact ⟨Real.neg_one_lt_goldenConj.le, by linarith [Real.goldenConj_neg]⟩

/--
**CLRS equation (3.25) — Binet's closed form.**  The {lit}`n`-th Fibonacci number
equals {lit}`(φⁿ − ψⁿ)/√5`.  This is a thin CLRS-facing restatement of Mathlib's
{name}`Real.coe_fib_eq`.
-/
theorem coe_fib_closed_form (n : ℕ) :
    (Nat.fib n : ℝ) = (Real.goldenRatio ^ n - Real.goldenConj ^ n) / Real.sqrt 5 :=
  Real.coe_fib_eq n

/--
**CLRS equation (3.26) — Fibonacci exponential growth.**  The Fibonacci numbers grow
like the golden ratio: {lit}`Fₙ = Θ(φⁿ)`.  Proof: from Binet's formula,
{lit}`√5·Fₙ = φⁿ − ψⁿ`; since {lit}`|ψ| < 1 < φ` the {lit}`ψⁿ` term is negligible, so
{lit}`Fₙ ≤ φⁿ` (upper bound) and {lit}`(1/5)·φⁿ ≤ Fₙ` for {lit}`n ≥ 2` (lower bound).
-/
theorem isBigTheta_fib_goldenRatio :
    isBigTheta (fun n : ℕ => (Nat.fib n : ℝ)) (fun n : ℕ => Real.goldenRatio ^ n) := by
  have hφ0 : ∀ n : ℕ, (0 : ℝ) ≤ Real.goldenRatio ^ n :=
    fun n => pow_nonneg Real.goldenRatio_pos.le n
  have hφ1 : ∀ n : ℕ, (1 : ℝ) ≤ Real.goldenRatio ^ n :=
    fun n => one_le_pow₀ Real.one_lt_goldenRatio.le
  have hnegψ : ∀ n : ℕ, -(Real.goldenConj ^ n) ≤ Real.goldenRatio ^ n := by
    intro n
    have h := (abs_le.mp (abs_goldenConj_pow_le_one n)).1
    linarith [hφ1 n]
  constructor
  · -- Upper bound: `Fₙ ≤ φⁿ`, so `Fₙ = O(φⁿ)`.
    rw [isBigO_iff]
    refine ⟨1, one_pos, 0, ?_⟩
    intro n _
    show |(Nat.fib n : ℝ)| ≤ 1 * |Real.goldenRatio ^ n|
    have hbound : (Nat.fib n : ℝ) ≤ Real.goldenRatio ^ n := by
      rw [Real.coe_fib_eq n, div_le_iff₀ sqrt5_pos]
      nlinarith [hnegψ n, hφ0 n, two_lt_sqrt5,
        mul_nonneg (hφ0 n) (show (0 : ℝ) ≤ Real.sqrt 5 - 2 by linarith [two_lt_sqrt5])]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.fib n : ℝ)),
        abs_of_nonneg (hφ0 n), one_mul]
    exact hbound
  · -- Lower bound: `(1/5)·φⁿ ≤ Fₙ` for `n ≥ 2`, so `Fₙ = Ω(φⁿ)`.
    rw [isBigOmega_iff]
    refine ⟨1 / 5, by norm_num, 2, ?_⟩
    intro n hn
    show (1 / 5 : ℝ) * |Real.goldenRatio ^ n| ≤ |(Nat.fib n : ℝ)|
    have hφn2 : (2 : ℝ) ≤ Real.goldenRatio ^ n := by
      have h2n : Real.goldenRatio ^ 2 ≤ Real.goldenRatio ^ n :=
        pow_le_pow_right₀ Real.one_lt_goldenRatio.le hn
      nlinarith [Real.one_lt_goldenRatio, h2n, Real.goldenRatio_sq]
    have hψle : Real.goldenConj ^ n ≤ 1 := (abs_le.mp (abs_goldenConj_pow_le_one n)).2
    have hbound : (1 / 5 : ℝ) * Real.goldenRatio ^ n ≤ (Nat.fib n : ℝ) := by
      rw [Real.coe_fib_eq n, le_div_iff₀ sqrt5_pos]
      nlinarith [hφn2, hψle, sqrt5_le_nine_quarters,
        mul_nonneg (hφ0 n)
          (show (0 : ℝ) ≤ 9 / 4 - Real.sqrt 5 by linarith [sqrt5_le_nine_quarters])]
    rw [abs_of_nonneg (hφ0 n), abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.fib n : ℝ))]
    exact hbound

/--
**CLRS equation (3.26) — closest-integer bound.**  {lit}`Fₙ` is the closest integer
to {lit}`φⁿ/√5`: {lit}`|φⁿ/√5 − Fₙ| < 1/2`.  The error is exactly {lit}`|ψⁿ|/√5 ≤ 1/√5`,
which is below {lit}`1/2` because {lit}`√5 > 2`.
-/
theorem goldenRatio_pow_div_sqrt5_sub_fib_abs_lt_half (n : ℕ) :
    |Real.goldenRatio ^ n / Real.sqrt 5 - (Nat.fib n : ℝ)| < 1 / 2 := by
  have hkey : Real.goldenRatio ^ n / Real.sqrt 5 - (Nat.fib n : ℝ)
      = Real.goldenConj ^ n / Real.sqrt 5 := by
    rw [Real.coe_fib_eq n]; ring
  rw [hkey, abs_div, abs_of_pos sqrt5_pos, div_lt_iff₀ sqrt5_pos]
  nlinarith [abs_goldenConj_pow_le_one n, two_lt_sqrt5]

/--
Exponential envelope (upper): for any base {lit}`c > φ`, {lit}`Fₙ = o(cⁿ)`.  Chains
{lit}`Fₙ = O(φⁿ)` with {lit}`φⁿ = o(cⁿ)`. -/
theorem isLittleO_fib_exp {c : ℝ} (hc : Real.goldenRatio < c) :
    isLittleO (fun n : ℕ => (Nat.fib n : ℝ)) (fun n : ℕ => c ^ n) := by
  have hO : (fun n : ℕ => (Nat.fib n : ℝ)) =O[atTop] (fun n : ℕ => Real.goldenRatio ^ n) :=
    isBigTheta_fib_goldenRatio.1
  have ho : (fun n : ℕ => Real.goldenRatio ^ n) =o[atTop] (fun n : ℕ => c ^ n) :=
    isLittleO_exp_exp_of_lt Real.goldenRatio_pos.le hc
  unfold isLittleO
  exact hO.trans_isLittleO ho

/--
Exponential envelope (lower): for any base {lit}`0 ≤ c < φ`, {lit}`cⁿ = o(Fₙ)`.  Chains
{lit}`cⁿ = o(φⁿ)` with {lit}`φⁿ = O(Fₙ)`. -/
theorem isLittleO_exp_fib {c : ℝ} (hc0 : 0 ≤ c) (hc : c < Real.goldenRatio) :
    isLittleO (fun n : ℕ => c ^ n) (fun n : ℕ => (Nat.fib n : ℝ)) := by
  have hΩ : (fun n : ℕ => Real.goldenRatio ^ n) =O[atTop] (fun n : ℕ => (Nat.fib n : ℝ)) :=
    isBigTheta_fib_goldenRatio.2
  have ho : (fun n : ℕ => c ^ n) =o[atTop] (fun n : ℕ => Real.goldenRatio ^ n) :=
    isLittleO_exp_exp_of_lt hc0 hc
  unfold isLittleO
  exact ho.trans_isBigO hΩ

/-! ## Iterated logarithm {lit}`lg*` (CLRS §3.2)

CLRS §3.2 defines the iterated logarithm
{lit}`lg* n = min { i ≥ 0 : lg⁽ⁱ⁾ n ≤ 1 }`, the number of times {lit}`lg` must be
applied before the result drops to {lit}`≤ 1`, and stresses how extraordinarily
slowly it grows.  Mathlib has no iterated logarithm (only {name}`Nat.log`/{name}`Nat.clog`), so
we define {lit}`lgStar` by well-founded recursion on {lit}`ℕ`, base {lit}`2`, then
prove the recurrence, monotonicity, and the {lit}`o(log n)` slow-growth bound. -/

/--
The base-{lit}`2` iterated logarithm {lit}`lg* n` (CLRS §3.2 definition): the number
of times base-{lit}`2` {name}`Nat.log` must be applied to {lit}`n` before reaching
{lit}`≤ 1`.  Defined by well-founded recursion; the recursive argument
{lit}`Nat.log 2 n` is strictly smaller than {lit}`n` for {lit}`n ≥ 2`.
-/
def lgStar (n : ℕ) : ℕ :=
  if h : n ≤ 1 then 0 else 1 + lgStar (Nat.log 2 n)
termination_by n
decreasing_by exact Nat.log_lt_self 2 (by omega)

/-- Base case: {lit}`lg* n = 0` for {lit}`n ≤ 1`. -/
theorem lgStar_of_le_one {n : ℕ} (h : n ≤ 1) : lgStar n = 0 := by
  conv_lhs => rw [lgStar]
  rw [dif_pos h]

/-- One-step recurrence: {lit}`lg* n = 1 + lg* (log₂ n)` for {lit}`n ≥ 2`. -/
theorem lgStar_of_two_le {n : ℕ} (h : 2 ≤ n) : lgStar n = 1 + lgStar (Nat.log 2 n) := by
  conv_lhs => rw [lgStar]
  rw [dif_neg (by omega : ¬ n ≤ 1)]

/-- {lit}`lg* 0 = 0`. -/
theorem lgStar_zero : lgStar 0 = 0 := lgStar_of_le_one (by norm_num)

/-- {lit}`lg* 1 = 0`. -/
theorem lgStar_one : lgStar 1 = 0 := lgStar_of_le_one (le_refl 1)

/-- {lit}`lg* 2 = 1`. -/
theorem lgStar_two : lgStar 2 = 1 := by
  have hl : Nat.log 2 2 = 1 := by decide
  rw [lgStar_of_two_le (le_refl 2), hl, lgStar_of_le_one (le_refl 1)]

/--
**Tower recurrence** (CLRS §3.2).  For {lit}`n ≥ 1`, {lit}`lg* (2ⁿ) = 1 + lg* n`: each
extra power-of-two "tower level" adds exactly one to the iterated logarithm.
-/
theorem lgStar_two_pow {n : ℕ} (hn : 1 ≤ n) : lgStar (2 ^ n) = 1 + lgStar n := by
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  rw [lgStar_of_two_le h2, Nat.log_pow (by norm_num)]

/-- {lit}`lg*` is monotone (nondecreasing).  Proved by strong induction: for
{lit}`a ≤ b` with {lit}`b ≥ 2`, {lit}`log₂` is monotone and strictly decreasing, so the
recurrence {lit}`lg* b = 1 + lg* (log₂ b)` reduces to the smaller instance. -/
theorem lgStar_monotone : Monotone lgStar := by
  have key : ∀ b, ∀ a, a ≤ b → lgStar a ≤ lgStar b := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro a ha
      by_cases hb : b ≤ 1
      · rw [lgStar_of_le_one (le_trans ha hb), lgStar_of_le_one hb]
      · by_cases haa : a ≤ 1
        · rw [lgStar_of_le_one haa]; exact Nat.zero_le _
        · rw [lgStar_of_two_le (by omega : 2 ≤ a), lgStar_of_two_le (by omega : 2 ≤ b)]
          have hlog : Nat.log 2 a ≤ Nat.log 2 b := Nat.log_mono_right ha
          have hb_lt : Nat.log 2 b < b := Nat.log_lt_self 2 (by omega)
          exact Nat.add_le_add_left (ih (Nat.log 2 b) hb_lt (Nat.log 2 a) hlog) 1
  intro a b hab
  exact key b a hab

/-- Slow-growth bound: {lit}`lg* n ≤ log₂ n + 1` for every {lit}`n`.  Proved by strong
induction using {lit}`log₂ (log₂ n) < log₂ n`. -/
theorem lgStar_le_log_add_one : ∀ n, lgStar n ≤ Nat.log 2 n + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n ≤ 1
    · rw [lgStar_of_le_one hn]; exact Nat.zero_le _
    · rw [lgStar_of_two_le (by omega : 2 ≤ n)]
      have hlog_ge1 : 1 ≤ Nat.log 2 n := Nat.log_pos (by norm_num) (by omega)
      have hloglog_lt : Nat.log 2 (Nat.log 2 n) < Nat.log 2 n :=
        Nat.log_lt_self 2 (by omega)
      have hIH := ih (Nat.log 2 n) (Nat.log_lt_self 2 (by omega))
      omega

/-- Every base-{lit}`2` integer logarithm is bounded by twice the real logarithm:
{lit}`log₂ m ≤ 2·log m` for {lit}`m ≥ 1`.  From {lit}`2^(log₂ m) ≤ m` and
{lit}`log 2 > 1/2`. -/
theorem natLog_two_le_two_log {m : ℕ} (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) ≤ 2 * Real.log (m : ℝ) := by
  have h1 : (2 : ℕ) ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 m) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have hcast : (0 : ℝ) ≤ (Nat.log 2 m : ℝ) := by positivity
  nlinarith [h3, hcast, Real.log_two_gt_d9,
    mul_nonneg hcast (show (0 : ℝ) ≤ Real.log 2 - 0.5 by linarith [Real.log_two_gt_d9])]

/--
**Extreme slow growth** (CLRS §3.2).  The iterated logarithm is {lit}`o(log n)`:
{lit}`lg* n = o(log n)`, placing it below {lit}`log n` in the growth hierarchy.
Proof: {lit}`lg* n ≤ log₂(log₂ n) + 2 ≤ 2·log 2 + 2·log(log n) + 2` for {lit}`n ≥ 4`,
so {lit}`lg* n = O(1 + log(log n))`, and {lit}`1 + log(log n) = o(log n)` by
{name}`isLittleO_one_log` and {name}`isLittleO_loglog_log`.
-/
theorem isLittleO_lgStar_log :
    isLittleO (fun n : ℕ => (lgStar n : ℝ)) (fun n : ℕ => Real.log (n : ℝ)) := by
  have hdom : (fun n : ℕ => (1 : ℝ) + Real.log (Real.log (n : ℝ))) =o[atTop]
      (fun n : ℕ => Real.log (n : ℝ)) := by
    have hone : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) :=
      isLittleO_one_log
    have hll : (fun n : ℕ => Real.log (Real.log (n : ℝ))) =o[atTop]
        (fun n : ℕ => Real.log (n : ℝ)) := isLittleO_loglog_log
    exact hone.add hll
  have hO : (fun n : ℕ => (lgStar n : ℝ)) =O[atTop]
      (fun n : ℕ => (1 : ℝ) + Real.log (Real.log (n : ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 * Real.log 2 + 4, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 4] with n hn
    show ‖(lgStar n : ℝ)‖ ≤
      (2 * Real.log 2 + 4) * ‖(1 : ℝ) + Real.log (Real.log (n : ℝ))‖
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hn1 : 1 ≤ n := by omega
    have hn2 : 2 ≤ n := by omega
    have hlogn_ge1 : (1 : ℝ) ≤ Real.log (n : ℝ) := by
      have h4 : Real.log 4 ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h4' : (1 : ℝ) ≤ Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        nlinarith [Real.log_two_gt_d9]
      linarith
    have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := by linarith
    have hloglogn_nonneg : (0 : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_nonneg hlogn_ge1
    have hlogn_ge2 : 2 ≤ Nat.log 2 n := by
      have hmono : Nat.log 2 4 ≤ Nat.log 2 n := Nat.log_mono_right hn
      have h44 : Nat.log 2 4 = 2 := by decide
      omega
    have hstar : lgStar n ≤ Nat.log 2 (Nat.log 2 n) + 2 := by
      rw [lgStar_of_two_le hn2]
      have := lgStar_le_log_add_one (Nat.log 2 n)
      omega
    have hstarR : (lgStar n : ℝ) ≤ (Nat.log 2 (Nat.log 2 n) : ℝ) + 2 := by
      exact_mod_cast hstar
    have hb1 : (Nat.log 2 (Nat.log 2 n) : ℝ) ≤ 2 * Real.log (Nat.log 2 n : ℝ) :=
      natLog_two_le_two_log (by omega)
    have hb2 : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := natLog_two_le_two_log hn1
    have hlogln_pos : (0 : ℝ) < (Nat.log 2 n : ℝ) := by
      have : 0 < Nat.log 2 n := by omega
      exact_mod_cast this
    have hb3 : Real.log (Nat.log 2 n : ℝ) ≤ Real.log (2 * Real.log (n : ℝ)) :=
      Real.log_le_log hlogln_pos hb2
    have hb4 : Real.log (2 * Real.log (n : ℝ)) = Real.log 2 + Real.log (Real.log (n : ℝ)) :=
      Real.log_mul (by norm_num) (by positivity)
    have hcombine : (lgStar n : ℝ) ≤
        2 * Real.log 2 + 2 * Real.log (Real.log (n : ℝ)) + 2 := by
      calc (lgStar n : ℝ) ≤ (Nat.log 2 (Nat.log 2 n) : ℝ) + 2 := hstarR
        _ ≤ 2 * Real.log (Nat.log 2 n : ℝ) + 2 := by linarith [hb1]
        _ ≤ 2 * Real.log (2 * Real.log (n : ℝ)) + 2 := by linarith [hb3]
        _ = 2 * (Real.log 2 + Real.log (Real.log (n : ℝ))) + 2 := by rw [hb4]
        _ = 2 * Real.log 2 + 2 * Real.log (Real.log (n : ℝ)) + 2 := by ring
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (lgStar n : ℝ)),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + Real.log (Real.log (n : ℝ)))]
    nlinarith [hcombine, hloglogn_nonneg, hlog2pos,
      mul_nonneg (le_of_lt hlog2pos) hloglogn_nonneg]
  unfold isLittleO
  exact hO.trans_isLittleO hdom

end Chapter03
end CLRS
