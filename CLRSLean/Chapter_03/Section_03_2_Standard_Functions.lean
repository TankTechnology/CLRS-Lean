import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation
import Mathlib
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Filter
open Asymptotics
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
* {lit}`log_b n = Θ(log n)` for any base {lit}`b > 1` (logarithm base independence)
* {lit}`n = o(n log n)` (linear vs linearithmic)
* {lit}`n log n = o(nʳ)` when {lit}`1 < r` (linearithmic vs superlinear)
* {lit}`nᵃ (log n)ᵇ = o(nᶜ)` when {lit}`a < c` (polylog factor)
* {lit}`nᵃ (log n)ᵇ = O(nᶜ)` when {lit}`a < c`
* {lit}`nᵇ = Ω(nᵃ)` when {lit}`a ≤ b` (polynomial lower bound)
* {lit}`1 = o(cⁿ)` when {lit}`c > 1` (constant vs exponential)
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

/-! ## Logarithm base independence -/

/-- Logarithms to different bases differ by a constant factor:
{lit}`log_b n = Θ(log n)` for any base {lit}`b > 1`.  This makes the base of a
logarithm invisible in asymptotic notation—the textbook's "logarithms are
asymptotically independent of their base." -/
theorem isBigTheta_logb_eq_log {b : ℝ} (hb : 1 < b) :
    isBigTheta (fun n : ℕ => Real.logb b (n : ℝ)) (fun n : ℕ => Real.log (n : ℝ)) := by
  have hinv_ne_zero : (Real.log b)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt (Real.log_pos hb))
  have h_eq : (fun n : ℕ => Real.logb b (n : ℝ)) =
      (fun n : ℕ => (Real.log b)⁻¹ • Real.log (n : ℝ)) := by
    ext n
    simp [Real.logb, div_eq_inv_mul]
  rw [h_eq]
  have htheta := (isTheta_const_smul_left (l := atTop) (c := (Real.log b)⁻¹) hinv_ne_zero).mpr
    (isTheta_refl (l := atTop) (fun n : ℕ => Real.log (n : ℝ)))
  rcases htheta with ⟨hO, hΩ⟩
  constructor
  · unfold isBigO; exact hO
  · unfold isBigOmega; exact hΩ

/-! ## Linear, linearithmic, and polynomial comparisons -/

/-- {lit}`n = o(n log n)`: linear functions are strictly dominated by linearithmic.
This is the formal basis for why {lit}`O(n log n)` sorting is not linear.

Proof: first show {lit}`1 = o(log n)` (since {lit}`log n → ∞`), then multiply
by {lit}`n = O(n)` using {lit}`IsBigO.mul_isLittleO`. -/
theorem isLittleO_id_log :
    isLittleO (fun n : ℕ => (n : ℝ)) (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) := by
  unfold isLittleO
  have h_one_log : (fun _ : ℕ => (1 : ℝ)) =o[atTop] (fun n : ℕ => Real.log (n : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hcpos
    let N : ℕ := max 2 (Nat.floor (Real.exp (c⁻¹)) + 1)
    refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by
        have : 2 ≤ N := Nat.le_max_left _ _
        have : 2 ≤ n := Nat.le_trans this hn
        exact_mod_cast (show 1 ≤ n from by omega))
    have hlog_large : c⁻¹ ≤ Real.log (n : ℝ) := by
      have hnexp : Real.exp (c⁻¹) ≤ (n : ℝ) := by
        have hfloorN : Real.exp (c⁻¹) ≤ (N : ℝ) := by
          have hlt : Real.exp (c⁻¹) < (Nat.floor (Real.exp (c⁻¹)) : ℝ) + 1 :=
            Nat.lt_floor_add_one (Real.exp (c⁻¹))
          have hcast : (Nat.floor (Real.exp (c⁻¹)) + 1 : ℕ) ≤ N := Nat.le_max_right _ _
          have hle' : (Nat.floor (Real.exp (c⁻¹)) : ℝ) + 1 ≤ (Nat.floor (Real.exp (c⁻¹)) + 1 : ℕ) := by simp
          have hNcast : (Nat.floor (Real.exp (c⁻¹)) + 1 : ℕ) ≤ (N : ℝ) := by exact mod_cast hcast
          linarith
        have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hlog_exp : Real.log (Real.exp (c⁻¹)) = c⁻¹ := Real.log_exp c⁻¹
      calc
        c⁻¹ = Real.log (Real.exp (c⁻¹)) := by rw [hlog_exp]
        _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos _) hnexp
    calc
      ‖(1 : ℝ)‖ = (1 : ℝ) := by simp
      _ = c * c⁻¹ := by field_simp [hcpos.ne']
      _ ≤ c * Real.log (n : ℝ) := by
        nlinarith
      _ = c * ‖Real.log (n : ℝ)‖ := by rw [Real.norm_eq_abs, abs_of_nonneg hlog_nonneg]
  have h_id : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    Asymptotics.isBigO_refl _ _
  have h_mul : (fun n : ℕ => (n : ℝ) * (1 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) :=
    h_id.mul_isLittleO h_one_log
  simpa [mul_comm] using h_mul

/-- {lit}`n log n = o(nʳ)` when {lit}`1 < r`.  Linearithmic is dominated by any
superlinear polynomial.  This is why {lit}`O(n log n)` sorts beat {lit}`O(n²)` sorts.

Proof: write {lit}`(n log n) / n^r = (log n) / n^(r-1)` and use
{lit}`log n = o(n^(r-1))` since {lit}`r-1 > 0`.  Then multiply by {lit}`n = O(n)`. -/
theorem isLittleO_mul_log_rpow {r : ℝ} (hr : 1 < r) :
    isLittleO (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) (fun n : ℕ => (n : ℝ) ^ r) := by
  unfold isLittleO
  have h_eps_pos : 0 < r - 1 := by linarith
  have h_log : (fun n : ℕ => Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (r - 1)) := by
    simpa [isLittleO] using isLittleO_log_rpow h_eps_pos
  have h_id : (fun n : ℕ => (n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ)) :=
    Asymptotics.isBigO_refl _ _
  -- BigO * LittleO = LittleO
  have h_mul : (fun n : ℕ => (n : ℝ) * Real.log (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) * ((n : ℝ) ^ (r - 1))) :=
    h_id.mul_isLittleO h_log
  -- (n) * (n^(r-1)) = n^(1 + (r-1)) = n^r
  have h_pow_eq : (fun n : ℕ => (n : ℝ) * ((n : ℝ) ^ (r - 1))) = (fun n : ℕ => (n : ℝ) ^ r) := by
    ext n
    by_cases hn : (n : ℝ) = 0
    · have hrpos : 0 < r := by linarith
      simp [hn, Real.zero_rpow (by linarith : r ≠ 0)]
    · have hpos : 0 < (n : ℝ) := by
        by_cases hn0 : n = 0
        · exfalso; apply hn; simpa [hn0] using rfl
        · have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn0
          exact Nat.cast_pos.mpr hn_pos_nat
      calc
        (n : ℝ) * ((n : ℝ) ^ (r - 1)) = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ (r - 1)) := by simp
        _ = (n : ℝ) ^ ((1 : ℝ) + (r - 1)) := by rw [Real.rpow_add hpos]
        _ = (n : ℝ) ^ r := by
          have : (1 : ℝ) + (r - 1) = r := by ring
          rw [this]
  simpa [h_pow_eq] using h_mul

/-! ## Polylog factors with polynomials -/

/-- For any exponents {lit}`a < c`, {lit}`nᵃ (log n)ᵇ = o(nᶜ)`.
A polylog factor does not change the asymptotic polynomial order—the textbook's
"any positive polynomial dominates any polylog."

Proof: factor {lit}`nᵃ (log n)ᵇ / nᶜ = (log n)ᵇ / n^(c-a)` using
{lit}`pow_add`, then apply {lit}`(log n)ᵇ = o(n^(c-a))` since {lit}`c-a > 0`. -/
theorem isLittleO_pow_log_pow_rpow {a b c : ℕ} (hac : a < c) :
    isLittleO (fun n : ℕ => (n : ℝ) ^ a * Real.log (n : ℝ) ^ b)
      (fun n : ℕ => (n : ℝ) ^ c) := by
  unfold isLittleO
  have h_poly : (fun n : ℕ => (n : ℝ) ^ a) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a) :=
    Asymptotics.isBigO_refl _ _
  have h_sub_pos : 0 < ((c - a : ℕ) : ℝ) := by
    have : 0 < c - a := Nat.sub_pos_of_lt hac
    exact_mod_cast this
  have h_log : (fun n : ℕ => Real.log (n : ℝ) ^ b) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ (c - a)) := by
    -- Use isLittleO_log_pow_rpow with r := (c-a : ℝ)
    have h := isLittleO_log_pow_rpow (a := b) (r := ((c - a : ℕ) : ℝ)) h_sub_pos
    unfold isLittleO at h
    -- (n:ℝ)^(c-a) with Nat exponent is the same as (n:ℝ)^((c-a):ℝ)
    simpa using h
  have h_mul : (fun n : ℕ => (n : ℝ) ^ a * Real.log (n : ℝ) ^ b) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ (c - a)) :=
    h_poly.mul_isLittleO h_log
  -- Rewrite using pow_add: (n:ℝ)^a * (n:ℝ)^(c-a) = (n:ℝ)^c
  have h_pow_eq : (fun n : ℕ => (n : ℝ) ^ a * (n : ℝ) ^ (c - a)) =
      (fun n : ℕ => (n : ℝ) ^ c) := by
    ext n
    have hsum : a + (c - a) = c := Nat.add_sub_cancel' (Nat.le_of_lt hac)
    calc
      (n : ℝ) ^ a * (n : ℝ) ^ (c - a) = (n : ℝ) ^ (a + (c - a)) := by rw [pow_add]
      _ = (n : ℝ) ^ c := by rw [hsum]
  simpa [h_pow_eq] using h_mul

/-- Big-O version: when {lit}`a < c`, the polylog factor does not prevent an
{lit}`O(nᶜ)` bound.  Follows directly from the {lit}`o` version. -/
theorem isBigO_pow_log_pow_rpow {a b c : ℕ} (hac : a < c) :
    isBigO (fun n : ℕ => (n : ℝ) ^ a * Real.log (n : ℝ) ^ b)
      (fun n : ℕ => (n : ℝ) ^ c) :=
  (isLittleO_pow_log_pow_rpow hac).isBigO

/-! ## Omega (lower-bound) versions -/

/-- {lit}`nᵇ = Ω(nᵃ)` when {lit}`a ≤ b`.  Polynomial lower bound; the Ω companion
to {lit}`isBigO_pow_pow`. -/
theorem isBigOmega_pow_pow {a b : ℕ} (h : a ≤ b) :
    isBigOmega (fun n : ℕ => (n : ℝ) ^ b) (fun n : ℕ => (n : ℝ) ^ a) := by
  unfold isBigOmega
  -- isBigOmega f g = g =O[l] f, so need (n^a) =O (n^b)
  have hO : isBigO (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) :=
    isBigO_pow_pow h
  unfold isBigO at hO
  exact hO

/-! ## Constant vs exponential -/

/-- {lit}`1 = o(cⁿ)` when {lit}`c > 1`.  Constants are asymptotically negligible
compared to any growing exponential.  This is the {lit}`k = 0` case of
{lit}`isLittleO_pow_const_exp`. -/
theorem isLittleO_const_exp {c : ℝ} (hc : 1 < c) :
    isLittleO (fun _ : ℕ => (1 : ℝ)) (fun n : ℕ => c ^ n) := by
  have := isLittleO_pow_const_exp (a := 0) hc
  simpa [pow_zero] using this

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

end Chapter03
end CLRS
