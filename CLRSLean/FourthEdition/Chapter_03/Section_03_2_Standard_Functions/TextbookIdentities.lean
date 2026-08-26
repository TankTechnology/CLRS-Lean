import CLRSLean.FourthEdition.Chapter_03.Section_03_2_Standard_Functions.Core

open Filter
open Asymptotics
open scoped Topology

/-!
# CLRS §3.2 textbook identities

This file gives stable CLRS-facing names to the elementary identities used in
the prose of §3.2.  Most proofs deliberately delegate to Mathlib; the value of
these declarations is an explicit, searchable textbook interface rather than
a second implementation of integer or real arithmetic.
-/

namespace CLRS
namespace Chapter03

/-! ## Monotonicity -/

def MonotonicallyIncreasing {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) : Prop := Monotone f

def MonotonicallyDecreasing {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) : Prop := Antitone f

def StrictlyIncreasing {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) : Prop := StrictMono f

def StrictlyDecreasing {α β : Type*} [Preorder α] [Preorder β]
    (f : α → β) : Prop := StrictAnti f

/-! ## Floors, ceilings, and remainders -/

/-- CLRS (3.1): an integer is unchanged by floor and ceiling. -/
theorem floor_ceil_int (n : ℤ) :
    ⌊(n : ℝ)⌋ = n ∧ ⌈(n : ℝ)⌉ = n :=
  ⟨Int.floor_intCast n, Int.ceil_intCast n⟩

/-- The two defining inequalities for the floor of a real number. -/
theorem clrs_floor_bounds (x : ℝ) :
    (⌊x⌋ : ℝ) ≤ x ∧ x < (⌊x⌋ : ℝ) + 1 :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

/-- The two defining inequalities for the ceiling of a real number. -/
theorem clrs_ceil_bounds (x : ℝ) :
    (⌈x⌉ : ℝ) - 1 < x ∧ x ≤ (⌈x⌉ : ℝ) := by
  constructor
  · have h := Int.ceil_lt_add_one x
    linarith
  · exact Int.le_ceil x

/-- CLRS (3.3): negating a floor gives the ceiling of the negation. -/
theorem neg_floor_eq_ceil_neg (x : ℝ) : -⌊x⌋ = ⌈-x⌉ := by
  rw [Int.ceil_neg]

/-- CLRS (3.4): negating a ceiling gives the floor of the negation. -/
theorem neg_ceil_eq_floor_neg (x : ℝ) : -⌈x⌉ = ⌊-x⌋ := by
  rw [Int.floor_neg]

/-- `⌊n/2⌋ + ⌈n/2⌉ = n`, using natural floor/ceiling division. -/
theorem floor_add_ceil_half (n : ℕ) : n / 2 + (n ⌈/⌉ 2) = n := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

/-- Nested flooring divisions combine their divisors. -/
theorem floor_nested_div (n a b : ℕ) : (n / a) / b = n / (a * b) :=
  Nat.div_div_eq_div_mul n a b

/-- Nested ceiling divisions combine their positive divisors. -/
theorem ceil_nested_div (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (n ⌈/⌉ a) ⌈/⌉ b = n ⌈/⌉ (a * b) := by
  apply le_antisymm
  · rw [ceilDiv_le_iff_le_mul hb, ceilDiv_le_iff_le_mul ha]
    have h := le_smul_ceilDiv (α := ℕ) (β := ℕ) (b := n) (Nat.mul_pos ha hb)
    simpa [nsmul_eq_mul, mul_assoc] using h
  · rw [ceilDiv_le_iff_le_mul (Nat.mul_pos ha hb)]
    have h₁ := le_smul_ceilDiv (α := ℕ) (β := ℕ) (b := n) ha
    have h₂ := le_smul_ceilDiv (α := ℕ) (β := ℕ) (b := n ⌈/⌉ a) hb
    calc
      n ≤ a * (n ⌈/⌉ a) := by simpa [nsmul_eq_mul] using h₁
      _ ≤ a * (b * ((n ⌈/⌉ a) ⌈/⌉ b)) := Nat.mul_le_mul_left a (by
        simpa [nsmul_eq_mul] using h₂)
      _ = (a * b) * ((n ⌈/⌉ a) ⌈/⌉ b) := by simp [mul_assoc]

/-- CLRS (3.6), in its original real/integer form. -/
theorem floor_nested_div_real (x : ℝ) (a b : ℕ) :
    ⌊(⌊x / a⌋ : ℝ) / b⌋ = ⌊x / (a * b)⌋ := by
  rw [Int.floor_div_natCast, Int.floor_intCast, Int.floor_div_natCast]
  have hab : (a : ℝ) * (b : ℝ) = ((a * b : ℕ) : ℝ) := by norm_num
  rw [hab]
  rw [Int.floor_div_natCast]
  exact Int.ediv_ediv_of_nonneg (Int.natCast_nonneg a)

/-- CLRS (3.5), in its original real/integer form. -/
theorem ceil_nested_div_real (x : ℝ) (a b : ℕ) :
    ⌈(⌈x / a⌉ : ℝ) / b⌉ = ⌈x / (a * b)⌉ := by
  calc
    ⌈(⌈x / a⌉ : ℝ) / b⌉ = -⌊-((⌈x / a⌉ : ℝ) / b)⌋ := by
      rw [Int.floor_neg]; simp
    _ = -⌊(⌊(-x) / a⌋ : ℝ) / b⌋ := by
      congr 2
      rw [show (-x) / (a : ℝ) = -(x / a) by ring, Int.floor_neg, Int.cast_neg]
      ring
    _ = -⌊(-x) / (a * b)⌋ := by rw [floor_nested_div_real]
    _ = ⌈x / (a * b)⌉ := by
      rw [show (-x) / ((a : ℝ) * b) = -(x / ((a : ℝ) * b)) by ring,
        Int.floor_neg]
      simp

/-- CLRS (3.7): ceiling division is at most the usual upper rounding envelope. -/
theorem ceilDiv_le_add_pred_div (a b : ℕ) (hb : 0 < b) :
    ((a ⌈/⌉ b : ℕ) : ℝ) ≤ ((a + (b - 1) : ℕ) : ℝ) / b := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  rw [show a + b - 1 = a + (b - 1) by omega]
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self (a + (b - 1)) b

/-- CLRS (3.8): ceiling division is at least the usual lower rounding envelope. -/
theorem sub_pred_div_le_ceilDiv (a b : ℕ) (hb : 0 < b) :
    ((a : ℝ) - ((b - 1 : ℕ) : ℝ)) / b ≤ ((a ⌈/⌉ b : ℕ) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  have hceil := le_smul_ceilDiv (α := ℕ) (β := ℕ) (b := a) hb
  have hceilR : (a : ℝ) ≤ b * (a ⌈/⌉ b) := by
    exact_mod_cast (by simpa [nsmul_eq_mul] using hceil)
  have hpred : (0 : ℝ) ≤ (b - 1 : ℕ) := by positivity
  linarith

/-- CLRS (3.9): floor commutes with adding an integer. -/
theorem floor_int_add (n : ℤ) (x : ℝ) : ⌊(n : ℝ) + x⌋ = n + ⌊x⌋ :=
  Int.floor_intCast_add n x

/-- CLRS (3.10): ceiling commutes with adding an integer. -/
theorem ceil_int_add (n : ℤ) (x : ℝ) : ⌈(n : ℝ) + x⌉ = n + ⌈x⌉ :=
  Int.ceil_intCast_add n x

/-- Remainder as the amount left after removing the quotient multiples. -/
theorem mod_eq_sub_mul_div (n d : ℕ) : n % d = n - d * (n / d) := by
  have h := Nat.div_add_mod n d
  omega

/-- A remainder is smaller than its positive divisor. -/
theorem mod_lt_divisor (n d : ℕ) (hd : 0 < d) : n % d < d :=
  Nat.mod_lt n hd

/-- CLRS (3.11), valid also for a negative integer dividend. -/
theorem int_mod_eq_sub_mul_floor (a : ℤ) (n : ℕ) :
    a % (n : ℤ) = a - n * ⌊(a : ℚ) / n⌋ :=
  Int.mod_nat_eq_sub_mul_floor_rat_div

/-- CLRS (3.12), including negative integer dividends. -/
theorem int_mod_bounds (a : ℤ) (n : ℕ) (hn : 0 < n) :
    0 ≤ a % (n : ℤ) ∧ a % (n : ℤ) < n :=
  ⟨Int.emod_nonneg _ (by exact_mod_cast hn.ne'), Int.emod_lt_of_pos _ (by exact_mod_cast hn)⟩

/-! ## Powers and the exponential function -/

theorem pow_zero_identity {M : Type*} [Monoid M] (a : M) : a ^ 0 = 1 :=
  pow_zero a

theorem pow_add_identity {M : Type*} [Monoid M] (a : M) (m n : ℕ) :
    a ^ (m + n) = a ^ m * a ^ n :=
  pow_add a m n

theorem pow_mul_identity {M : Type*} [Monoid M] (a : M) (m n : ℕ) :
    (a ^ m) ^ n = a ^ (m * n) :=
  (pow_mul a m n).symm

theorem mul_pow_identity {M : Type*} [CommMonoid M] (a b : M) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n :=
  mul_pow a b n

theorem rpow_zero_identity (a : ℝ) : a ^ (0 : ℝ) = 1 := Real.rpow_zero a

theorem rpow_one_identity (a : ℝ) : a ^ (1 : ℝ) = a := Real.rpow_one a

theorem rpow_neg_one_identity (a : ℝ) : a ^ (-1 : ℝ) = a⁻¹ := Real.rpow_neg_one a

theorem rpow_mul_identity {a : ℝ} (ha : 0 ≤ a) (m n : ℝ) :
    (a ^ m) ^ n = a ^ (m * n) :=
  (Real.rpow_mul ha m n).symm

theorem rpow_swap_identity {a : ℝ} (ha : 0 ≤ a) (m n : ℝ) :
    (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [rpow_mul_identity ha, rpow_mul_identity ha, mul_comm]

theorem rpow_add_identity {a : ℝ} (ha : 0 < a) (m n : ℝ) :
    a ^ m * a ^ n = a ^ (m + n) :=
  (Real.rpow_add ha m n).symm

/-- CLRS equation `1 + x ≤ eˣ`. -/
theorem one_add_le_exp (x : ℝ) : 1 + x ≤ Real.exp x := by
  simpa [add_comm] using Real.add_one_le_exp x

/-- The power-series expansion of the real exponential. -/
theorem exp_series (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := by
  rw [Real.exp_eq_exp_ℝ]
  simpa using NormedSpace.expSeries_div_hasSum_exp x

/-- CLRS's limit `(1 + 1/n)ⁿ → e`. -/
theorem tendsto_one_add_inv_pow :
    Tendsto (fun n : ℕ => (1 + (1 : ℝ) / n) ^ n) atTop (𝓝 (Real.exp 1)) := by
  simpa using Real.tendsto_one_add_div_pow_exp 1

/-- CLRS (3.15): `exp x = 1 + x + Θ(x²)` as `x → 0`. -/
theorem exp_sub_one_sub_id_isTheta_sq :
    (fun x : ℝ => Real.exp x - 1 - x) =Θ[𝓝 0] (fun x => x ^ 2) := by
  have ho := Real.exp_sub_sum_range_succ_isLittleO_pow 2
  have ho' :
      (fun x : ℝ => Real.exp x - (1 + x + x ^ 2 / 2)) =o[𝓝 0]
        (fun x => x ^ 2) := by
    simpa [Finset.sum_range_succ] using ho
  have htheta : (fun x : ℝ => (1 / 2 : ℝ) * x ^ 2) =Θ[𝓝 0]
      (fun x => x ^ 2) :=
    IsTheta.const_mul_left (by norm_num) (isTheta_refl _ _)
  have h := htheta.add_isLittleO ho'
  have heq :
      (fun x : ℝ => (1 / 2 : ℝ) * x ^ 2) +
          (fun x => Real.exp x - (1 + x + x ^ 2 / 2)) =
        (fun x => Real.exp x - 1 - x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [heq] at h
  exact h

/-! ## Logarithms -/

noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x

noncomputable def ln (x : ℝ) : ℝ := Real.log x

noncomputable def lgPow (k : ℝ) (x : ℝ) : ℝ := lg x ^ k

noncomputable def lgIterate (i : ℕ) (x : ℝ) : ℝ := lg^[i] x

theorem log_mul_identity {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) = Real.log x + Real.log y :=
  Real.log_mul hx hy

theorem log_div_identity {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x / y) = Real.log x - Real.log y :=
  Real.log_div hx hy

theorem log_pow_identity (x : ℝ) (n : ℕ) :
    Real.log (x ^ n) = n * Real.log x :=
  Real.log_pow x n

/-- CLRS (3.17). -/
theorem rpow_logb_identity {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hb1 : b ≠ 1) :
    b ^ Real.logb b a = a :=
  Real.rpow_logb hb hb1 ha

/-- CLRS (3.18). -/
theorem logb_mul_identity {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.logb c (a * b) = Real.logb c a + Real.logb c b :=
  Real.logb_mul ha hb

/-- CLRS (3.18), power form with a real exponent. -/
theorem logb_rpow_identity {a b n : ℝ} (ha : 0 < a) :
    Real.logb b (a ^ n) = n * Real.logb b a :=
  Real.logb_rpow_eq_mul_logb_of_pos ha

/-- CLRS (3.19), change of base. -/
theorem logb_change_base (a : ℝ) {b c : ℝ}
    (hb : 0 < b) (hb1 : b ≠ 1) (hc : 0 < c) (hc1 : c ≠ 1) :
    Real.logb b a = Real.logb c a / Real.logb c b := by
  simp only [Real.logb]
  field_simp [Real.log_ne_zero_of_pos_of_ne_one hb hb1,
    Real.log_ne_zero_of_pos_of_ne_one hc hc1]

/-- The reciprocal identity in CLRS (3.20). -/
theorem logb_reciprocal (a b : ℝ) :
    (Real.logb a b)⁻¹ = Real.logb b a :=
  Real.inv_logb a b

/-- The inverse-argument identity in CLRS (3.20). -/
theorem logb_inv_identity (a b : ℝ) :
    Real.logb b a⁻¹ = -Real.logb b a :=
  Real.logb_inv b a

/-- CLRS (3.21). -/
theorem rpow_logb_swap {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    a ^ Real.logb b c = c ^ Real.logb b a := by
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hc]
  congr 1
  simp [Real.logb]
  ring

/-- CLRS (3.22): the power series for `log (1 + x)`. -/
theorem log_one_add_series {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ => -((-x) ^ (n + 1) / (n + 1)))
      (Real.log (1 + x)) := by
  simpa [sub_neg_eq_add] using
    (Real.hasSum_pow_div_log_of_abs_lt_one (x := -x) (by simpa using hx)).neg

/-- The upper inequality in CLRS (3.23). -/
theorem log_one_add_le {x : ℝ} (hx : -1 < x) : Real.log (1 + x) ≤ x := by
  simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)

/-- The lower inequality in CLRS (3.23). -/
theorem div_one_add_le_log_one_add {x : ℝ} (hx : -1 < x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have h := Real.log_le_sub_one_of_pos (x := (1 + x)⁻¹) (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  field_simp [hpos.ne'] at h ⊢
  linarith

/-! ## Factorials -/

theorem factorial_recurrence (n : ℕ) :
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n :=
  Nat.factorial_succ n

theorem factorial_zero : Nat.factorial 0 = 1 := Nat.factorial_zero

/-- Stirling's formula in asymptotic-equivalence form. -/
theorem stirling_formula :
    (fun n : ℕ => (Nat.factorial n : ℝ)) ~[atTop]
      (fun n : ℕ => Real.sqrt (2 * n * Real.pi) *
        (n / Real.exp 1) ^ n) :=
  Stirling.factorial_isEquivalent_stirling

/-- The global lower half of the refined Stirling bound. -/
theorem stirling_lower_bound (n : ℕ) :
    Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n ≤
      (Nat.factorial n : ℝ) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using Stirling.le_factorial_stirling n

/-- Robbins' sharp stepwise error bound underlying CLRS (3.29). -/
theorem robbins_stirling_log_error_step (n : ℕ) :
    Real.log (Stirling.stirlingSeq n) -
        Real.log (Stirling.stirlingSeq (n + 1)) ≤
      1 / (12 * n * (n + 1)) :=
  Stirling.log_stirlingSeq_sdiff_le n

/-! ## Function iteration -/

def iterateFunction {α : Type*} (f : α → α) (i : ℕ) : α → α := f^[i]

theorem iterateFunction_zero {α : Type*} (f : α → α) (x : α) :
    iterateFunction f 0 x = x := by
  simp [iterateFunction]

theorem iterateFunction_succ {α : Type*} (f : α → α) (i : ℕ) (x : α) :
    iterateFunction f (i + 1) x = f (iterateFunction f i x) := by
  simpa [iterateFunction] using Function.iterate_succ_apply' f i x

/-! ## Fibonacci numbers and the golden ratio -/

theorem fibonacci_recurrence (n : ℕ) :
    Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) :=
  Nat.fib_add_two

theorem fibonacci_zero : Nat.fib 0 = 0 := rfl

theorem fibonacci_one : Nat.fib 1 = 1 := rfl

theorem goldenRatio_definition :
    Real.goldenRatio = (1 + Real.sqrt 5) / 2 := rfl

theorem goldenConj_definition :
    Real.goldenConj = (1 - Real.sqrt 5) / 2 := rfl

/-! ## Concrete iterated-logarithm values -/

theorem lgStar_four : lgStar 4 = 2 := by
  rw [show 4 = 2 ^ 2 by norm_num, lgStar_two_pow (by norm_num), lgStar_two]

theorem lgStar_sixteen : lgStar 16 = 3 := by
  rw [show 16 = 2 ^ 4 by norm_num, lgStar_two_pow (by norm_num), lgStar_four]

theorem lgStar_65536 : lgStar 65536 = 4 := by
  rw [show 65536 = 2 ^ 16 by norm_num, lgStar_two_pow (by norm_num), lgStar_sixteen]

theorem lgStar_two_pow_65536 : lgStar (2 ^ 65536) = 5 := by
  rw [lgStar_two_pow (by norm_num), lgStar_65536]

end Chapter03
end CLRS
