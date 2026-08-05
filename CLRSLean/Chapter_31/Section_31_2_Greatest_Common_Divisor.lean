import Mathlib
import CLRSLean.Chapter_31.Section_31_1_Elementary_Number_Theory

/-!
# 31.2 Greatest Common Divisor

CLRS §31.2: the Euclid recursion, Bezout's lemma, the
smallest-positive-linear-combination characterization of the gcd, and the
EUCLID and EXTENDED-EUCLID algorithms.

Main results:

- Lemma 31.2 ({lit}`euclid_recursion`, {lit}`gcd_zero_left`,
  {lit}`gcd_zero_right`): `gcd(a, b) = gcd(b mod a, a)` and the base cases
  `gcd(0, b) = b`, `gcd(a, 0) = a`.
- {lit}`euclid` + {lit}`euclid_eq_gcd` + {lit}`euclid_terminates`: the EUCLID
  algorithm is a total function and always returns `Nat.gcd a b`.
- Lemma 31.3 ({lit}`gcd_is_linear_combination`): **Bezout's identity** —
  `gcd a b` is an integer linear combination of `a` and `b`.
- Theorem 31.2 ({lit}`gcd_is_smallest_positive_linear_combination`): `gcd a b`
  is the smallest positive linear combination of `a` and `b` (when
  `a ≠ 0 ∨ b ≠ 0`).
- Corollary 31.3 ({lit}`gcd_dvd_linear_combination`): `gcd a b` divides every
  linear combination of `a` and `b`.
- Corollary 31.4 ({lit}`gcd_eq_one_iff_coprime`,
  {lit}`coprime_iff_one_linear_combination`,
  {lit}`gcd_div_gcd_coprime`): coprime characterizations, including
  `coprime (a/g) (b/g)` for `g = gcd a b`.
- {lit}`extendedEuclid` + {lit}`extendedEuclid_spec`: EXTENDED-EUCLID returns
  `(d, x, y)` with `d = gcd a b = a·x + b·y`.

Notation:

- {lit}`Nat.gcd a b` : the greatest common divisor.
- {lit}`Nat.gcdA a b` / {lit}`Nat.gcdB a b` : the Bezout coefficients.
- `x·a + y·b` : integer linear combinations (coefficients in `ℤ`).

Deferred: the running-time (Lamé / Fibonacci) analysis of EUCLID, and
modular arithmetic, primality testing, and RSA (§31.3–31.9).
-/

namespace CLRS

namespace Chapter31

/-- Lemma 31.2 (Euclid's recursion): `gcd(a, b) = gcd(b mod a, a)`. -/
theorem euclid_recursion (a b : ℕ) : Nat.gcd a b = Nat.gcd (b % a) a :=
  Nat.gcd_rec a b

/-- Lemma 31.2: `gcd(0, b) = b`. -/
theorem gcd_zero_left (b : ℕ) : Nat.gcd 0 b = b :=
  Nat.gcd_zero_left b

/-- Lemma 31.2: `gcd(a, 0) = a`. -/
theorem gcd_zero_right (a : ℕ) : Nat.gcd a 0 = a :=
  Nat.gcd_zero_right a

/--
**EUCLID (CLRS §31.2).**  Compute `gcd a b` by the recursion
`gcd(a, b) = gcd(b mod a, a)` for `a > 0` and `gcd(0, b) = b`.  Total by
well-founded recursion on the first argument (it strictly decreases to
`b mod (a+1) < a+1`), so termination is part of the definition.
-/
def euclid : ℕ → ℕ → ℕ
  | 0, b => b
  | a' + 1, b => euclid (b % (a' + 1)) (a' + 1)
termination_by a b => a
decreasing_by
  exact Nat.mod_lt b (Nat.succ_pos a')

/-- **EUCLID is correct**: `euclid a b` returns `Nat.gcd a b`. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  induction a, b using Nat.gcd.induction with
  | H0 b => simp [euclid]
  | H1 a b ha ih =>
      cases a with
      | zero => exact (Nat.ne_of_gt ha rfl).elim
      | succ a' =>
          simp [euclid]
          rw [ih]
          rw [← Nat.gcd_succ]

/-- **EUCLID terminates**: it is total, so every call returns a value. -/
theorem euclid_terminates (a b : ℕ) : ∃ r : ℕ, euclid a b = r :=
  ⟨euclid a b, rfl⟩

/-- Lemma 31.3 (**Bezout's identity**): `gcd a b` is an integer linear
combination of `a` and `b`. -/
theorem gcd_is_linear_combination (a b : ℕ) :
    (Nat.gcd a b : ℤ) = (a : ℤ) * Nat.gcdA a b + (b : ℤ) * Nat.gcdB a b :=
  Nat.gcd_eq_gcd_ab a b

/-- Corollary 31.3: `gcd a b` divides every integer linear combination of
`a` and `b`. -/
theorem gcd_dvd_linear_combination (a b : ℕ) (x y : ℤ) :
    (Nat.gcd a b : ℤ) ∣ x * (a : ℤ) + y * (b : ℤ) := by
  have hga : (Nat.gcd a b : ℤ) ∣ (a : ℤ) := by exact_mod_cast Nat.gcd_dvd_left a b
  have hgb : (Nat.gcd a b : ℤ) ∣ (b : ℤ) := by exact_mod_cast Nat.gcd_dvd_right a b
  exact dvd_add (dvd_mul_of_dvd_right hga x) (dvd_mul_of_dvd_right hgb y)

/-- Theorem 31.2, lower-bound part: `gcd a b` is no larger than any positive
linear combination of `a` and `b`. -/
theorem gcd_le_positive_linear_combination (a b : ℕ) {z : ℤ}
    (hzpos : 0 < z) (hz : ∃ x y : ℤ, z = x * (a : ℤ) + y * (b : ℤ)) :
    (Nat.gcd a b : ℤ) ≤ z := by
  rcases hz with ⟨x, y, rfl⟩
  exact Int.le_of_dvd hzpos (gcd_dvd_linear_combination a b x y)

/--
**Theorem 31.2.**  `gcd a b` is the smallest positive linear combination of
`a` and `b` (for `a ≠ 0 ∨ b ≠ 0`).  Bezout's identity shows it is itself a
positive linear combination; Corollary 31.3 shows it divides (hence is `≤`)
every positive one.
-/
theorem gcd_is_smallest_positive_linear_combination (a b : ℕ) (hab : a ≠ 0 ∨ b ≠ 0) :
    IsLeast {z : ℤ | 0 < z ∧ ∃ x y : ℤ, z = x * (a : ℤ) + y * (b : ℤ)}
      (Nat.gcd a b : ℤ) := by
  constructor
  · constructor
    · rcases hab with ha | hb
      · exact_mod_cast Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)
      · exact_mod_cast Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hb)
    · refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
      rw [← mul_comm (a : ℤ), ← mul_comm (b : ℤ)]
      exact gcd_is_linear_combination a b
  · intro z hz
    exact gcd_le_positive_linear_combination a b hz.1 hz.2

/-- Corollary 31.4: `a` and `b` are coprime exactly when `gcd a b = 1`. -/
theorem gcd_eq_one_iff_coprime (a b : ℕ) : Nat.gcd a b = 1 ↔ Nat.Coprime a b :=
  Nat.coprime_iff_gcd_eq_one.symm

/-- Corollary 31.4: `a` and `b` are coprime exactly when `1` is an integer
linear combination of them. -/
theorem coprime_iff_one_linear_combination (a b : ℕ) :
    Nat.Coprime a b ↔ ∃ x y : ℤ, 1 = x * (a : ℤ) + y * (b : ℤ) := by
  constructor
  · intro hcop
    have h := Nat.gcd_eq_gcd_ab a b
    rw [hcop.gcd_eq_one] at h
    refine ⟨Nat.gcdA a b, Nat.gcdB a b, ?_⟩
    rw [← mul_comm (a : ℤ), ← mul_comm (b : ℤ)]
    exact h
  · rintro ⟨x, y, h⟩
    have hdiv : (Nat.gcd a b : ℤ) ∣ 1 := by
      rw [h]
      exact gcd_dvd_linear_combination a b x y
    have hgcd : Nat.gcd a b = 1 := by
      have hdiv' : (Nat.gcd a b : ℤ).natAbs ∣ (1 : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr hdiv
      have hg1 : (Nat.gcd a b : ℤ).natAbs = 1 := Nat.dvd_one.mp (by simpa using hdiv')
      exact (by simpa using hg1)
    exact hgcd

/-- Corollary 31.4: dividing `a` and `b` by their gcd yields coprime numbers. -/
theorem gcd_div_gcd_coprime (a b : ℕ) (h : 0 < Nat.gcd a b) :
    Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b) :=
  Nat.coprime_div_gcd_div_gcd h

/--
**EXTENDED-EUCLID (CLRS §31.2).**  Return `(d, x, y)` with `d = gcd a b` and
`d = a·x + b·y`.  Mathlib's `Nat.gcdA`/`Nat.gcdB` supply the Bezout
coefficients.
-/
def extendedEuclid (a b : ℕ) : ℕ × ℤ × ℤ :=
  (Nat.gcd a b, Nat.gcdA a b, Nat.gcdB a b)

/-- **EXTENDED-EUCLID is correct**: it returns `d = gcd a b` together with
coefficients `x`, `y` satisfying `d = a·x + b·y`. -/
theorem extendedEuclid_spec (a b : ℕ) :
    let (d, x, y) := extendedEuclid a b
    d = Nat.gcd a b ∧ (d : ℤ) = (a : ℤ) * x + (b : ℤ) * y := by
  simp [extendedEuclid, Nat.gcd_eq_gcd_ab]

end Chapter31

end CLRS
