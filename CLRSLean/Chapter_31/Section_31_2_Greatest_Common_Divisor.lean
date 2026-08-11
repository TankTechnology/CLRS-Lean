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
- **Running time (Lamé / Fibonacci)**: {lit}`euclidDivisions` counts the
  recursive calls of `EUCLID`.  Lemma 31.10
  ({lit}`fib_le_of_euclidDivisions`) gives the Fibonacci lower bounds
  `a ≥ F_{k+2}` and `b ≥ F_{k+1}` for `k` calls; Theorem 31.11, **Lamé's
  theorem** ({lit}`euclidDivisions_lt`), is the running-time bound
  `b < F_{k+1} ⇒` fewer than `k` calls; and Corollary 31.12
  ({lit}`euclidDivisions_le_two_log`) records the `O(log b)` bound.  The
  helper lemmas {lit}`fib_two_step_ge_pow_two` and {lit}`pow_two_le_fib`
  prove the exponential Fibonacci growth `2^(n/2) ≤ F_{n+2}` used by
  Corollary 31.12.
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

This section is complete.  Modular arithmetic, primality testing, and RSA
are covered in their own sections (§31.3–31.9).
-/

open Nat

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

/--
**EUCLID division count (CLRS §31.2).**  The number of recursive calls that
`EUCLID(a, b)` makes under CLRS's recursion `EUCLID(a, b) = EUCLID(b, a mod b)`
for `b > 0`, with `EUCLID(a, 0) = a`.  Total by well-founded recursion on the
second argument (each call drops to `a mod b < b`).
-/
def euclidDivisions : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 => 1 + euclidDivisions (b + 1) (a % (b + 1))
termination_by _ b => b
decreasing_by
  exact Nat.mod_lt a (Nat.succ_pos b)

/--
**Lemma 31.10 (Lamé, core direction).**  If `EUCLID(a, b)` with `a > b ≥ 1`
invokes `k` recursive calls, then the Fibonacci bounds `b ≥ F_{k+1}` and
`a ≥ F_{k+2}` hold.
-/
theorem fib_le_of_euclidDivisions (a b : ℕ) (hb0 : 0 < b) (hba : b < a) :
    fib (euclidDivisions a b + 1) ≤ b ∧ fib (euclidDivisions a b + 2) ≤ a := by
  revert a hb0 hba
  induction b using Nat.strong_induction_on with
  | h b ih =>
      intro a hb0 hba
      cases b with
      | zero => omega
      | succ b' =>
          let r := a % (b' + 1)
          have hmain : euclidDivisions a (b' + 1) = 1 + euclidDivisions (b' + 1) r := by
            simp [euclidDivisions, r]
          by_cases hr0 : r = 0
          · have hk1 : euclidDivisions a (b' + 1) = 1 := by
              rw [hmain]
              simp [euclidDivisions, r, hr0]
            constructor
            · rw [hk1]
              simp [fib_two]
            · rw [hk1]
              simp [fib_add_two]
              have hdvd : b' + 1 ∣ a := by
                exact Nat.dvd_of_mod_eq_zero (by simpa [r] using hr0)
              rcases hdvd with ⟨q, ha⟩
              have hqb : b' + 1 < (b' + 1) * q := by
                simpa [ha] using hba
              have hq : 1 < q := by
                exact (Nat.mul_lt_mul_left (by omega : 0 < b' + 1)).mp (by simpa using hqb)
              have hle : 2 ≤ (b' + 1) * q := by
                simpa using (Nat.mul_le_mul (by omega : 1 ≤ b' + 1) (Nat.succ_le_of_lt hq))
              rw [ha]
              exact hle
          · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
            have hrlt : r < b' + 1 := by
              simpa [r] using (Nat.mod_lt a (Nat.succ_pos b'))
            have ih' := ih r hrlt (b' + 1) hrpos hrlt
            let k' := euclidDivisions (b' + 1) r
            have hk' : euclidDivisions a (b' + 1) = 1 + k' := by
              simpa [k'] using hmain
            constructor
            · rw [hk']
              have harg : (1 + k') + 1 = k' + 2 := by omega
              rw [harg]
              simpa [k'] using ih'.2
            · rw [hk']
              have hfib3 : fib (k' + 3) = fib (k' + 1) + fib (k' + 2) := by
                simpa [Nat.add_assoc] using (fib_add_two (n := k' + 1))
              have hfib_sum : fib (k' + 1) + fib (k' + 2) ≤ r + (b' + 1) := by
                exact Nat.add_le_add (by simpa [k'] using ih'.1) (by simpa [k'] using ih'.2)
              have hra : r + (b' + 1) ≤ a := by
                have hmod : a = a / (b' + 1) * (b' + 1) + r := by
                  change a = a / (b' + 1) * (b' + 1) + a % (b' + 1)
                  rw [mul_comm]
                  exact (Nat.div_add_mod a (b' + 1)).symm
                have hq1 : 1 ≤ a / (b' + 1) := by
                  rw [Nat.le_div_iff_mul_le (Nat.succ_pos b')]
                  simpa using (Nat.le_of_lt hba)
                rw [hmod]
                have hle : b' + 1 ≤ a / (b' + 1) * (b' + 1) := by
                  simpa using (Nat.mul_le_mul_right (b' + 1) hq1)
                omega
              have harg : (1 + k') + 2 = k' + 3 := by omega
              calc
                fib ((1 + k') + 2) = fib (k' + 3) := by rw [harg]
                _ = fib (k' + 1) + fib (k' + 2) := hfib3
                _ ≤ r + (b' + 1) := hfib_sum
                _ ≤ a := hra

/--
**Theorem 31.11 (Lamé's theorem).**  For `k ≥ 1`, if `a > b ≥ 1` and
`b < F_{k+1}`, then `EUCLID(a, b)` makes fewer than `k` recursive calls —
equivalently, `EUCLID` needs `O(log b)` calls for inputs `a > b`.
-/
theorem euclidDivisions_lt {a b k : ℕ} (_hk : 1 ≤ k) (hb0 : 0 < b) (hba : b < a)
    (hbf : b < fib (k + 1)) : euclidDivisions a b < k := by
  have hcore := fib_le_of_euclidDivisions a b hb0 hba
  by_contra hnot
  have hge : k ≤ euclidDivisions a b := Nat.le_of_not_gt hnot
  have hmono : fib (k + 1) ≤ fib (euclidDivisions a b + 1) := by
    exact fib_mono (by omega)
  have : fib (k + 1) ≤ b := le_trans hmono hcore.1
  exact (not_lt_of_ge this) hbf

/--
**Exponential Fibonacci growth.**  For every `t`, `fib(2t+2) ≥ 2^t` and
`fib(2t+3) ≥ 2^t`; hence the Fibonacci sequence grows at least like
`2^(n/2)`.  This is the exponential bound that turns Lamé's theorem into the
`O(log b)` running-time bound.
-/
theorem fib_two_step_ge_pow_two (t : ℕ) :
    (2 ^ t ≤ fib (2 * t + 2)) ∧ (2 ^ t ≤ fib (2 * t + 3)) := by
  induction t with
  | zero =>
      constructor <;> norm_num [fib_two, fib_add_two, fib_one]
  | succ t ih =>
      have hA0 : 2 ^ t ≤ fib (2 * t + 2) := ih.1
      have hB0 : 2 ^ t ≤ fib (2 * t + 3) := ih.2
      have hA1 : 2 ^ (t + 1) ≤ fib (2 * (t + 1) + 2) := by
        have hfib : fib (2 * (t + 1) + 2) = fib (2 * t + 2) + fib (2 * t + 3) := by
          rw [show 2 * (t + 1) + 2 = 2 * t + 4 by ring]
          have h := fib_add_two (n := 2 * t + 2)
          rw [show (2 * t + 2) + 2 = 2 * t + 4 by omega,
              show (2 * t + 2) + 1 = 2 * t + 3 by omega] at h
          exact h
        rw [hfib]
        rw [show 2 ^ (t + 1) = 2 ^ t + 2 ^ t by rw [pow_succ]; ring]
        exact Nat.add_le_add hA0 hB0
      have hB1 : 2 ^ (t + 1) ≤ fib (2 * (t + 1) + 3) := by
        have hfib : fib (2 * (t + 1) + 3) = fib (2 * t + 3) + fib (2 * t + 4) := by
          rw [show 2 * (t + 1) + 3 = 2 * t + 5 by ring]
          have h := fib_add_two (n := 2 * t + 3)
          rw [show (2 * t + 3) + 2 = 2 * t + 5 by omega,
              show (2 * t + 3) + 1 = 2 * t + 4 by omega] at h
          exact h
        rw [hfib]
        have hA1' : 2 ^ (t + 1) ≤ fib (2 * t + 4) := by
          simpa [show 2 * (t + 1) + 2 = 2 * t + 4 by ring] using hA1
        exact le_trans (Nat.le_add_left _ _)
          (by simpa [Nat.add_comm] using (Nat.add_le_add hB0 hA1'))
      exact ⟨hA1, hB1⟩

/-- The Fibonacci sequence grows exponentially: `2^(n/2) ≤ fib (n+2)` for all
`n`. -/
theorem pow_two_le_fib (n : ℕ) : 2 ^ (n / 2) ≤ fib (n + 2) := by
  rcases Nat.even_or_odd n with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h2 : t + t = 2 * t := by omega
    simpa [h2] using (fib_two_step_ge_pow_two t).1
  · have hdiv : (2 * t + 1) / 2 = t := by
      simpa [show 1 / 2 = 0 by norm_num] using (Nat.mul_add_div (by decide : 2 > 0) t 1)
    rw [hdiv]
    have harg : (2 * t + 1) + 2 = 2 * t + 3 := by omega
    rw [harg]
    exact (fib_two_step_ge_pow_two t).2

/--
**Corollary 31.12.**  For `a > b ≥ 1`, `EUCLID(a, b)` makes at most
`2·log₂ b + 2` recursive calls — i.e. `O(log b)`.  Combining Lemma 31.10
with `b ≥ F_{k+1} ≥ 2^{(k−1)/2}` bounds the division count logarithmically.
-/
theorem euclidDivisions_le_two_log (a b : ℕ) (hb0 : 0 < b) (hba : b < a) :
    euclidDivisions a b ≤ 2 * Nat.log 2 b + 2 := by
  have hkge1 : 1 ≤ euclidDivisions a b := by
    rcases b with _ | b'
    · omega
    · simp [euclidDivisions]
  have hcore := fib_le_of_euclidDivisions a b hb0 hba
  have hpow_le_fib : 2 ^ ((euclidDivisions a b - 1) / 2) ≤ fib (euclidDivisions a b + 1) := by
    have h := pow_two_le_fib (euclidDivisions a b - 1)
    rwa [show (euclidDivisions a b - 1) + 2 = euclidDivisions a b + 1 by omega] at h
  have hpow_le_b : 2 ^ ((euclidDivisions a b - 1) / 2) ≤ b := le_trans hpow_le_fib hcore.1
  have hlog : (euclidDivisions a b - 1) / 2 ≤ Nat.log 2 b :=
    Nat.le_log_of_pow_le (by decide : 1 < 2) hpow_le_b
  have hk1 : euclidDivisions a b - 1 ≤ 2 * Nat.log 2 b + 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 2)] at hlog
    exact hlog
  omega

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
