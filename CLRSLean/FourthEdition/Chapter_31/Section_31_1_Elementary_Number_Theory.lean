import Mathlib

/-!
# 31.1 Elementary Number-Theoretic Notions

CLRS §31.1: divisibility, the division theorem, the greatest common divisor,
coprime, and prime numbers.

Main results:

- Lemma 31.1 ({lit}`divides_refl`, {lit}`divides_zero`, {lit}`divides_trans`,
  {lit}`divides_mul_right`, {lit}`divides_add`, {lit}`divides_sub`): the basic
  divisibility facts used throughout the chapter.
- Theorem 31.1 ({lit}`division_theorem`): for `b > 0`, `a = q·b + r` with
  `0 ≤ r < b` has a unique quotient `q` and remainder `r`.
- {lit}`IsGCD` / {lit}`nat_gcd_isGCD` / {lit}`IsGCD.eq_gcd`: the
  greatest-common-divisor property predicate and its agreement with Mathlib's
  {lit}`Nat.gcd`.
- {lit}`coprime_iff_gcd_eq_one` / {lit}`coprime_iff_no_common_divisor`:
  characterizations of {lit}`Nat.Coprime`.
- {lit}`prime_def_gt_one`, {lit}`prime_two`, and {lit}`exists_prime_ge`
  (Euclid's theorem: there are infinitely many primes).

Notation:

- {lit}`a ∣ b` : `a` divides `b`.
- {lit}`Nat.gcd a b` : the greatest common divisor.
- {lit}`Nat.Coprime a b` : `gcd a b = 1`.
- {lit}`Nat.Prime p` : `p` is prime.

Deferred: lcm results (Mathlib `Nat.lcm` is available; a dedicated lcm layer
is deferred to the modular-arithmetic section).
-/

namespace CLRS

namespace Chapter31

/-- `g` is a **greatest common divisor** of `a` and `b`: a common divisor that
is divisible by every common divisor (the universal property).  For `g > 0`
this is equivalent to CLRS's wording "the largest `d` with `d ∣ a` and
`d ∣ b`"; the universal form also behaves at `g = 0`. -/
def IsGCD (g a b : ℕ) : Prop :=
  g ∣ a ∧ g ∣ b ∧ ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ g

/-- `Nat.gcd a b` is a greatest common divisor of `a` and `b`. -/
theorem nat_gcd_isGCD (a b : ℕ) : IsGCD (Nat.gcd a b) a b :=
  ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b, fun d hda hdb => Nat.dvd_gcd hda hdb⟩

/-- The greatest-common-divisor property determines the value: if `g` is a
greatest common divisor of `a` and `b`, then `g = Nat.gcd a b`. -/
theorem IsGCD.eq_gcd {g a b : ℕ} (hg : IsGCD g a b) : g = Nat.gcd a b :=
  Nat.dvd_antisymm (Nat.dvd_gcd hg.1 hg.2.1)
    (hg.2.2 (Nat.gcd a b) (Nat.gcd_dvd_left a b) (Nat.gcd_dvd_right a b))

/-- For a positive greatest common divisor, the universal property gives the
CLRS "largest common divisor" form: every common divisor is `≤ g`. -/
theorem IsGCD.greatest {g a b : ℕ} (hgpos : 0 < g) (hg : IsGCD g a b) :
    ∀ d : ℕ, d ∣ a → d ∣ b → d ≤ g := by
  intro d hda hdb
  exact Nat.le_of_dvd hgpos (hg.2.2 d hda hdb)

/-- Lemma 31.1: every number divides itself. -/
theorem divides_refl (a : ℕ) : a ∣ a := Nat.dvd_refl a

/-- Lemma 31.1: every number divides zero. -/
theorem divides_zero (a : ℕ) : a ∣ 0 := Nat.dvd_zero a

/-- Lemma 31.1: divisibility is transitive. -/
theorem divides_trans {a b c : ℕ} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c :=
  Nat.dvd_trans hab hbc

/-- Lemma 31.1: if `a ∣ b` then `a ∣ b·c`. -/
theorem divides_mul_right {a b c : ℕ} (hab : a ∣ b) : a ∣ b * c :=
  Nat.dvd_mul_right_of_dvd hab c

/-- Lemma 31.1: if `a ∣ b` and `a ∣ c` then `a ∣ b + c`. -/
theorem divides_add {a b c : ℕ} (hab : a ∣ b) (hac : a ∣ c) : a ∣ b + c :=
  Nat.dvd_add hab hac

/-- Lemma 31.1: if `a ∣ b` and `a ∣ c` then `a ∣ b - c`. -/
theorem divides_sub {a b c : ℕ} (hab : a ∣ b) (hac : a ∣ c) : a ∣ b - c :=
  Nat.dvd_sub hab hac

/-- If `a` divides both `b` and `c`, then `a` divides every integer linear
combination `x·b + y·c` of them. -/
theorem divides_linear_combination {a b c x y : ℕ} (hab : a ∣ b) (hac : a ∣ c) :
    a ∣ x * b + y * c :=
  Nat.dvd_add (by simpa [Nat.mul_comm] using Nat.dvd_mul_right_of_dvd hab x)
    (by simpa [Nat.mul_comm] using Nat.dvd_mul_right_of_dvd hac y)

/-- Two representations of `a` as `q·b + r` with `0 ≤ r < b` agree: the
division theorem's `(q, r)` is unique. -/
lemma division_unique (a b q₁ r₁ q₂ r₂ : ℕ) (hb : 0 < b)
    (h₁ : a = q₁ * b + r₁) (hr₁ : r₁ < b)
    (h₂ : a = q₂ * b + r₂) (hr₂ : r₂ < b) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have h : q₁ * b + r₁ = q₂ * b + r₂ := h₁.symm.trans h₂
  have hmod₁ : (q₁ * b + r₁) % b = r₁ := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hr₁]
  have hmod₂ : (q₂ * b + r₂) % b = r₂ := by
    rw [Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hr₂]
  have hr : r₁ = r₂ := by
    calc r₁ = (q₁ * b + r₁) % b := hmod₁.symm
         _ = (q₂ * b + r₂) % b := congrArg (fun x => x % b) h
         _ = r₂ := hmod₂
  have hb_mul : q₁ * b = q₂ * b := by
    exact Nat.add_right_cancel (by rwa [← hr] at h)
  have hq : q₁ = q₂ := Nat.mul_right_cancel hb hb_mul
  exact ⟨hq, hr⟩

/--
**Theorem 31.1 (Division theorem).**  For `a` and `b > 0`, there is a unique
pair `(q, r)` with `a = q·b + r` and `0 ≤ r < b` (over `ℕ`, `0 ≤ r` is
automatic).  `q` is the quotient and `r` the remainder.
-/
theorem division_theorem (a b : ℕ) (hb : 0 < b) :
    ∃! q : ℕ, ∃! r : ℕ, a = q * b + r ∧ r < b := by
  have hda : a = a / b * b + a % b := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod a b).symm
  refine ⟨a / b, ?_⟩
  constructor
  · refine ⟨a % b, ?_, ?_⟩
    · exact ⟨hda, Nat.mod_lt a hb⟩
    · intro r' hr'
      exact (division_unique a b (a / b) (a % b) (a / b) r' hb
        hda (Nat.mod_lt a hb) hr'.1 hr'.2).2.symm
  · intro q hq
    rcases hq with ⟨r, hr, hrq⟩
    exact (division_unique a b q r (a / b) (a % b) hb hr.1 hr.2
      hda (Nat.mod_lt a hb)).1

/-- `a` and `b` are coprime exactly when their gcd is one. -/
theorem coprime_iff_gcd_eq_one (a b : ℕ) : Nat.Coprime a b ↔ Nat.gcd a b = 1 :=
  Nat.coprime_iff_gcd_eq_one

/-- `a` and `b` are coprime exactly when they have no common divisor other
than one. -/
theorem coprime_iff_no_common_divisor (a b : ℕ) :
    Nat.Coprime a b ↔ ∀ d : ℕ, d ∣ a → d ∣ b → d = 1 := by
  rw [coprime_iff_gcd_eq_one, Nat.gcd_eq_one_iff]

/-- CLRS's definition of prime: `p > 1` and the only divisors of `p` are
`1` and `p` itself. -/
theorem prime_def_gt_one (p : ℕ) : Nat.Prime p ↔ 1 < p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p := by
  rw [Nat.prime_def]
  constructor
  · intro hp
    exact ⟨Nat.lt_of_lt_of_le (by norm_num) hp.1, hp.2⟩
  · intro hp
    exact ⟨by omega, hp.2⟩

/-- `2` is prime. -/
theorem prime_two : Nat.Prime 2 := by
  decide

/-- **Euclid's theorem**: for every `n` there is a prime `≥ n`, so there are
infinitely many primes. -/
theorem exists_prime_ge (n : ℕ) : ∃ p : ℕ, Nat.Prime p ∧ n ≤ p := by
  rcases Nat.exists_infinite_primes n with ⟨p, hp, hprime⟩
  exact ⟨p, hprime, hp⟩

end Chapter31

end CLRS
