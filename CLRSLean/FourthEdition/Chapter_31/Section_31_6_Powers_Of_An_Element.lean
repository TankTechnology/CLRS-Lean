import Mathlib
import CLRSLean.FourthEdition.Chapter_31.Section_31_3_Modular_Arithmetic

/-!
# 31.6 Powers of an Element

CLRS §31.6: modular exponentiation and the two theorems that make powers
modulo a number tractable — **Fermat's little theorem** (prime modulus) and
**Euler's theorem** (general modulus, via the totient function).

Main results:

- {lit}`modularExponentiation` + {lit}`modularExponentiation_spec`:
  computing `a^b mod n` by repeated squaring returns a number congruent to
  `a^b` modulo `n`.
- Theorem {lit}`fermat_little_theorem` (CLRS Theorem 31.30): for prime `p`,
  `a^p ≡ a (mod p)`.
- Theorem {lit}`euler_theorem` (CLRS Euler's theorem): for `gcd(a, n) = 1`,
  `a^φ(n) ≡ 1 (mod n)`.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq`.
- {lit}`Nat.totient n` : Euler's totient `φ(n)`.

Deferred: none (the repeated-squaring recursion with its explicit operation
count is proved by {lit}`modExpWithCount` and {lit}`modExpWithCount_count_le`).
-/

namespace CLRS

namespace Chapter31

/-- **MODULAR-EXPONENTIATION (CLRS §31.6).**  Compute `a^b mod n`.  The
value is the remainder of `a^b` upon division by `n`; the repeated-squaring
algorithm computes it in `O(log b)` multiplications. -/
def modularExponentiation (a b n : ℕ) : ℕ :=
  a ^ b % n

/-- **MODULAR-EXPONENTIATION is correct**: `modularExponentiation a b n`
is congruent to `a^b` modulo `n`. -/
theorem modularExponentiation_spec (a b n : ℕ) :
    modularExponentiation a b n ≡ a ^ b [MOD n] := by
  rw [Nat.ModEq]
  unfold modularExponentiation
  rw [Nat.mod_mod]

/--
**Fermat's little theorem (CLRS Theorem 31.30).**  For a prime `p` and any
`a`, `a^p ≡ a (mod p)`.
-/
theorem fermat_little_theorem {p a : ℕ} (hp : Nat.Prime p) : a ^ p ≡ a [MOD p] := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := ZMod.pow_card (p := p) (x := (a : ZMod p))
  exact (ZMod.natCast_eq_natCast_iff (a ^ p) a p).mp (by
    simpa [Nat.cast_pow] using h)

/--
**Euler's theorem (CLRS §31.6).**  If `gcd(a, n) = 1` and `1 < n`, then
`a^φ(n) ≡ 1 (mod n)`.
-/
theorem euler_theorem {a n : ℕ} (hn : 1 < n) (hcop : Nat.Coprime a n) :
    a ^ Nat.totient n ≡ 1 [MOD n] := by
  rw [Nat.ModEq]
  rw [Nat.pow_totient_mod_eq_one hn hcop]
  rw [Nat.mod_eq_of_lt hn]

/--
**MODULAR-EXPONENTIATION by repeated squaring (CLRS §31.6).**  Compute
`a^b mod n` with the square-and-multiply recursion that reads the binary
digits of `b` least-significant first: each level squares the running residue,
and a `1` bit additionally multiplies by `a`.  The returned pair carries the
residue together with the number of modular multiplications performed (one
square per bit plus one multiply per `1` bit).
-/
def modExpWithCount (a n : ℕ) (b : ℕ) : ℕ × ℕ :=
  if hb : b = 0 then (1 % n, 0)
  else
    let r := modExpWithCount a n (b / 2)
    let d := (r.1 * r.1) % n
    if b % 2 = 0 then (d, r.2 + 1) else ((d * a) % n, r.2 + 2)
termination_by b
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)

/-- One square step: `(a^(b/2) mod n)² mod n = a^(2·(b/2)) mod n`. -/
private lemma mod_sq_mod (a n b : ℕ) :
    ((a ^ (b / 2) % n) * (a ^ (b / 2) % n)) % n = a ^ (2 * (b / 2)) % n := by
  rw [← Nat.mul_mod]
  rw [← Nat.pow_add]
  rw [show b / 2 + b / 2 = 2 * (b / 2) by omega]

/-- `(X mod n) · a mod n = X · a mod n`: the residue of a product depends only
on the residue of `X`. -/
private lemma mod_mul_mod_left (X a n : ℕ) : ((X % n) * a) % n = (X * a) % n := by
  rw [Nat.mul_mod (X % n) a n]
  rw [Nat.mod_mod]
  rw [← Nat.mul_mod X a n]

/-- One square-then-multiply step:
`((a^(b/2) mod n)² mod n) · a mod n = a^(2·(b/2)+1) mod n`. -/
private lemma mod_sq_mul_mod (a n b : ℕ) :
    (((a ^ (b / 2) % n) * (a ^ (b / 2) % n)) % n * a) % n = a ^ (2 * (b / 2) + 1) % n := by
  rw [mod_sq_mod]
  rw [mod_mul_mod_left]
  rw [← Nat.pow_succ]

/--
**MODULAR-EXPONENTIATION is correct**: the repeated-squaring recursion
returns exactly `a^b mod n` (CLRS §31.6).
-/
theorem modExpWithCount_spec (a n b : ℕ) : (modExpWithCount a n b).1 = a ^ b % n := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · simp [modExpWithCount, hb]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)
      have ihr := ih (b / 2) hlt
      unfold modExpWithCount
      rw [dif_neg hb]
      simp only
      split_ifs with heven
      · -- even: square only
        calc
          (((modExpWithCount a n (b / 2)).1 * (modExpWithCount a n (b / 2)).1) % n)
              = ((a ^ (b / 2) % n) * (a ^ (b / 2) % n)) % n := by rw [ihr]
          _ = a ^ (2 * (b / 2)) % n := by rw [mod_sq_mod]
          _ = a ^ b % n := by
            rw [show 2 * (b / 2) = b by
              have hdiv := Nat.div_add_mod b 2
              omega]
      · -- odd: square and multiply by `a`
        have hodd : b % 2 = 1 := by
          have hmodlt := Nat.mod_lt b (by decide : 0 < 2)
          omega
        calc
          ((((modExpWithCount a n (b / 2)).1 * (modExpWithCount a n (b / 2)).1) % n) * a) % n
              = (((a ^ (b / 2) % n) * (a ^ (b / 2) % n)) % n * a) % n := by rw [ihr]
          _ = a ^ (2 * (b / 2) + 1) % n := by rw [mod_sq_mul_mod]
          _ = a ^ b % n := by
            rw [show 2 * (b / 2) + 1 = b by
              have hdiv := Nat.div_add_mod b 2
              omega]

/-- `Nat.size (b / 2) + 1 = Nat.size b` for nonzero `b` (dropping the least
significant bit reduces the bit length by exactly one). -/
private lemma size_div_two_succ {b : ℕ} (hb : b ≠ 0) : Nat.size (b / 2) + 1 = Nat.size b := by
  have hdecomp : Nat.bit b.bodd b.div2 = b := Nat.bit_bodd_div2 b
  have hnb : Nat.bit b.bodd b.div2 ≠ 0 := by
    rw [hdecomp]
    exact hb
  calc
    Nat.size (b / 2) + 1 = b.div2.size + 1 := by rw [Nat.div2_val]
    _ = b.div2.size.succ := rfl
    _ = Nat.size (Nat.bit b.bodd b.div2) := by rw [Nat.size_bit hnb]
    _ = Nat.size b := by rw [hdecomp]

/--
**MODULAR-EXPONENTIATION uses `O(log b)` multiplications**: the repeated
squaring recursion performs at most `2 · Nat.size b` modular multiplications,
where `Nat.size b` is the number of bits of `b` (CLRS §31.6).
-/
theorem modExpWithCount_count_le (a n b : ℕ) : (modExpWithCount a n b).2 ≤ 2 * Nat.size b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases hb : b = 0
    · simp [modExpWithCount, hb]
    · have hlt : b / 2 < b := Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)
      have ihr := ih (b / 2) hlt
      unfold modExpWithCount
      rw [dif_neg hb]
      simp only
      split_ifs with heven
      · have hs : Nat.size (b / 2) + 1 = Nat.size b := size_div_two_succ hb
        omega
      · have hs : Nat.size (b / 2) + 1 = Nat.size b := size_div_two_succ hb
        omega

end Chapter31

end CLRS
