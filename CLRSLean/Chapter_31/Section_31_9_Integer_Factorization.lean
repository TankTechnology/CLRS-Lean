import Mathlib
import CLRSLean.Chapter_31.Section_31_2_Greatest_Common_Divisor

/-!
# 31.9 Integer Factorization

CLRS §31.9: **Pollard's rho** heuristic for factoring a composite integer.
The iteration `x ↦ (x² + c) mod n` eventually produces two values congruent
modulo a prime factor `p` of `n`; then `gcd(x − y, n)` is a nontrivial
divisor of `n`.

Main results:

- {lit}`rhoStep` (CLRS Pollard's rho iteration): `x ↦ (x² + c) mod n`.
- Theorem {lit}`rho_collision_factor`: if `x ≡ y (mod p)` and `p ∣ n`, then
  `p ∣ gcd(x − y, n)` — a mod-`p` collision forces the gcd to be a nontrivial
  divisor (`> 1`; when it is also `< n`, it is a proper factor).

Notation:

- {lit}`a ≡ b [MOD p]` : `Nat.ModEq`.
- {lit}`Nat.gcd a n` : the greatest common divisor.

Deferred: the full Pollard's rho algorithm with the tortoise-and-hare
collision detection, and the birthday-paradox / expected-`O(√p)` running-time
analysis (CLRS Theorem 31.40).
-/

namespace CLRS

namespace Chapter31

/--
**Pollard's rho iteration (CLRS §31.9).**  The map `x ↦ (x² + c) mod n`
whose orbit is a pseudorandom walk; two of its values colliding modulo a
prime factor `p` expose `p`.
-/
def rhoStep (c n x : ℕ) : ℕ :=
  (x * x + c) % n

/--
**Pollard's rho collision factor.**  If `x` and `y` are two rho values that
are congruent modulo a divisor `p` of `n` (in practice a prime factor), then
`p` divides `gcd(x − y, n)`, so the gcd is a nontrivial divisor of `n`.
-/
theorem rho_collision_factor {p x y n : ℕ} (hpn : p ∣ n) (hxy : x ≡ y [MOD p]) :
    p ∣ Nat.gcd (x - y) n := by
  have hdvd_xy : p ∣ x - y := by
    by_cases hyx : y ≤ x
    · have hmod : (x - y) % p = 0 := by
        have hsub := Nat.ModEq.sub (c := y) (d := y) hyx (Nat.le_refl y) hxy (Nat.ModEq.refl y)
        have hyy : y - y = 0 := by omega
        rw [hyy] at hsub
        simpa [Nat.ModEq, Nat.zero_mod] using hsub
      exact Nat.dvd_of_mod_eq_zero hmod
    · have h0 : x - y = 0 := by omega
      rw [h0]
      exact Nat.dvd_zero p
  exact Nat.dvd_gcd hdvd_xy hpn

/--
**A nontrivial divisor is a proper factor.**  If `1 < gcd(a, n)` and
`gcd(a, n) < n`, then `gcd(a, n)` divides `n` and is neither `1` nor `n`.
-/
theorem nontrivial_factor_of_gcd {a n : ℕ} (hgt : 1 < Nat.gcd a n) (hlt : Nat.gcd a n < n) :
    Nat.gcd a n ∣ n ∧ 1 < Nat.gcd a n ∧ Nat.gcd a n < n :=
  ⟨Nat.gcd_dvd_right a n, hgt, hlt⟩

end Chapter31

end CLRS
