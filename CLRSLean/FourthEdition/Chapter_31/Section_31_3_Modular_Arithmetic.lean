import Mathlib
import CLRSLean.FourthEdition.Chapter_31.Section_31_2_Greatest_Common_Divisor

/-!
# 31.3 Modular Arithmetic

CLRS §31.3: the arithmetic of the ring `Z_n` of residues modulo `n` — the
well-definedness of addition and multiplication, additive and multiplicative
inverses, cancellation, and the solvability criterion for linear congruences.

Main results:

- Theorem 31.5 ({lit}`mod_add`, {lit}`mod_mul`): `(a + b) mod n` and
  `(a · b) mod n` are well-defined on residues, so `+` and `·` descend to
  `Z_n`.
- Theorem 31.6 ({lit}`exists_mul_inverse_mod`): if `gcd(a, n) = 1`, then `a`
  has a multiplicative inverse modulo `n`.
- Theorem 31.9 ({lit}`mul_left_cancel_mod`): `gcd(c, n) = 1` and
  `a·c ≡ b·c (mod n)` imply `a ≡ b (mod n)` (cancellation in `Z_n`).
- Theorem 31.11 ({lit}`modular_linear_solvable`): the congruence
  `a·x ≡ b (mod n)` has a solution exactly when `gcd(a, n) ∣ b`.

Notation:

- {lit}`a ≡ b [MOD n]` : `Nat.ModEq` — `a` and `b` leave the same remainder
  modulo `n`.
- {lit}`ZMod n` : the ring of residues modulo `n`.
- {lit}`Nat.gcd a n` : the greatest common divisor.

Deferred: none (the enumeration of all solutions of a linear congruence is
proved in §31.4 via {lit}`CLRS.Chapter31.modularLinearEquationSolver`).
-/

namespace CLRS

namespace Chapter31

/-- Theorem 31.5: addition modulo `n` is well-defined on residues. -/
theorem mod_add (a b n : ℕ) : (a + b) % n = (a % n + b % n) % n :=
  Nat.add_mod a b n

/-- Theorem 31.5: multiplication modulo `n` is well-defined on residues. -/
theorem mod_mul (a b n : ℕ) : (a * b) % n = ((a % n) * (b % n)) % n :=
  Nat.mul_mod a b n

/-- Congruence preserves addition: `a ≡ b` and `c ≡ d` imply `a + c ≡ b + d`. -/
theorem modEq_add {a b c d n : ℕ} (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
    a + c ≡ b + d [MOD n] :=
  Nat.ModEq.add hab hcd

/-- Congruence preserves multiplication: `a ≡ b` and `c ≡ d` imply `a·c ≡ b·d`. -/
theorem modEq_mul {a b c d n : ℕ} (hab : a ≡ b [MOD n]) (hcd : c ≡ d [MOD n]) :
    a * c ≡ b * d [MOD n] :=
  Nat.ModEq.mul hab hcd

/-- Congruence preserves powers: `a ≡ b` implies `aᵏ ≡ bᵏ`. -/
theorem modEq_pow {a b n : ℕ} (hab : a ≡ b [MOD n]) (k : ℕ) :
    a ^ k ≡ b ^ k [MOD n] :=
  Nat.ModEq.pow k hab

/-- Congruence is an equivalence relation. -/
theorem modEq_refl (a n : ℕ) : a ≡ a [MOD n] := Nat.ModEq.refl a
theorem modEq_symm {a b n : ℕ} (h : a ≡ b [MOD n]) : b ≡ a [MOD n] := h.symm
theorem modEq_trans {a b c n : ℕ} (hab : a ≡ b [MOD n]) (hbc : b ≡ c [MOD n]) :
    a ≡ c [MOD n] := hab.trans hbc

/--
**Theorem 31.6.**  If `gcd(a, n) = 1`, then `a` has a multiplicative inverse
modulo `n`: there is `x` with `a·x ≡ 1 (mod n)`.
-/
theorem exists_mul_inverse_mod {a n : ℕ} [NeZero n] (hcop : Nat.Coprime a n) :
    ∃ x : ℕ, a * x ≡ 1 [MOD n] := by
  let x : ℕ := ((a : ZMod n)⁻¹).val
  refine ⟨x, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  have hx : (x : ZMod n) = (a : ZMod n)⁻¹ := by
    dsimp [x]
    simpa using (ZMod.natCast_val (R := ZMod n) ((a : ZMod n)⁻¹))
  rw [Nat.cast_mul, hx]
  simpa using (ZMod.coe_mul_inv_eq_one a hcop)

/--
**Theorem 31.9 (cancellation).**  If `gcd(c, n) = 1` and `a·c ≡ b·c (mod n)`,
then `a ≡ b (mod n)`.
-/
theorem mul_left_cancel_mod {a b c n : ℕ} (hcop : Nat.Coprime c n)
    (h : a * c ≡ b * c [MOD n]) : a ≡ b [MOD n] := by
  have h' : c * a ≡ c * b [MOD n] := by simpa [Nat.mul_comm] using h
  exact Nat.ModEq.cancel_left_of_coprime (Nat.gcd_comm n c ▸ hcop) h'

/--
**Theorem 31.11.**  The linear congruence `a·x ≡ b (mod n)` has a solution
exactly when `gcd(a, n) ∣ b`.
-/
theorem modular_linear_solvable (a b n : ℕ) [NeZero n] :
    (∃ x : ℕ, a * x ≡ b [MOD n]) ↔ Nat.gcd a n ∣ b := by
  constructor
  · rintro ⟨x, h⟩
    have hzn : (a * x : ZMod n) = (b : ZMod n) := by
      simpa using ((ZMod.natCast_eq_natCast_iff (a * x) b n).mpr h)
    let f : ZMod n →+* ZMod (Nat.gcd a n) := ZMod.castHom (Nat.gcd_dvd_right a n) (ZMod (Nat.gcd a n))
    have hf : f (a * x : ZMod n) = f (b : ZMod n) := congrArg f hzn
    have ha0 : (a : ZMod (Nat.gcd a n)) = 0 := (ZMod.natCast_eq_zero_iff a (Nat.gcd a n)).mpr (Nat.gcd_dvd_left a n)
    have hb0 : (b : ZMod (Nat.gcd a n)) = 0 := by
      have hfax : f (a * x : ZMod n) = 0 := by
        rw [map_mul]
        simp [ha0]
      simpa using (hf.symm.trans hfax)
    exact (ZMod.natCast_eq_zero_iff b (Nat.gcd a n)).mp hb0
  · intro h
    rcases h with ⟨k, hk⟩
    have hbez := Nat.gcd_eq_gcd_ab a n
    let x0 : ℤ := Nat.gcdA a n * (k : ℤ)
    let y0 : ℤ := Nat.gcdB a n * (k : ℤ)
    have hb : (b : ℤ) = (a : ℤ) * x0 + (n : ℤ) * y0 := by
      calc
        (b : ℤ) = (Nat.gcd a n : ℤ) * (k : ℤ) := by rw [hk]; norm_num
        _ = ((a : ℤ) * Nat.gcdA a n + (n : ℤ) * Nat.gcdB a n) * (k : ℤ) := by rw [hbez]
        _ = (a : ℤ) * (Nat.gcdA a n * (k : ℤ)) + (n : ℤ) * (Nat.gcdB a n * (k : ℤ)) := by ring
        _ = (a : ℤ) * x0 + (n : ℤ) * y0 := by rfl
    have hcong : (a : ℤ) * x0 ≡ (b : ℤ) [ZMOD n] := by
      rw [hb]
      exact (Int.modEq_iff_dvd.2 ⟨y0, by ring⟩)
    let x : ℕ := Int.toNat (x0 % n)
    have hxrep : (x : ℤ) ≡ x0 [ZMOD n] := by
      dsimp [x]
      rw [Int.ModEq]
      have hnn : (n : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
      have hnonneg : 0 ≤ x0 % n := Int.emod_nonneg x0 hnn
      rw [Int.toNat_of_nonneg hnonneg]
      rw [Int.emod_emod]
    have hcongx : (a : ℤ) * (x : ℤ) ≡ (b : ℤ) [ZMOD n] :=
      (Int.ModEq.mul_left (a : ℤ) hxrep).trans hcong
    exact ⟨x, by exact_mod_cast hcongx⟩

end Chapter31

end CLRS
