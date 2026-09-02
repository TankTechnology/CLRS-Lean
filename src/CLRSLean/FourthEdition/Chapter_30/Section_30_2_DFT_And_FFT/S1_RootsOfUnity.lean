import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-! # Chapter 30.2: Roots-of-unity toolkit

This module packages the primitive-root facts used by the generic DFT,
including the complete finite root-sum orthogonality statement.
-/

namespace CLRS
namespace Chapter30

/-- The first `n` powers of a primitive `n`-th root are injective. -/
theorem primitiveRoot_powers_injective [CommRing K] {n : Nat} {omega : K}
    (homega : IsPrimitiveRoot omega n) :
    Function.Injective (fun i : Fin n => omega ^ i.1) := by
  intro i j hij
  apply Fin.ext
  exact homega.pow_inj i.2 j.2 hij

/-- Squaring a primitive root of order `2 * n` gives one of order `n`. -/
theorem primitiveRoot_square [CommMonoid K] {n : Nat} {omega : K}
    (hn : 0 < n) (homega : IsPrimitiveRoot omega (2 * n)) :
    IsPrimitiveRoot (omega ^ 2) n := by
  exact homega.pow (by omega) rfl

/-- The inverse of a primitive root has the same order. -/
theorem primitiveRoot_inv [CommGroupWithZero K] {n : Nat} {omega : K}
    (homega : IsPrimitiveRoot omega n) :
    IsPrimitiveRoot omega⁻¹ n :=
  homega.inv

/-- The halfway power of a primitive even-order root is negative one. -/
theorem primitiveRoot_half_pow_eq_neg_one [Field K] [CharZero K]
    {n : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega (2 * n)) :
    omega ^ n = -1 := by
  have htwo : IsPrimitiveRoot (omega ^ n) 2 := by
    exact homega.pow (by omega) (by omega)
  exact htwo.eq_neg_one_of_two_right

/-- A finite geometric sum vanishes when its base is a nontrivial `n`-th
root of one. -/
private theorem fin_root_sum_eq_zero [Field K] {n : Nat} {x : K}
    (hxpow : x ^ n = 1) (hx : x ≠ 1) :
    (∑ j : Fin n, x ^ j.1) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hgeom := geom_sum_mul x n
  have hzero : (∑ j ∈ Finset.range n, x ^ j) * (x - 1) = 0 := by
    simpa [hxpow] using hgeom
  exact (mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr hx)

/-- The powers of a primitive root sum to the cardinality precisely on
exponents divisible by its order, and otherwise sum to zero. -/
theorem root_sum_orthogonality [Field K] [CharZero K]
    {n exponent : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega n) :
    (∑ j : Fin n, omega ^ (j.1 * exponent)) =
      if n ∣ exponent then (n : K) else 0 := by
  by_cases hdiv : n ∣ exponent
  · rw [if_pos hdiv]
    obtain ⟨t, rfl⟩ := hdiv
    simp [pow_mul, homega.pow_eq_one, Nat.mul_assoc, Nat.mul_comm,
      Nat.mul_left_comm]
  · rw [if_neg hdiv]
    have hxne : omega ^ exponent ≠ 1 := by
      intro hpow
      exact hdiv ((homega.pow_eq_one_iff_dvd exponent).mp hpow)
    have hxpow : (omega ^ exponent) ^ n = 1 := by
      rw [← pow_mul]
      rw [Nat.mul_comm]
      rw [pow_mul, homega.pow_eq_one, one_pow]
    simpa [pow_mul, Nat.mul_comm] using
      (fin_root_sum_eq_zero hxpow hxne)

/-- Orthogonality in the signed form used by Fourier inversion. -/
theorem root_sum_difference_orthogonality [Field K] [CharZero K]
    {n : Nat} (hn : 0 < n) {omega : K}
    (homega : IsPrimitiveRoot omega n) (i k : Fin n) :
    (∑ j : Fin n,
      omega ^ (j.1 * i.1) * omega⁻¹ ^ (j.1 * k.1)) =
      if i = k then (n : K) else 0 := by
  let x : K := omega ^ i.1 * omega⁻¹ ^ k.1
  have homega0 : omega ≠ 0 := homega.ne_zero (Nat.ne_of_gt hn)
  have hx_iff : x = 1 ↔ i = k := by
    constructor
    · intro hx
      apply Fin.ext
      apply homega.pow_inj i.2 k.2
      have hk0 : omega ^ k.1 ≠ 0 := pow_ne_zero _ homega0
      apply (div_eq_one_iff_eq hk0).mp
      simpa [x, div_eq_mul_inv, inv_pow] using hx
    · intro hik
      subst k
      simp [x, ← mul_pow, homega0]
  have hxpow : x ^ n = 1 := by
    have hi : (omega ^ i.1) ^ n = (omega ^ n) ^ i.1 := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    have hk : (omega⁻¹ ^ k.1) ^ n = (omega⁻¹ ^ n) ^ k.1 := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    dsimp [x]
    rw [mul_pow, hi, hk, homega.pow_eq_one, homega.inv.pow_eq_one]
    simp
  have hsum :
      (∑ j : Fin n,
        omega ^ (j.1 * i.1) * omega⁻¹ ^ (j.1 * k.1)) =
        ∑ j : Fin n, x ^ j.1 := by
    apply Finset.sum_congr rfl
    intro j _
    simp [x, mul_pow, pow_mul, Nat.mul_comm]
  rw [hsum]
  by_cases hik : i = k
  · rw [if_pos hik, (hx_iff.mpr hik)]
    simp
  · rw [if_neg hik]
    exact fin_root_sum_eq_zero hxpow (fun hx => hik (hx_iff.mp hx))

end Chapter30
end CLRS
