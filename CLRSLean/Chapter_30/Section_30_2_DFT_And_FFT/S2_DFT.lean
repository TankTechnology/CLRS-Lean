import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.S1_RootsOfUnity
import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials
import Mathlib.Analysis.Fourier.ZMod

/-! # Chapter 30.2: The generic discrete Fourier transform

The reusable transform is defined over an arbitrary semiring with the positive
exponent convention used by CLRS.  The complex compatibility theorem below
keeps Mathlib's opposite sign visible at the boundary.
-/

namespace CLRS
namespace Chapter30

/-- The successive powers of `omega`, used as polynomial evaluation points. -/
def powerPoints [Monoid K] {n : Nat} (omega : K) : Fin n → K :=
  fun k => omega ^ k.1

/-- The positive-exponent discrete Fourier transform used by CLRS. -/
def dft [Semiring K] {n : Nat} (omega : K) (a : CoeffVector K n) :
    CoeffVector K n :=
  fun k => ∑ j : Fin n, a j * omega ^ (j.1 * k.1)

/-- The DFT is precisely evaluation of the represented polynomial at powers
of the root. -/
theorem dft_eq_pointValues [CommSemiring K] {n : Nat}
    (omega : K) (a : CoeffVector K n) :
    dft omega a = pointValues (powerPoints omega) (vectorToPolynomial a) := by
  funext k
  simp [dft, pointValues, powerPoints, vectorToPolynomial,
    Polynomial.eval_finsetSum, pow_mul, Nat.mul_comm]

/-- The DFT maps the zero vector to zero. -/
theorem dft_zero [Semiring K] {n : Nat} (omega : K) :
    dft omega (0 : CoeffVector K n) = 0 := by
  funext k
  simp [dft]

/-- The DFT preserves vector addition. -/
theorem dft_add [Semiring K] {n : Nat} (omega : K)
    (a b : CoeffVector K n) :
    dft omega (a + b) = dft omega a + dft omega b := by
  funext k
  simp [dft, add_mul, Finset.sum_add_distrib]

/-- Over a commutative semiring, the DFT commutes with scalar multiplication. -/
theorem dft_smul [CommSemiring K] {n : Nat} (omega c : K)
    (a : CoeffVector K n) :
    dft omega (c • a) = c • dft omega a := by
  funext k
  simp [dft, Finset.mul_sum, mul_assoc]

/-- Transport a `Fin n` vector to Mathlib's `ZMod n` indexing. -/
def finVectorToZMod {n : Nat} [NeZero n] (a : CoeffVector ℂ n) :
    ZMod n → ℂ :=
  fun j => a ((ZMod.finEquiv n).symm j)

/-- Transport a Mathlib `ZMod n` vector back to `Fin n` indexing. -/
def zmodVectorToFin {n : Nat} [NeZero n] (a : ZMod n → ℂ) :
    CoeffVector ℂ n :=
  fun j => a (ZMod.finEquiv n j)

/-- Transporting a finite vector to `ZMod` and back is exact. -/
@[simp] theorem zmodVectorToFin_finVectorToZMod {n : Nat} [NeZero n]
    (a : CoeffVector ℂ n) :
    zmodVectorToFin (finVectorToZMod a) = a := by
  funext j
  simp [zmodVectorToFin, finVectorToZMod]

/-- Transporting a `ZMod` vector to `Fin` and back is exact. -/
@[simp] theorem finVectorToZMod_zmodVectorToFin {n : Nat} [NeZero n]
    (a : ZMod n → ℂ) :
    finVectorToZMod (zmodVectorToFin a) = a := by
  funext j
  simp [zmodVectorToFin, finVectorToZMod]

/-- The ring equivalence sends a bounded natural index to its residue class. -/
theorem finEquiv_eq_natCast {n : Nat} [NeZero n] (j : Fin n) :
    ZMod.finEquiv n j = (j.1 : ZMod n) := by
  apply ZMod.val_injective
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt j.2]
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- A power of the positive principal root is Mathlib's standard additive
character at the corresponding residue class. -/
private theorem principalRoot_pow_eq_stdAddChar {n : Nat} [NeZero n]
    (m : Nat) :
    (Complex.exp (2 * Real.pi * Complex.I / n)) ^ m =
      ZMod.stdAddChar (m : ZMod n) := by
  rw [← Complex.exp_nat_mul]
  rw [show (m : ZMod n) = ((m : Int) : ZMod n) by norm_num]
  rw [ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

/-- The generic positive-sign transform agrees with Mathlib's negative-sign
transform after explicitly negating the output index. -/
theorem complexDft_mathlib {n : Nat} [NeZero n]
    (a : CoeffVector ℂ n) (k : Fin n) :
    dft (Complex.exp (2 * Real.pi * Complex.I / n)) a k =
      ZMod.dft (finVectorToZMod a) (-(ZMod.finEquiv n k)) := by
  rw [ZMod.dft_apply]
  rw [← (ZMod.finEquiv n).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (ZMod.finEquiv n).toEquiv j = (j.1 : ZMod n) :=
    finEquiv_eq_natCast j
  have hk : ZMod.finEquiv n k = (k.1 : ZMod n) :=
    finEquiv_eq_natCast k
  have hjback : (ZMod.finEquiv n).symm (j.1 : ZMod n) = j := by
    rw [← hj]
    exact Equiv.symm_apply_apply _ j
  rw [hj, hk]
  simp only [finVectorToZMod, neg_neg, mul_neg, neg_neg, smul_eq_mul]
  rw [principalRoot_pow_eq_stdAddChar]
  rw [hjback]
  simpa only [Nat.cast_mul] using
    (mul_comm (a j)
      (ZMod.stdAddChar ((j.1 * k.1 : Nat) : ZMod n)))

end Chapter30
end CLRS
