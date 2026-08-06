import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Tactic

/-! # Chapter 30.1: Fixed-capacity coefficient vectors

This module establishes the representation boundary between mathematical
polynomials and the total fixed-capacity vectors used by Chapter 30's
algorithms.
-/

namespace CLRS
namespace Chapter30

open Polynomial

/-- A total coefficient vector with fixed capacity `n`. -/
abbrev CoeffVector (K : Type*) (n : Nat) := Fin n → K

/-- A coefficient vector whose capacity is a power of two. -/
abbrev PowTwoVec (K : Type*) (k : Nat) := CoeffVector K (2 ^ k)

/-- Read and zero-pad the first `n` coefficients of a polynomial. -/
def coeffVector [Semiring K] (n : Nat) (p : K[X]) : CoeffVector K n :=
  fun i => p.coeff i

/-- Reconstruct a polynomial from every slot of a fixed coefficient vector. -/
noncomputable def vectorToPolynomial [Semiring K] {n : Nat}
    (a : CoeffVector K n) : K[X] :=
  ∑ i : Fin n, Polynomial.monomial i.1 (a i)

/-- Reconstruction preserves every coefficient whose index is in range. -/
theorem vectorToPolynomial_coeff [Semiring K] {n : Nat}
    (a : CoeffVector K n) (i : Fin n) :
    (vectorToPolynomial a).coeff i = a i := by
  classical
  change (Polynomial.lcoeff K i)
      (∑ j : Fin n, Polynomial.monomial j.1 (a j)) = a i
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [if_neg]
    exact fun hval => hji (Fin.ext hval)
  · simp

/-- Reading the coefficients of a reconstructed vector returns that vector. -/
theorem coeffVector_vectorToPolynomial [Semiring K] {n : Nat}
    (a : CoeffVector K n) :
    coeffVector n (vectorToPolynomial a) = a := by
  funext i
  exact vectorToPolynomial_coeff a i

/-- A reconstructed vector has no coefficient at or beyond its capacity. -/
theorem vectorToPolynomial_coeff_eq_zero_of_ge [Semiring K] {n i : Nat}
    (a : CoeffVector K n) (hi : n ≤ i) :
    (vectorToPolynomial a).coeff i = 0 := by
  classical
  have hne : ∀ j : Fin n, (j : Nat) ≠ i := by
    intro j hji
    omega
  simp [vectorToPolynomial, Polynomial.coeff_monomial, hne]

/-- The degree of a reconstructed vector is strictly below its capacity. -/
theorem vectorToPolynomial_degree_lt [Semiring K] {n : Nat}
    (a : CoeffVector K n) :
    (vectorToPolynomial a).degree < n := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  exact vectorToPolynomial_coeff_eq_zero_of_ge a hi

/-- Reconstruction after truncation is exact when the polynomial fits. -/
theorem vectorToPolynomial_coeffVector [Semiring K] {n : Nat} (p : K[X])
    (hp : p.degree < n) :
    vectorToPolynomial (coeffVector n p) = p := by
  ext i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    simpa [coeffVector, j] using
      (vectorToPolynomial_coeff (coeffVector n p) j)
  · rw [vectorToPolynomial_coeff_eq_zero_of_ge]
    · exact ((Polynomial.degree_lt_iff_coeff_zero p n).mp hp) i
        (Nat.le_of_not_gt hi) |>.symm
    · exact Nat.le_of_not_gt hi

/-- Remove the constant slot from a nonempty low-coefficient-first vector. -/
def tailCoeffs {K : Type*} {n : Nat} (a : CoeffVector K (n + 1)) :
    CoeffVector K n :=
  fun i => a i.succ

/-- The value and arithmetic counters produced by a scalar computation. -/
structure ArithmeticExecution (K : Type*) where
  /-- The computed scalar. -/
  value : K
  /-- The number of charged additions. -/
  additions : Nat
  /-- The number of charged multiplications. -/
  multiplications : Nat

/-- Total charged arithmetic work of a scalar execution. -/
def ArithmeticExecution.work (r : ArithmeticExecution K) : Nat :=
  r.additions + r.multiplications

/-- Canonical Horner execution on a low-coefficient-first vector. -/
def hornerEvalExec [Semiring K] :
    {n : Nat} → CoeffVector K n → K → ArithmeticExecution K
  | 0, _, _ => ⟨0, 0, 0⟩
  | n + 1, a, x =>
      let child := hornerEvalExec (tailCoeffs a) x
      ⟨a 0 + x * child.value,
        child.additions + 1,
        child.multiplications + 1⟩

/-- The value returned by the canonical Horner execution. -/
def hornerEval [Semiring K] {n : Nat} (a : CoeffVector K n) (x : K) : K :=
  (hornerEvalExec a x).value

/-- Reconstructing a nonempty vector splits into its constant term and shifted
tail polynomial. -/
theorem vectorToPolynomial_succ [CommSemiring K] {n : Nat}
    (a : CoeffVector K (n + 1)) :
    vectorToPolynomial a = Polynomial.monomial 0 (a 0) +
      Polynomial.X * vectorToPolynomial (tailCoeffs a) := by
  simp [vectorToPolynomial, tailCoeffs, Fin.sum_univ_succ, Finset.mul_sum,
    Polynomial.X, Polynomial.monomial_mul_monomial, Nat.add_comm]

/-- Evaluation of a nonempty coefficient vector splits into its constant term
and the shifted tail. -/
theorem vectorToPolynomial_eval_succ [CommSemiring K] {n : Nat}
    (a : CoeffVector K (n + 1)) (x : K) :
    (vectorToPolynomial a).eval x =
      a 0 + x * (vectorToPolynomial (tailCoeffs a)).eval x := by
  rw [vectorToPolynomial_succ]
  simp

/-- Horner execution evaluates the polynomial represented by its input. -/
theorem hornerEval_correct [CommSemiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) :
    hornerEval a x = (vectorToPolynomial a).eval x := by
  induction n with
  | zero => simp [hornerEval, hornerEvalExec, vectorToPolynomial]
  | succ n ih =>
      simp only [hornerEval, hornerEvalExec]
      change a 0 + x * hornerEval (tailCoeffs a) x =
        (vectorToPolynomial a).eval x
      rw [ih (tailCoeffs a)]
      exact (vectorToPolynomial_eval_succ a x).symm

/-- Horner execution charges exactly one addition per input slot. -/
theorem hornerEvalExec_additions [Semiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) :
    (hornerEvalExec a x).additions = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [hornerEvalExec]
      rw [ih (tailCoeffs a)]

/-- Horner execution charges exactly one multiplication per input slot. -/
theorem hornerEvalExec_multiplications [Semiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) :
    (hornerEvalExec a x).multiplications = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [hornerEvalExec]
      rw [ih (tailCoeffs a)]

/-- Horner execution performs exactly twice the vector capacity in charged
arithmetic operations. -/
theorem hornerEvalWork_exact [Semiring K] {n : Nat}
    (a : CoeffVector K n) (x : K) :
    (hornerEvalExec a x).work = 2 * n := by
  rw [ArithmeticExecution.work, hornerEvalExec_additions,
    hornerEvalExec_multiplications]
  omega

end Chapter30
end CLRS
