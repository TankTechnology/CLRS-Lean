import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Definitions

/-! # Chapter 30.2: Recursive FFT correctness -/

namespace CLRS
namespace Chapter30

open Polynomial

/-- Interleaved even/odd indices form an equivalence with a successor
power-of-two index. -/
private def radixTwoIndexEquiv (k : Nat) :
    Fin (2 ^ k) × Fin 2 ≃ Fin (2 ^ (k + 1)) :=
  finProdFinEquiv.trans (finCongr (by simp [pow_succ, Nat.mul_comm]))

private theorem radixTwoIndexEquiv_zero {k : Nat} (j : Fin (2 ^ k)) :
    (radixTwoIndexEquiv k (j, (0 : Fin 2))).1 = 2 * j.1 := by
  simp [radixTwoIndexEquiv, finProdFinEquiv, Nat.mul_comm]

private theorem radixTwoIndexEquiv_one {k : Nat} (j : Fin (2 ^ k)) :
    (radixTwoIndexEquiv k (j, (1 : Fin 2))).1 = 2 * j.1 + 1 := by
  simp [radixTwoIndexEquiv, finProdFinEquiv, Nat.mul_comm,
    Nat.add_comm]

private theorem radixTwoIndexEquiv_zero_eq {k : Nat} (j : Fin (2 ^ k)) :
    radixTwoIndexEquiv k (j, (0 : Fin 2)) = evenIndex j := by
  apply Fin.ext
  exact radixTwoIndexEquiv_zero j

private theorem radixTwoIndexEquiv_one_eq {k : Nat} (j : Fin (2 ^ k)) :
    radixTwoIndexEquiv k (j, (1 : Fin 2)) = oddIndex j := by
  apply Fin.ext
  simpa [Nat.add_comm] using radixTwoIndexEquiv_one j

/-- The coefficient polynomial splits into its even and odd parts. -/
theorem polynomial_evenOdd_split [CommRing K] {k : Nat}
    (a : PowTwoVec K (k + 1)) :
    vectorToPolynomial a =
      (vectorToPolynomial (evenCoeffs a)).comp (Polynomial.X ^ 2) +
      Polynomial.X *
        (vectorToPolynomial (oddCoeffs a)).comp (Polynomial.X ^ 2) := by
  classical
  rw [vectorToPolynomial]
  rw [← (radixTwoIndexEquiv k).sum_comp
    (fun i => Polynomial.monomial i.1 (a i))]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp [vectorToPolynomial, Polynomial.monomial_comp,
    Finset.mul_sum, Finset.sum_add_distrib, radixTwoIndexEquiv_zero,
    radixTwoIndexEquiv_one, radixTwoIndexEquiv_zero_eq,
    radixTwoIndexEquiv_one_eq, evenCoeffs, oddCoeffs, evenIndex, oddIndex,
    Polynomial.X_pow_eq_monomial, Polynomial.C_mul_monomial,
    Polynomial.X_mul_monomial, pow_mul, Nat.mul_comm, Nat.add_comm]

private theorem dft_apply_eq_eval [CommSemiring K] {n : Nat}
    (omega : K) (a : CoeffVector K n) (i : Fin n) :
    dft omega a i = (vectorToPolynomial a).eval (omega ^ i.1) := by
  rw [dft_eq_pointValues]
  rfl

private theorem dft_lower_split [CommRing K] {k : Nat}
    (omega : K) (a : PowTwoVec K (k + 1)) (j : Fin (2 ^ k)) :
    dft omega a (lowerHalfIndex j) =
      dft (omega ^ 2) (evenCoeffs a) j +
        omega ^ j.1 * dft (omega ^ 2) (oddCoeffs a) j := by
  rw [dft_apply_eq_eval, lowerHalfIndex_val, polynomial_evenOdd_split]
  rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_comp]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  have hsquare : (omega ^ j.1) ^ 2 = (omega ^ 2) ^ j.1 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hsquare]
  rw [← dft_apply_eq_eval, ← dft_apply_eq_eval]

private theorem dft_upper_split [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ (k + 1)))
    (a : PowTwoVec K (k + 1)) (j : Fin (2 ^ k)) :
    dft omega a (upperHalfIndex j) =
      dft (omega ^ 2) (evenCoeffs a) j -
        omega ^ j.1 * dft (omega ^ 2) (oddCoeffs a) j := by
  have horder : 2 ^ (k + 1) = 2 * 2 ^ k := by
    simp [pow_succ, Nat.mul_comm]
  have hhalf : omega ^ (2 ^ k) = -1 := by
    apply primitiveRoot_half_pow_eq_neg_one (by positivity)
    simpa [horder] using homega
  have hfull : omega ^ (2 ^ (k + 1)) = 1 := homega.pow_eq_one
  have hsquare :
      (omega ^ (2 ^ k + j.1)) ^ 2 = (omega ^ 2) ^ j.1 := by
    calc
      (omega ^ (2 ^ k + j.1)) ^ 2 =
          omega ^ ((2 ^ k + j.1) * 2) :=
            (pow_mul omega (2 ^ k + j.1) 2).symm
      _ = omega ^ (2 ^ (k + 1) + 2 * j.1) := by
            congr 1
            rw [pow_succ]
            omega
      _ = omega ^ (2 ^ (k + 1)) * omega ^ (2 * j.1) := by
            rw [pow_add]
      _ = (omega ^ 2) ^ j.1 := by
            rw [hfull, one_mul]
            rw [pow_mul]
  have hpoint : omega ^ (2 ^ k + j.1) = -(omega ^ j.1) := by
    rw [pow_add, hhalf]
    ring
  rw [dft_apply_eq_eval, upperHalfIndex_val, polynomial_evenOdd_split]
  rw [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_comp]
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [hsquare, hpoint]
  rw [← dft_apply_eq_eval, ← dft_apply_eq_eval]
  ring

private theorem powTwoVec_ext_halves {K : Type*} {k : Nat}
    {f g : PowTwoVec K (k + 1)}
    (hlower : ∀ j : Fin (2 ^ k), f (lowerHalfIndex j) = g (lowerHalfIndex j))
    (hupper : ∀ j : Fin (2 ^ k), f (upperHalfIndex j) = g (upperHalfIndex j)) :
    f = g := by
  funext i
  have h : ∀ t : Fin (2 ^ k + 2 ^ k),
      f ((powTwoSuccEquiv k).symm t) = g ((powTwoSuccEquiv k).symm t) := by
    intro t
    refine Fin.addCases ?_ ?_ t
    · intro j
      exact hlower j
    · intro j
      exact hupper j
  simpa using h (powTwoSuccEquiv k i)

/-- One butterfly layer combines the two half-size DFTs into the full DFT. -/
theorem butterflyLayer_dft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ (k + 1)))
    (a : PowTwoVec K (k + 1)) :
    butterflyLayer omega
        (dft (omega ^ 2) (evenCoeffs a))
        (dft (omega ^ 2) (oddCoeffs a)) =
      dft omega a := by
  apply powTwoVec_ext_halves
  · intro j
    rw [butterflyLayer_lower, dft_lower_split]
  · intro j
    rw [butterflyLayer_upper, dft_upper_split homega]

/-- The actual recursive radix-2 execution computes the generic DFT. -/
theorem recursiveFFT_eq_dft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveFFT omega a = dft omega a := by
  induction k generalizing omega with
  | zero =>
      funext i
      fin_cases i
      simp [recursiveFFT, recursiveFFTExec, dft]
  | succ k ih =>
      have hsquare : IsPrimitiveRoot (omega ^ 2) (2 ^ k) := by
        apply primitiveRoot_square (by positivity)
        simpa [pow_succ, Nat.mul_comm] using homega
      have hchildRoot :
          twiddleChildRoot k omega
              (twiddlePowersAuxExec omega (2 ^ k) 1) = omega ^ 2 := by
        by_cases hk : k = 0
        · subst k
          simp only [twiddleChildRoot, if_pos rfl]
          exact homega.pow_eq_one.symm
        · exact twiddleChildRoot_eq_square (Nat.pos_of_ne_zero hk) omega
      simp only [recursiveFFT, recursiveFFTExec]
      rw [hchildRoot]
      change butterflyLayer omega
          (recursiveFFT (omega ^ 2) (evenCoeffs a))
          (recursiveFFT (omega ^ 2) (oddCoeffs a)) = dft omega a
      rw [ih hsquare, ih hsquare]
      exact butterflyLayer_dft homega a

/-- The recursive inverse agrees with the algebraic inverse DFT. -/
theorem recursiveIFFT_eq_idft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveIFFT omega a = idft omega a := by
  funext i
  simp [recursiveIFFT, idft,
    recursiveFFT_eq_dft (primitiveRoot_inv homega)]

/-- Recursive inverse after recursive forward transform is the identity. -/
theorem recursiveIFFT_recursiveFFT [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveIFFT omega (recursiveFFT omega a) = a := by
  rw [recursiveIFFT_eq_idft homega, recursiveFFT_eq_dft homega,
    idft_dft (by positivity) homega]

/-- Recursive forward transform after recursive inverse is the identity. -/
theorem recursiveFFT_recursiveIFFT [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    recursiveFFT omega (recursiveIFFT omega a) = a := by
  rw [recursiveFFT_eq_dft homega, recursiveIFFT_eq_idft homega,
    dft_idft (by positivity) homega]

end Chapter30
end CLRS
