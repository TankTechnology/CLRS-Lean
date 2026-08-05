import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S2_PointValueInterpolation

/-! # Chapter 30.1: Representation operations

This module gives canonical executions for fixed-vector operations.  Its
schoolbook multiplication really traverses every coefficient pair, inserts
the product into one output bucket, and increments the attached counters.
-/

namespace CLRS
namespace Chapter30

open Polynomial

/-- The value and arithmetic counters produced by a fixed-vector operation. -/
structure VectorArithmeticExecution (K : Type*) (n : Nat) where
  /-- The computed vector. -/
  value : CoeffVector K n
  /-- The number of charged additions. -/
  additions : Nat
  /-- The number of charged multiplications. -/
  multiplications : Nat

/-- Total charged arithmetic work of a vector execution. -/
def VectorArithmeticExecution.work (r : VectorArithmeticExecution K n) : Nat :=
  r.additions + r.multiplications

/-- Canonical pointwise vector-addition execution. -/
def vectorAddExec [AddMonoid K] {n : Nat}
    (a b : CoeffVector K n) : VectorArithmeticExecution K n :=
  ⟨fun i => a i + b i, n, 0⟩

/-- The value returned by canonical vector addition. -/
def vectorAdd [AddMonoid K] {n : Nat}
    (a b : CoeffVector K n) : CoeffVector K n :=
  (vectorAddExec a b).value

/-- Canonical pointwise vector-multiplication execution. -/
def pointwiseMulExec [Mul K] {n : Nat}
    (a b : CoeffVector K n) : VectorArithmeticExecution K n :=
  ⟨fun i => a i * b i, 0, n⟩

/-- The value returned by canonical pointwise multiplication. -/
def pointwiseMul [Mul K] {n : Nat}
    (a b : CoeffVector K n) : CoeffVector K n :=
  (pointwiseMulExec a b).value

/-- Vector addition charges exactly one addition per slot. -/
theorem vectorAddWork_exact [AddMonoid K] {n : Nat}
    (a b : CoeffVector K n) :
    (vectorAddExec a b).work = n := by
  simp [vectorAddExec, VectorArithmeticExecution.work]

/-- Pointwise multiplication charges exactly one multiplication per slot. -/
theorem pointwiseMulWork_exact [Mul K] {n : Nat}
    (a b : CoeffVector K n) :
    (pointwiseMulExec a b).work = n := by
  simp [pointwiseMulExec, VectorArithmeticExecution.work]

/-- Vector addition represents polynomial addition. -/
theorem vectorToPolynomial_vectorAdd [CommSemiring K] {n : Nat}
    (a b : CoeffVector K n) :
    vectorToPolynomial (vectorAdd a b) =
      vectorToPolynomial a + vectorToPolynomial b := by
  ext i
  by_cases hi : i < n
  · let j : Fin n := ⟨i, hi⟩
    change (vectorToPolynomial (vectorAdd a b)).coeff j =
      (vectorToPolynomial a + vectorToPolynomial b).coeff j
    rw [Polynomial.coeff_add, vectorToPolynomial_coeff,
      vectorToPolynomial_coeff, vectorToPolynomial_coeff]
    rfl
  · have hge : n ≤ i := Nat.le_of_not_gt hi
    simp [vectorToPolynomial_coeff_eq_zero_of_ge, hge]

/-- Sampling commutes with polynomial addition. -/
theorem pointValues_add [Semiring K] {n : Nat} (points : Fin n → K)
    (p q : K[X]) :
    pointValues points (p + q) =
      vectorAdd (pointValues points p) (pointValues points q) := by
  funext i
  simp [pointValues, vectorAdd, vectorAddExec]

/-- Sampling commutes with polynomial multiplication. -/
theorem pointValues_mul [CommSemiring K] {n : Nat} (points : Fin n → K)
    (p q : K[X]) :
    pointValues points (p * q) =
      pointwiseMul (pointValues points p) (pointValues points q) := by
  funext i
  simp [pointValues, pointwiseMul, pointwiseMulExec]

/-- The output bucket receiving the product of input slots `i` and `j`. -/
def productIndex {m n : Nat} (i : Fin m) (j : Fin n) : Fin (m + n) :=
  ⟨i.1 + j.1, by omega⟩

/-- Add a scalar to one output bucket and leave every other bucket unchanged. -/
def addToBucket [AddMonoid K] {n : Nat} (out : CoeffVector K n)
    (i : Fin n) (v : K) : CoeffVector K n :=
  Function.update out i (out i + v)

/-- A vector supported at exactly one output bucket. -/
def singleBucket [Zero K] {n : Nat} (i : Fin n) (v : K) : CoeffVector K n :=
  fun j => if j = i then v else 0

/-- Updating one bucket is pointwise addition by its singleton vector. -/
theorem addToBucket_eq_vectorAdd_singleBucket [AddMonoid K] {n : Nat}
    (out : CoeffVector K n) (i : Fin n) (v : K) :
    addToBucket out i v = vectorAdd out (singleBucket i v) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [addToBucket, vectorAdd, vectorAddExec, singleBucket]
  · simp [addToBucket, vectorAdd, vectorAddExec, singleBucket, hji]

/-- Reconstructing a singleton bucket gives the corresponding monomial. -/
theorem vectorToPolynomial_singleBucket [Semiring K] {n : Nat}
    (i : Fin n) (v : K) :
    vectorToPolynomial (singleBucket i v) = Polynomial.monomial i.1 v := by
  ext k
  by_cases hk : k < n
  · let j : Fin n := ⟨k, hk⟩
    simpa [singleBucket, j, Polynomial.coeff_monomial, Fin.ext_iff,
      eq_comm] using (vectorToPolynomial_coeff (singleBucket i v) j)
  · have hge : n ≤ k := Nat.le_of_not_gt hk
    have hik : (i : Nat) ≠ k := by omega
    rw [vectorToPolynomial_coeff_eq_zero_of_ge _ hge]
    simp [Polynomial.coeff_monomial, hik]

/-- One bucket insertion adds exactly its corresponding monomial. -/
theorem vectorToPolynomial_addToBucket [CommSemiring K] {n : Nat}
    (out : CoeffVector K n) (i : Fin n) (v : K) :
    vectorToPolynomial (addToBucket out i v) =
      vectorToPolynomial out + Polynomial.monomial i.1 v := by
  rw [addToBucket_eq_vectorAdd_singleBucket,
    vectorToPolynomial_vectorAdd, vectorToPolynomial_singleBucket]

/-- One coefficient-pair step of the schoolbook execution. -/
def schoolbookStep [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n)
    (r : VectorArithmeticExecution K (m + n)) (ij : Fin m × Fin n) :
    VectorArithmeticExecution K (m + n) :=
  ⟨addToBucket r.value (productIndex ij.1 ij.2) (a ij.1 * b ij.2),
    r.additions + 1,
    r.multiplications + 1⟩

/-- Traverse a list of coefficient pairs from an arbitrary execution state. -/
def schoolbookPairsExec [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n)
    (pairs : List (Fin m × Fin n))
    (initial : VectorArithmeticExecution K (m + n)) :
    VectorArithmeticExecution K (m + n) :=
  pairs.foldl (schoolbookStep a b) initial

/-- The zero-valued initial state of schoolbook multiplication. -/
def schoolbookInitial [Semiring K] (m n : Nat) :
    VectorArithmeticExecution K (m + n) :=
  ⟨fun _ => 0, 0, 0⟩

/-- A deterministic list containing every coefficient-index pair exactly
once, in lexicographic row order. -/
def coefficientPairs (m n : Nat) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange n).map fun j => (i, j)

/-- The deterministic pair list enumerates the full Cartesian product. -/
theorem coefficientPairs_toFinset (m n : Nat) :
    (coefficientPairs m n).toFinset =
      (Finset.univ : Finset (Fin m)).product Finset.univ := by
  ext ij
  simp [coefficientPairs]

/-- Summing along the deterministic pair list is the usual nested finite
sum over both index types. -/
private theorem coefficientPairs_sum [AddCommMonoid M] {m n : Nat}
    (f : Fin m → Fin n → M) :
    ((coefficientPairs m n).map fun ij => f ij.1 ij.2).sum =
      ∑ i : Fin m, ∑ j : Fin n, f i j := by
  have hflat (xs : List (Fin m)) :
      (xs.flatMap fun i => (List.finRange n).map fun j => f i j).sum =
        (xs.map fun i => ((List.finRange n).map fun j => f i j).sum).sum := by
    induction xs with
    | nil => simp
    | cons i xs ih => simp [ih]
  have hinner (i : Fin m) :
      ((List.finRange n).map fun j => f i j).sum =
        ∑ j : Fin n, f i j := by
    rw [← List.sum_toFinset _ (List.nodup_finRange n)]
    simp
  rw [coefficientPairs]
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  rw [hflat]
  simp_rw [hinner]
  rw [← List.sum_toFinset _ (List.nodup_finRange m)]
  simp

/-- Canonical schoolbook execution over every coefficient pair exactly once. -/
def schoolbookMulExec [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    VectorArithmeticExecution K (m + n) :=
  schoolbookPairsExec a b (coefficientPairs m n) (schoolbookInitial m n)

/-- The value returned by canonical schoolbook multiplication. -/
def schoolbookMul [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) : CoeffVector K (m + n) :=
  (schoolbookMulExec a b).value

/-- Folding coefficient pairs adds their monomials to the initial polynomial. -/
private theorem schoolbookPairsExec_polynomial [CommSemiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n)
    (pairs : List (Fin m × Fin n))
    (initial : VectorArithmeticExecution K (m + n)) :
    vectorToPolynomial (schoolbookPairsExec a b pairs initial).value =
      vectorToPolynomial initial.value +
        (pairs.map fun ij => Polynomial.monomial (ij.1.1 + ij.2.1)
          (a ij.1 * b ij.2)).sum := by
  induction pairs generalizing initial with
  | nil => simp [schoolbookPairsExec]
  | cons ij pairs ih =>
      simp only [schoolbookPairsExec, List.foldl]
      change vectorToPolynomial
          (schoolbookPairsExec a b pairs (schoolbookStep a b initial ij)).value =
        vectorToPolynomial initial.value +
          (List.map (fun ij => Polynomial.monomial (ij.1.1 + ij.2.1)
            (a ij.1 * b ij.2)) (ij :: pairs)).sum
      rw [ih]
      simp [schoolbookStep, productIndex, vectorToPolynomial_addToBucket,
        add_assoc]

/-- The full pair sum of coefficient monomials is the product of the two
reconstructed input polynomials. -/
private theorem pairMonomialSum_eq [CommSemiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (∑ i : Fin m, ∑ j : Fin n,
      Polynomial.monomial (i.1 + j.1) (a i * b j)) =
      vectorToPolynomial a * vectorToPolynomial b := by
  rw [vectorToPolynomial, vectorToPolynomial]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.monomial_mul_monomial]

/-- Schoolbook multiplication represents the product of the input
polynomials. -/
theorem schoolbookMul_correct [CommSemiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    vectorToPolynomial (schoolbookMul a b) =
      vectorToPolynomial a * vectorToPolynomial b := by
  rw [schoolbookMul, schoolbookMulExec]
  rw [schoolbookPairsExec_polynomial]
  rw [show vectorToPolynomial (schoolbookInitial m n).value = 0 by
    simp [schoolbookInitial, vectorToPolynomial]]
  simp only [zero_add]
  calc
    ((coefficientPairs m n).map fun ij =>
        Polynomial.monomial (ij.1.1 + ij.2.1) (a ij.1 * b ij.2)).sum =
        ∑ i : Fin m, ∑ j : Fin n,
          Polynomial.monomial (i.1 + j.1) (a i * b j) := by
      simpa using (coefficientPairs_sum (m := m) (n := n)
        (fun i j => Polynomial.monomial (i.1 + j.1) (a i * b j)))
    _ = vectorToPolynomial a * vectorToPolynomial b :=
      pairMonomialSum_eq a b

/-- A schoolbook output always fits its declared sum capacity. -/
theorem schoolbookMul_degreeBound [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (vectorToPolynomial (schoolbookMul a b)).degree < m + n :=
  vectorToPolynomial_degree_lt _

/-- Pair folding increments the addition counter once per processed pair. -/
private theorem schoolbookPairsExec_additions [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n)
    (pairs : List (Fin m × Fin n))
    (initial : VectorArithmeticExecution K (m + n)) :
    (schoolbookPairsExec a b pairs initial).additions =
      initial.additions + pairs.length := by
  induction pairs generalizing initial with
  | nil => simp [schoolbookPairsExec]
  | cons ij pairs ih =>
      simp only [schoolbookPairsExec, List.foldl]
      change (schoolbookPairsExec a b pairs
        (schoolbookStep a b initial ij)).additions =
          initial.additions + (ij :: pairs).length
      rw [ih]
      simp [schoolbookStep]
      omega

/-- Pair folding increments the multiplication counter once per pair. -/
private theorem schoolbookPairsExec_multiplications [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n)
    (pairs : List (Fin m × Fin n))
    (initial : VectorArithmeticExecution K (m + n)) :
    (schoolbookPairsExec a b pairs initial).multiplications =
      initial.multiplications + pairs.length := by
  induction pairs generalizing initial with
  | nil => simp [schoolbookPairsExec]
  | cons ij pairs ih =>
      simp only [schoolbookPairsExec, List.foldl]
      change (schoolbookPairsExec a b pairs
        (schoolbookStep a b initial ij)).multiplications =
          initial.multiplications + (ij :: pairs).length
      rw [ih]
      simp [schoolbookStep]
      omega

/-- Schoolbook execution performs exactly one addition per coefficient pair. -/
theorem schoolbookMulExec_additions [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (schoolbookMulExec a b).additions = m * n := by
  rw [schoolbookMulExec, schoolbookPairsExec_additions]
  simp [schoolbookInitial, coefficientPairs]

/-- Schoolbook execution performs exactly one multiplication per coefficient
pair. -/
theorem schoolbookMulExec_multiplications [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (schoolbookMulExec a b).multiplications = m * n := by
  rw [schoolbookMulExec, schoolbookPairsExec_multiplications]
  simp [schoolbookInitial, coefficientPairs]

/-- Schoolbook execution performs exactly twice the number of coefficient
pairs in charged arithmetic work. -/
theorem schoolbookMulWork_exact [Semiring K] {m n : Nat}
    (a : CoeffVector K m) (b : CoeffVector K n) :
    (schoolbookMulExec a b).work = 2 * (m * n) := by
  rw [VectorArithmeticExecution.work, schoolbookMulExec_additions,
    schoolbookMulExec_multiplications]
  omega

end Chapter30
end CLRS
