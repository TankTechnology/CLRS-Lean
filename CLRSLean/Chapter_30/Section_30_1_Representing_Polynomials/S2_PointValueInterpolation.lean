import CLRSLean.Chapter_30.Section_30_1_Representing_Polynomials.S1_CoefficientVectors
import Mathlib.LinearAlgebra.Lagrange

/-! # Chapter 30.1: Point-value interpolation

Point-value vectors are connected to Mathlib's Lagrange interpolant.  The
public theorems keep the distinct-node and degree-capacity premises explicit.
-/

namespace CLRS
namespace Chapter30

open Polynomial

/-- Evaluate a polynomial at every node in a fixed vector. -/
def pointValues [Semiring K] {n : Nat} (points : Fin n → K) (p : K[X]) :
    CoeffVector K n :=
  fun i => p.eval (points i)

/-- The Lagrange interpolant through a fixed vector of nodes and values. -/
noncomputable def interpolateVector [Field K] {n : Nat}
    (points values : Fin n → K) : K[X] :=
  Lagrange.interpolate Finset.univ points values

/-- Two degree-bounded polynomials agreeing at distinct nodes are equal. -/
theorem pointValues_injective [Field K] {n : Nat}
    {points : Fin n → K} (hpoints : Function.Injective points)
    {p q : K[X]} (hp : p.degree < n) (hq : q.degree < n)
    (hvalues : pointValues points p = pointValues points q) : p = q := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ
      hpoints.injOn
  · simpa using hp
  · simpa using hq
  · intro i _
    exact congrFun hvalues i

/-- The Lagrange interpolant assumes its prescribed value at every distinct
sample node. -/
theorem interpolate_pointValues [Field K] {n : Nat}
    {points values : Fin n → K} (hpoints : Function.Injective points)
    (i : Fin n) :
    (interpolateVector points values).eval (points i) = values i := by
  exact Lagrange.eval_interpolate_at_node values hpoints.injOn (by simp)

/-- Every Lagrange basis divisor has natural degree at most one. -/
private theorem basisDivisor_natDegree_le_one [Field K] (x y : K) :
    (Lagrange.basisDivisor x y).natDegree ≤ 1 := by
  by_cases hxy : x = y
  · simp [hxy, Lagrange.basisDivisor_self]
  · simp [Lagrange.natDegree_basisDivisor_of_ne hxy]

/-- A Lagrange basis polynomial has natural degree at most the number of
factors in its defining product. -/
private theorem lagrangeBasis_natDegree_le [Field K] {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (points : ι → K) (i : ι) :
    (Lagrange.basis s points i).natDegree ≤ (s.erase i).card := by
  rw [Lagrange.basis]
  calc
    (∏ j ∈ s.erase i, Lagrange.basisDivisor (points i) (points j)).natDegree
        ≤ ∑ j ∈ s.erase i,
            (Lagrange.basisDivisor (points i) (points j)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ s.erase i, 1 := by
      exact Finset.sum_le_sum fun j _ =>
        basisDivisor_natDegree_le_one (points i) (points j)
    _ = (s.erase i).card := by simp

/-- The interpolant always fits in the declared node capacity, independently
of whether the nodes are distinct. -/
theorem interpolateVector_degree_lt [Field K] {n : Nat}
    (points values : Fin n → K) :
    (interpolateVector points values).degree < n := by
  cases n with
  | zero =>
      simp [interpolateVector, Lagrange.interpolate_empty]
  | succ n =>
      have hnat : (interpolateVector points values).natDegree ≤ n := by
        rw [interpolateVector, Lagrange.interpolate_apply]
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro i hi
        calc
          (Polynomial.C (values i) *
              Lagrange.basis Finset.univ points i).natDegree
              ≤ (Polynomial.C (values i)).natDegree +
                  (Lagrange.basis Finset.univ points i).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ 0 + (Finset.univ.erase i).card := by
            gcongr
            · simp
            · exact lagrangeBasis_natDegree_le Finset.univ points i
          _ = n := by
            rw [Finset.card_erase_of_mem hi]
            simp
      calc
        (interpolateVector points values).degree ≤
            ((interpolateVector points values).natDegree : WithBot Nat) :=
          Polynomial.degree_le_natDegree
        _ ≤ (n : WithBot Nat) := by exact_mod_cast hnat
        _ < ((n + 1 : Nat) : WithBot Nat) := by exact_mod_cast Nat.lt_succ_self n

/-- A degree-bounded polynomial with prescribed values is the interpolant. -/
theorem interpolate_unique [Field K] {n : Nat}
    {points values : Fin n → K} (hpoints : Function.Injective points)
    {p : K[X]} (hp : p.degree < n)
    (heval : ∀ i, p.eval (points i) = values i) :
    p = interpolateVector points values := by
  apply pointValues_injective hpoints hp
    (interpolateVector_degree_lt points values)
  funext i
  rw [pointValues, pointValues, heval i, interpolate_pointValues hpoints i]

/-- Interpolating the point values of a fitting polynomial is a round trip. -/
theorem interpolate_pointValues_roundTrip [Field K] {n : Nat}
    {points : Fin n → K} (hpoints : Function.Injective points)
    {p : K[X]} (hp : p.degree < n) :
    interpolateVector points (pointValues points p) = p := by
  exact (interpolate_unique hpoints hp (fun _ => rfl)).symm

end Chapter30
end CLRS
