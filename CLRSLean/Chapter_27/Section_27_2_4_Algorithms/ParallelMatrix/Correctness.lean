import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Definitions

/-!
# CLRS Section 27.2 — Correctness of Parallel Matrix Addition

The balanced execution structure affects only work and span: the value returned
by {lit}`P-ADD` is exactly ordinary matrix addition over any ring, including a
noncommutative one.

Main results:

- Theorem {lit}`pAdd_value`: the executable result value is {lit}`A + B`.
- Theorem {lit}`pAdd_correct`: reader-facing correctness of CLRS {lit}`P-ADD`.
-/

namespace CLRS
namespace Chapter27

universe u

/-- The value computed by {lit}`P-ADD` is ordinary matrix addition. -/
theorem pAdd_value (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) : (pAdd R k A B).value = A + B := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext i j
      change (pAdd R (k + 1) A B).value i j = A i j + B i j
      fin_cases i <;> fin_cases j <;>
        simp [pAdd, ih]

/-- Reader-facing correctness theorem for CLRS {lit}`P-ADD`. -/
theorem pAdd_correct (R : Type u) [Ring R] (k : ℕ)
    (A B : Chapter04.SqMat R k) : (pAdd R k A B).value = A + B :=
  pAdd_value R k A B

end Chapter27
end CLRS
