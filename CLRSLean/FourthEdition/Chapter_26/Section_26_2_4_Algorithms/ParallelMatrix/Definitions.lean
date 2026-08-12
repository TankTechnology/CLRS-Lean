import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S1_CostModel
import CLRSLean.Chapter_04.Section_04_2_Strassen_Algorithm

/-!
# CLRS Section 26.2 — Parallel Matrix Algorithms

This module gives the main-text {lit}`P-ADD` and {lit}`P-MATMUL` algorithms
executable interpretations.  Each positive-depth addition runs four independent
quadrant additions.  Matrix multiplication runs eight independent recursive
products, stores their values in two fresh functional temporary matrices, and
then adds those matrices with {lit}`P-ADD`.

The returned {name}`CLRS.Chapter27.Costed` value simultaneously records the
ordinary result, total work, and critical-path span of the balanced execution.
-/

namespace CLRS
namespace Chapter27

universe u

/--
CLRS {lit}`P-ADD` on a depth-indexed {lit}`2^k × 2^k` square matrix.

The value is the recursively assembled matrix sum.  Each scalar leaf charges
one unit of work and span, while each four-way level uses the fixed balanced
fork/join structure of {name}`Costed.par4`.
-/
def pAdd (R : Type u) [Ring R] :
    ∀ k, Chapter04.SqMat R k → Chapter04.SqMat R k → Costed (Chapter04.SqMat R k)
  | 0, x, y => Costed.charge 1 1 (x + y)
  | k + 1, A, B =>
      Costed.map
        (fun q => !![q.1.1, q.1.2; q.2.1, q.2.2])
        (Costed.par4
          (pAdd R k (A 0 0) (B 0 0))
          (pAdd R k (A 0 1) (B 0 1))
          (pAdd R k (A 1 0) (B 1 0))
          (pAdd R k (A 1 1) (B 1 1)))

/--
CLRS {lit}`P-MATMUL` on a depth-indexed {lit}`2^k × 2^k` square matrix.

At a positive depth the eight recursive products run in one balanced parallel
composition.  The first four and last four results form fresh temporary
matrices, which are then added sequentially.  Because each branch produces an
immutable value, the computation has no concurrent writes or data race.
-/
def pMatMul (R : Type u) [Ring R] :
    ∀ k, Chapter04.SqMat R k → Chapter04.SqMat R k → Costed (Chapter04.SqMat R k)
  | 0, x, y => Costed.charge 1 1 (x * y)
  | k + 1, A, B =>
      Costed.seq
        (Costed.par8
          (pMatMul R k (A 0 0) (B 0 0))
          (pMatMul R k (A 0 0) (B 0 1))
          (pMatMul R k (A 1 0) (B 0 0))
          (pMatMul R k (A 1 0) (B 0 1))
          (pMatMul R k (A 0 1) (B 1 0))
          (pMatMul R k (A 0 1) (B 1 1))
          (pMatMul R k (A 1 1) (B 1 0))
          (pMatMul R k (A 1 1) (B 1 1)))
        (fun q =>
          let C : Chapter04.SqMat R (k + 1) :=
            !![q.1.1.1, q.1.1.2; q.1.2.1, q.1.2.2]
          let T : Chapter04.SqMat R (k + 1) :=
            !![q.2.1.1, q.2.1.2; q.2.2.1, q.2.2.2]
          pAdd R (k + 1) C T)

end Chapter27
end CLRS
