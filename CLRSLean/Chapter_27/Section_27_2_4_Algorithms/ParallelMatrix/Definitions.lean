import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S1_CostModel
import CLRSLean.Chapter_04.Section_04_2_Strassen_Algorithm

/-!
# CLRS Section 27.2 — Parallel Matrix Addition

This module gives the main-text {lit}`P-ADD` algorithm an executable interpretation.
At depth zero it performs one scalar addition.  At each positive depth it runs
the four independent quadrant additions with the deterministic balanced
{name}`CLRS.Chapter27.Costed.par4` tree and reassembles their values in matrix order.

The returned {name}`CLRS.Chapter27.Costed` value simultaneously records the ordinary matrix
sum, total work, and critical-path span of that balanced execution.
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

end Chapter27
end CLRS
