import CLRSLean.FourthEdition.Chapter_30.Section_30_1_Representing_Polynomials.S1_CoefficientVectors
import CLRSLean.FourthEdition.Chapter_30.Section_30_1_Representing_Polynomials.S2_PointValueInterpolation
import CLRSLean.FourthEdition.Chapter_30.Section_30_1_Representing_Polynomials.S3_RepresentationOperations

/-! # Section 30.1 - Representing Polynomials

Fixed-capacity coefficient vectors are connected to `Polynomial` by exact
round trips, and `hornerEval_correct` verifies their canonical Horner
execution.  Distinct point-value samples determine bounded-degree
polynomials through `interpolate_pointValues_roundTrip`.  Vector addition,
pointwise multiplication, and the explicit pair-traversing schoolbook
execution have representation theorems and execution-attached exact costs.

Roots of unity and Fourier transforms belong to Section 30.2.

Implementation pages:

- [Fixed-capacity coefficient vectors](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S1_CoefficientVectors/)
- [Point-value interpolation](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S2_PointValueInterpolation/)
- [Representation operations](CLRSLean/FourthEdition/Chapter_30/Section_30_1_Representing_Polynomials/S3_RepresentationOperations/)
-/

namespace CLRS
namespace Chapter30

end Chapter30
end CLRS
