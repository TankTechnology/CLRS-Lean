import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.VariableOrder
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Entering
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Leaving
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Step
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Optimality
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Unboundedness
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Equivalence
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Run
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Pivot

/-!
# 29.3 SIMPLEX

This reader module groups the Bland-rule selectors, the three-way SIMPLEX
step, terminal correctness, and finite-termination proof.  The implementation
is split into small theorem-role modules.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
