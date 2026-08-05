import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.ArtificialLP
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.InitialPivot
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.PhaseOne
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.LockVariable
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.RestoreObjective
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.PhaseTwoStart
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.PhaseTwoBridge
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.InitializedSimplex
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.DualProjection
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.GeneralStrongDuality

/-!
# 29.5 The initial basic feasible solution

This section formalizes the textbook phase-I auxiliary program and the
initialized SIMPLEX procedure.  The textbook deletes the artificial variable
before phase II; the fixed-dimension dictionary model instead adds the
equivalent lock {lit}`x₀ ≤ 0`.  Together with auxiliary nonnegativity this
forces {lit}`x₀ = 0`, preserves exactly the original feasible assignments, and
avoids a dimension-changing tableau operation.

## Implementation details

* [Artificial LP](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/ArtificialLP/)
* [Initial Artificial Pivot](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/InitialPivot/)
* [Phase One](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/PhaseOne/)
* [Locking the Artificial Variable](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/LockVariable/)
* [Restoring the Objective](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/RestoreObjective/)
* [Phase-Two Start](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/PhaseTwoStart/)
* [Phase-Two Semantic Bridge](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/PhaseTwoBridge/)
* [Initialized SIMPLEX](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/InitializedSimplex/)
* [Dual Projection](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/DualProjection/)
* [General Strong Duality](CLRSLean/Chapter_29/Section_29_5_The_Initial_Basic_Feasible_Solution/GeneralStrongDuality/)
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
