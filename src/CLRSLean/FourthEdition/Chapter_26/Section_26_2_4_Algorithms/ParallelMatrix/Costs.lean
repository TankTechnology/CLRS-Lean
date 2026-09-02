import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.Definitions
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.ExecutionEqualities
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.Monotonicity
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.PowerBounds
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs.AllInputBounds

/-!
# CLRS Section 26.2 — Matrix Execution Cost Analysis

This navigation module groups the exact work/span recurrences for executable
{lit}`P-ADD` and {lit}`P-MATMUL` with the theorems connecting those recurrences
to the costs carried by their {lit}`Costed` results, their power-of-two
solutions, and the all-input asymptotic main theorems.

## Implementation details

* [Cost recurrences](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix/Costs/Definitions/)
* [Execution equalities](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix/Costs/ExecutionEqualities/)
* [Monotonicity and power sandwiches](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix/Costs/Monotonicity/)
* [Power-of-two bounds](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix/Costs/PowerBounds/)
* [All-input bounds](CLRSLean/FourthEdition/Chapter_26/Section_26_2_4_Algorithms/ParallelMatrix/Costs/AllInputBounds/)
-/
