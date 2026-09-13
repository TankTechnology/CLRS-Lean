import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S1_CostModel
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S2_Recurrences
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.S3_AllInputBounds
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Definitions
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Correctness
import CLRSLean.FourthEdition.Chapter_26.Section_26_2_4_Algorithms.ParallelMatrix.Costs

/-!
# 26.2. Parallel Matrix Multiplication

This is the canonical fourth-edition reader page for P-MATRIX-MULTIPLY.  It
directly exposes the executable matrix definitions, value-correctness proofs,
and execution-attached work and span analysis imported above.

## Formalized content

The constructors P-ADD and P-MATMUL operate on square matrices of dimension
{lit}`2^k`.  Their correctness theorems identify the returned matrices with
ordinary addition and multiplication.  Exact equalities connect the costs
carried by each execution to the formal work and span recurrences.

The recurrence development proves monotonicity, exact power-of-two solutions,
adjacent-power sandwiches, and all-input {lit}`Theta` bounds for the numerical
extensions.  Those arbitrary-input bounds analyze recurrence functions; they
do not claim an arbitrary-dimension padding and unpadding implementation.

Status: `proved` for the power-of-two executable algorithms and their stated
cost model.
-/
