import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S1_CostModel
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S2_Recurrences
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S3_AllInputBounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge

/-!
# 27.2–27.4. Multithreaded Algorithms (Compatibility)

The historical `2_4` module name is retained for compatibility.  Its main
text now covers §§27.2–27.3: parallel-recurrence definitions and all-input
analysis for P-MATMUL, P-MERGE, and P-MERGE-SORT.  Parallel Strassen remains a
retained §27.4 extension until its later closure split.

## Main results

The imported modules provide an executable value/work/span layer for attaching
costs directly to algorithm results, executable and proved-correct P-ADD and
P-MATMUL algorithms, exact equalities between their recorded costs and their
execution recurrences, monotonicity and adjacent-power sandwiches for all four
matrix costs, power-of-two solutions, and all-input {lit}`Theta` results for
P-ADD and executable P-MATMUL.  The earlier idealized P-MATMUL recurrence
retains its all-input upper bounds.  The imports also provide monotonicity,
adjacent-power sandwiches, and all-input {lit}`Theta` results for P-MERGE,
P-MERGE-SORT, and retained Strassen.  The executable binary lower bound used by
P-MERGE additionally has a complete duplicate-sensitive partition theorem and
logarithmic work/span bounds.

## Deferred work

Executable P-MERGE / P-MERGE-SORT implementations refining these recurrence
models remain deferred.

## Implementation details

* [Costed execution model](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S1_CostModel/)
* [Parallel recurrences](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S2_Recurrences/)
* [All-input bounds](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/S3_AllInputBounds/)
* [Parallel matrix definitions](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Definitions/)
* [Parallel matrix correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Correctness/)
* [Exact execution costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/)
* [Exact cost recurrences](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/Definitions/)
* [Execution cost equalities](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/ExecutionEqualities/)
* [Matrix cost monotonicity](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/Monotonicity/)
* [Power-of-two matrix cost bounds](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/PowerBounds/)
* [All-input matrix asymptotics](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMatrix/Costs/AllInputBounds/)
* [Parallel merge](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/)
* [Parallel merge definitions](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Definitions/)
* [P-MERGE split data](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/MergeSplit/)
* [P-MERGE](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/)
* [Executable P-MERGE](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Definitions/)
* [Parallel merge correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Correctness/)
* [Binary lower bound](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/)
* [Binary lower-bound definitions](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/Definitions/)
* [Binary lower-bound correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/Correctness/)
* [Binary lower-bound costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/Costs/)
-/
