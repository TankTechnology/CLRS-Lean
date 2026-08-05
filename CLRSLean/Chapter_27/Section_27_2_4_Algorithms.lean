import CLRSLean.Chapter_27.Section_27_1_Multithreading_Model
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S1_CostModel
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S2_Recurrences
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.S3_AllInputBounds
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Definitions
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMatrix.Costs
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelStrassen

/-!
# 27.2–27.4. Multithreaded Algorithms (Compatibility)

The historical `2_4` module name is retained for compatibility.  Its main
text now covers §§27.2–27.3: parallel-recurrence definitions and all-input
analysis for P-MATMUL, P-MERGE, and P-MERGE-SORT.  The historical parallel
Strassen names are imported separately from an explicitly labeled Chapter 27
extension.

## Main results

The imported modules provide an executable value/work/span layer for attaching
costs directly to algorithm results, executable and proved-correct P-ADD and
P-MATMUL algorithms, exact equalities between their recorded costs and their
execution recurrences, monotonicity and adjacent-power sandwiches for all four
matrix costs, power-of-two solutions, and all-input {lit}`Theta` results for
P-ADD and executable P-MATMUL.  The earlier idealized P-MATMUL recurrence
retains its all-input upper bounds.  The imports also provide monotonicity,
adjacent-power sandwiches, and all-input {lit}`Theta` results for P-MERGE and
P-MERGE-SORT.  The compatibility extension retains the corresponding Strassen
recurrence results without presenting them as Chapter 27 main text.  The
executable binary lower bound used by P-MERGE additionally has a complete
duplicate-sensitive partition theorem and logarithmic work/span bounds.
{name}`CLRS.Chapter27.MergeSplit` and
{name}`CLRS.Chapter27.pMerge` implement the actual midpoint/binary-search
P-MERGE control structure, and {name}`CLRS.Chapter27.pMerge_correct` proves its
sortedness, permutation, and exact-length specification.  The pointwise
{name}`CLRS.Chapter27.pMerge_work_lower` and
{name}`CLRS.Chapter27.pMerge_work_upper` theorems prove its actual execution
has linear work.  The theorem {name}`CLRS.Chapter27.pMerge_span_upper` proves
the universal quadratic-logarithmic span upper bound, and sorted interleaved
power-of-two inputs attain the matching bound through
{name}`CLRS.Chapter27.pMerge_interleaved_span_lower`.
{name}`CLRS.Chapter27.pMergeSort` executes the textbook midpoint split,
parallel recursive sorting, and sequential P-MERGE phase;
{name}`CLRS.Chapter27.pMergeSort_correct` proves sortedness, permutation, and
exact output length for every input.  The exact step equations
{name}`CLRS.Chapter27.pMergeSort_work_step_eq` and
{name}`CLRS.Chapter27.pMergeSort_span_step_eq` connect its carried costs to the
recursion.  The pointwise pair {name}`CLRS.Chapter27.pMergeSort_work_lower` and
{name}`CLRS.Chapter27.pMergeSort_work_upper` proves executable Θ(n log n) work;
{name}`CLRS.Chapter27.pMergeSort_span_upper` gives the universal cubic-log span
bound, while {name}`CLRS.Chapter27.pMergeSort_worstFamily_span_lower` gives the
matching recursive witness family.

## Completion boundary

The executable P-MERGE-SORT cost gap is closed, and the parallel-Strassen
compatibility extension has been isolated from the main-text recurrence
modules.  No represented Chapter 27 main-text core proof obligation remains.

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
* [P-MERGE correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Correctness/)
* [P-MERGE order boundaries](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Correctness/Boundaries/)
* [P-MERGE permutation](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Correctness/Permutation/)
* [P-MERGE strong-induction proof](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/PMerge/Correctness/Main/)
* [Parallel merge correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Correctness/)
* [P-MERGE costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/)
* [P-MERGE structural bounds](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Structure/)
* [P-MERGE one-step costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Step/)
* [P-MERGE linear work](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Work/)
* [P-MERGE logarithmic work potential](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Work/LogPotential/)
* [P-MERGE pointwise work bounds](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Work/Bounds/)
* [P-MERGE span](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/)
* [P-MERGE span envelope](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/Envelope/)
* [P-MERGE pointwise span bound](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/Bounds/)
* [P-MERGE witness lists](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/WitnessLists/)
* [P-MERGE interleaved lower bound](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/Costs/Span/LowerBound/)
* [P-MERGE-SORT](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/)
* [P-MERGE-SORT definitions](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Definitions/)
* [P-MERGE-SORT correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Correctness/)
* [P-MERGE-SORT specification](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Correctness/Spec/)
* [P-MERGE-SORT strong-induction proof](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Correctness/Main/)
* [P-MERGE-SORT costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/)
* [P-MERGE-SORT one-step costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Step/)
* [P-MERGE-SORT recurrence links](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/RecurrenceLinks/)
* [P-MERGE-SORT work](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Work/)
* [P-MERGE-SORT work bounds](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Work/Bounds/)
* [P-MERGE-SORT span](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/)
* [P-MERGE-SORT span upper bound](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/Bounds/)
* [P-MERGE-SORT span witness input](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/WitnessInput/)
* [P-MERGE-SORT map invariance](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/MapInvariance/)
* [P-MERGE-SORT span lower bound](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMergeSort/Costs/Span/LowerBound/)
* [Parallel-Strassen recurrence extension](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/)
* [Parallel-Strassen recurrence definitions](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/Definitions/)
* [Parallel-Strassen recurrence monotonicity](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/Monotonicity/)
* [Parallel-Strassen all-input bounds](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelStrassen/Recurrences/AllInputBounds/)
* [Binary lower bound](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/)
* [Binary lower-bound definitions](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/Definitions/)
* [Binary lower-bound correctness](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/Correctness/)
* [Binary lower-bound costs](CLRSLean/Chapter_27/Section_27_2_4_Algorithms/ParallelMerge/LowerBound/Costs/)
-/
