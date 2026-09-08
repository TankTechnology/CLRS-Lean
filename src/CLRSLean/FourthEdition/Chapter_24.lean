import CLRSLean.Chapter_26
import CLRSLean.FourthEdition.Chapter_24.Section_24_1_Flow_Networks
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.Ford_Fulkerson_Augmentation
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S2_EK_Loop
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S3_WorkAnalysis
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S5_SparseExecution
import CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_24.Section_24_4_Push_Relabel
import CLRSLean.FourthEdition.Chapter_24.Section_24_5_Relabel_To_Front
import CLRSLean.FourthEdition.Chapter_24.Section_24_5_Relabel_To_Front.Execution
import CLRSLean.FourthEdition.Chapter_24.Section_24_6_MaxFlow_MinCut

/-!
# Chapter 24 — Maximum Flow

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 24.1--24.6 are native fourth-edition sections (flow networks, the
Ford–Fulkerson method with the Edmonds-Karp correctness and work-analysis
development, maximum bipartite matching, the push-relabel preflow model and its
operation count, an initialized relabel-to-front execution, and the max-flow min-cut
theorem), imported directly from
[Section 24.1](CLRSLean/FourthEdition/Chapter_24/Section_24_1_Flow_Networks/),
[Section 24.2](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/),
[Section 24.3](CLRSLean/FourthEdition/Chapter_24/Section_24_3_Bipartite_Matching/),
[Section 24.4](CLRSLean/FourthEdition/Chapter_24/Section_24_4_Push_Relabel/),
[Section 24.5](CLRSLean/FourthEdition/Chapter_24/Section_24_5_Relabel_To_Front/),
and
[Section 24.6](CLRSLean/FourthEdition/Chapter_24/Section_24_6_MaxFlow_MinCut/).
Section 24.6 is named after the theorem it proves (Theorem 24.6).  Declarations
retain the legacy `CLRS.Chapter26` namespace during the compatibility period;
the third-edition-numbered imports {lit}`CLRSLean.Chapter_26` and
{lit}`CLRSLean.Chapter_26.Section_26_*` forward to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Ford-Fulkerson Augmentation Foundation](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/Ford_Fulkerson_Augmentation/)
* [Shortest Augmenting Paths](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S1_ShortestAugmentingPath/)
* [The Edmonds-Karp Loop](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S2_EK_Loop/)
* [The O(VE^2) Work Analysis](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S3_WorkAnalysis/)
* [Executable BFS](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S4_ExecutableBFS/)
* [Sparse Counted Edmonds-Karp](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/S5_SparseExecution/)
* [Initialized Relabel-to-Front Execution](CLRSLean/FourthEdition/Chapter_24/Section_24_5_Relabel_To_Front/Execution/)

## Coverage boundary

The native sections prove the flow/cut identities, maximum bipartite matching,
push-relabel invariants, and max-flow min-cut. Two constructed executions now
connect maximum-flow output and work to their own state traces.

{lit}`SparseEK.execute` consumes a duplicate-free list of every positive-capacity
arc, builds forward/reverse support buckets, and uses its counted support BFS
and saved parent chain for each augmentation. It returns a maximum flow with
at most {lit}`2VE` augmentations and work at most {lit}`130VE²` when {lit}`E>0`;
empty support costs at most {lit}`V+2`. Here {lit}`V` includes isolated vertices
and {lit}`E` counts positive-capacity arcs. The proof follows this BFS-selected
timeline; it does not identify it with the older classical-choice sequence.

{lit}`RelabelExecution.initializedFlow` constructs the source-saturated preflow,
heights, excess cache, current-neighbor cursors, and internal-vertex list. Its
actual scan/push/relabel/move controller preserves the list discipline and
terminates at a maximum flow without an input schedule or terminal certificate.
The same trace counts initialization writes, cursor/list visits, minimum scans,
and moved cells. The stated weighted scalar/indexed RAM charge is at most
{lit}`864V³`; the underlying basic-operation count is at most {lit}`9V³`.

These models use exact-real arithmetic and indexed table, dictionary, queue,
and bucket primitives. They exclude persistent-container evaluation/copying,
allocation, and bit complexity; the relabel-to-front execution is not a
mutable-array refinement. Neither execution needs integral capacities.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
