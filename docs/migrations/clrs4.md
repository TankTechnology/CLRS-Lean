# Migrating to the CLRS fourth-edition module tree

CLRS-Lean now uses `CLRSLean.FourthEdition.Chapter_NN` as its canonical chapter
guide imports. The existing `CLRSLean.Chapter_NN` modules retain their
third-edition meanings throughout the compatibility period. In particular,
`CLRSLean.Chapter_19` still means Fibonacci heaps; fourth-edition Chapter 19,
data structures for disjoint sets, is imported as
`CLRSLean.FourthEdition.Chapter_19`.

## Import examples

New code should import the fourth-edition facade:

```lean
import CLRSLean.FourthEdition.Chapter_19

#check CLRS.Chapter21.Forest.singletonForest
```

The declaration remains in its legacy namespace while the facade imports the
existing theorem-bearing source. Code that uses a third-edition-numbered import
continues to compile:

```lean
import CLRSLean.Chapter_21

#check CLRS.Chapter21.Forest.singletonForest
```

For content outside the fourth-edition main chapter tree, use the umbrella
import:

```lean
import CLRSLean.OnlineMaterial

#check CLRS.Chapter19.FH.extractMin_correct
#check CLRS.Chapter20.VEBTreeMM.delete_correct
```

## Chapter mapping during the facade period

| Fourth-edition guide | Current theorem-bearing source | Migration note |
| --- | --- | --- |
| Chapters 1--13 | `CLRSLean.Chapter_01`--`CLRSLean.Chapter_13` | Same chapter number; section differences are recorded in the edition map. |
| Chapter 14, Dynamic Programming | `CLRSLean.Chapter_15` | Shifted facade. |
| Chapter 15, Greedy Algorithms | `CLRSLean.FourthEdition.Chapter_15` (native §15.1--15.4) | Sections 15.1--15.4 use native fourth-edition sources. Textbook-facing companions provide the iterative activity selector and exact scan count, the activity instance of the generic greedy theorem, Huffman equation (15.4), named Lemma 15.2/15.3 interfaces, honest list/heap cost layers, and literal-empty-start offline-cache optimality. Legacy `CLRSLean.Chapter_16.Section_16_1..3_*` forward to the first three core sections. Matroid and task-scheduling material is supplementary online material. |
| Chapter 16, Amortized Analysis | `CLRSLean.FourthEdition.Chapter_16` (native §16.1--16.4) | Sections 16.1--16.4 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_17.Section_17_*` forward to them. Declarations retain the `CLRS.Chapter17` namespace pending the chapter-by-chapter namespace migration. |
| Chapter 17, Augmenting Data Structures | `CLRSLean.Chapter_14` | Shifted facade. |
| Chapter 18, B-Trees | `CLRSLean.Chapter_18` | Same chapter number. |
| Chapter 19, Data Structures for Disjoint Sets | `CLRSLean.FourthEdition.Chapter_19` (native §19.1--19.4) | Sections 19.1--19.4 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_21.Section_21_*` forward to them. Declarations retain the `CLRS.Chapter21` namespace pending the chapter-by-chapter namespace migration. |
| Chapter 20, Elementary Graph Algorithms | `CLRSLean.FourthEdition.Chapter_20` (native §20.1--20.5) | Sections 20.1--20.5 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_22.Section_22_*` forward to them. Declarations retain the `CLRS.Chapter22` namespace pending the chapter-by-chapter namespace migration. |
| Chapter 21, Minimum Spanning Trees | `CLRSLean.FourthEdition.Chapter_21` (native §21.1--21.2) | Sections 21.1--21.2 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_23.Section_23_*` forward to them. Declarations retain the `CLRS.MST` namespace. |
| Chapter 22, Single-Source Shortest Paths | `CLRSLean.FourthEdition.Chapter_22` (native §22.1--22.5) | Sections 22.1--22.5 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_24.Section_24_*` forward to them. Declarations retain the `CLRS.Chapter24` namespace pending the chapter-by-chapter namespace migration. |
| Chapter 23, All-Pairs Shortest Paths | `CLRSLean.FourthEdition.Chapter_23` (native §23.1--23.3) | Sections 23.1--23.3 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_25.Section_25_*` forward to them. Declarations retain the `CLRS.Chapter24.WeightedGraph` namespace. |
| Chapter 24, Maximum Flow | `CLRSLean.FourthEdition.Chapter_24` (native §24.1--24.3, 24.6) | Sections 24.1--24.3 and 24.6 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_26.Section_26_*` forward to them. Declarations retain the `CLRS.Chapter26` namespace. |
| Chapter 25, Matchings in Bipartite Graphs | `CLRSLean.FourthEdition.Chapter_25` (native §25.1--25.3) | Sections 25.1--25.3 migrated to native fourth-edition sources (maximum bipartite matching, stable marriage, and the Hungarian algorithm). |
| Chapter 26, Parallel Algorithms | `CLRSLean.FourthEdition.Chapter_26` (native §26.1--26.3) | Sections 26.1--26.3 migrated to native fourth-edition sources; legacy `CLRSLean.Chapter_27.Section_27_*` forward to them. Declarations retain the `CLRS.Chapter27` namespace. |
| Chapter 27, Online Algorithms | `CLRSLean.FourthEdition.Chapter_27` (native §27.1--27.3) | Sections 27.1--27.3 migrated to native fourth-edition sources (waiting-for-the-elevator lower bound, maintaining a search tree, and online caching). |
| Chapters 28--32 | `CLRSLean.FourthEdition.Chapter_28`--`CLRSLean.FourthEdition.Chapter_32` (native, same section numbers) | Same chapter number with explicit section-level differences; the legacy `CLRSLean.Chapter_NN.Section_*` files forward to the fourth-edition sources during the compatibility period. |
| Chapter 33, Machine-Learning Algorithms | `CLRSLean.FourthEdition.Chapter_33` (native §33.1--33.3) | Sections 33.1--33.3 migrated to native fourth-edition sources (clustering, multiplicative weights, and gradient descent). |
| Chapter 34, NP-Completeness | `CLRSLean.Chapter_34` (facade §34.1--34.3, represented §§34.4--34.5) | Sections 34.1--34.3 reuse the legacy source through a compatibility facade; §34.4 includes the concrete Cook--Levin reduction, `GeneralCircuitSAT` NP-completeness, a concrete GeneralCircuitSAT-to-SAT machine, and the resulting full hardness chain to an honest general graph-plus-`k` `CLIQUE`, which is NP-complete. §34.5 closes the selected typed and strict serialized reductions through VERTEX-COVER, HAM-CYCLE, decision-TSP, and SUBSET-SUM, including fixed polynomial-time reduction/verifier machines and the public theorems `VERTEXCOVER_npComplete`, `HAMCYCLE_npComplete`, `TSP_npComplete`, and `SUBSETSUM_npComplete`. |
| Chapter 35, Approximation Algorithms | `CLRSLean.FourthEdition.Chapter_35` (native §35.1--35.5) | Sections 35.1--35.5 migrated to native fourth-edition sources. |

The authoritative section-level mapping is
[`docs/clrs-fourth-edition-map.csv`](../clrs-fourth-edition-map.csv). Facades do
not rename declarations: namespaces migrate chapter by chapter, and the map
identifies the source namespace to use until each migration lands.

Remaining facade-to-native migrations are optional follow-up work and should be
tracked as GitHub issues.  The CSV map above remains the authoritative current
state.

## Online and supplementary mapping

| Retained material | Compatibility import |
| --- | --- |
| Third-edition Chapter 19, Fibonacci heaps | `CLRSLean.Chapter_19` |
| Third-edition Chapter 20, van Emde Boas trees | `CLRSLean.Chapter_20` |
| Third-edition Chapter 33, computational geometry | `CLRSLean.Chapter_33` |
| Third-edition Section 4.1, maximum subarray | `CLRSLean.Chapter_04.Section_04_1_Maximum_Subarray` |
| Third-edition Section 11.5, perfect hashing | `CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing` |
| Third-edition Section 16.4, matroids | `CLRSLean.Chapter_16.Section_16_4_Matroids` |
| Third-edition Section 16.5, task scheduling | `CLRSLean.Chapter_16.Section_16_5_Task_Scheduling` |
| Third-edition Section 29.3, the simplex algorithm | `CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm` |
| Third-edition Section 29.5, the initial basic feasible solution | `CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution` |
| Third-edition Section 30.3, bit reversal | `CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.BitReversal` |
| Third-edition Section 30.3, iterative FFT | `CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT` |
| Third-edition Section 31.9, integer factorization | `CLRSLean.Chapter_31.Section_31_9_Integer_Factorization` |

All entries in this table are also available through
`import CLRSLean.OnlineMaterial`. The old imports remain supported during the
compatibility period; the umbrella is the stable discovery point for new code.
The authoritative topic-level counts are in
[`docs/clrs-online-material.csv`](../clrs-online-material.csv); they are
disjoint from the canonical chapter counts in `clrs-proof-progress.csv`.
Fourth-edition FFT-circuit results remain canonical Chapter 30 content and are
therefore intentionally absent from the online-material umbrella.

## Compatibility and deprecation policy

The compatibility guarantee is conjunctive:

1. Every existing `CLRSLean.Chapter_*` import and its public declarations is
   preserved through **all `1.x` releases**.
2. Those imports are preserved for **at least six calendar months after the
   first published release containing the fourth-edition facades**. The
   six-month clock starts on that release's publication date, not on the date
   of this document.
3. No legacy import may be removed before a **`2.0` or later** release. If a
   `2.0` release occurs before the six-month minimum expires, removal waits for
   a later eligible release.

Passing the version and time gates is necessary but not sufficient. Before an
individual legacy import prefix can be removed, all of these migration gates
must also pass:

- its fourth-edition source and declaration-namespace migration is complete,
  or retained supplementary content has a stable content-named replacement;
- the last `1.x` release still passes the legacy-import compatibility tests;
- this guide and the cleanup release notes list the exact removed prefix and
  its replacement import and declaration namespace; and
- no theorem-bearing online material becomes unreachable through a supported
  named import.

Deprecation during `1.x` is documentation-only: the project does not add mass
deprecation warnings to existing declarations. At the eligible cleanup major
release, unqualified `CLRSLean.Chapter_NN` imports may adopt fourth-edition
meanings. `CLRSLean.FourthEdition.Chapter_NN` then becomes a forwarding path
and may itself be removed only in a later major release with its own notice.
