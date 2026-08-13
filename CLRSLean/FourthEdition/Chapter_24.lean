import CLRSLean.Chapter_26
import CLRSLean.FourthEdition.Chapter_24.Section_24_1_Flow_Networks
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.Ford_Fulkerson_Augmentation
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S1_ShortestAugmentingPath
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S2_EK_Loop
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S3_WorkAnalysis
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS
import CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_24.Section_24_4_Push_Relabel
import CLRSLean.FourthEdition.Chapter_24.Section_24_6_MaxFlow_MinCut

/-!
# Chapter 24 — Maximum Flow

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 24.1--24.4 and 24.6 are native fourth-edition sections (flow
networks, the Ford–Fulkerson method with the Edmonds-Karp correctness and
work-analysis development, maximum bipartite matching, the push-relabel
preflow model, and the max-flow min-cut theorem), imported directly from
[Section 24.1](CLRSLean/FourthEdition/Chapter_24/Section_24_1_Flow_Networks/),
[Section 24.2](CLRSLean/FourthEdition/Chapter_24/Section_24_2_Edmonds_Karp/),
[Section 24.3](CLRSLean/FourthEdition/Chapter_24/Section_24_3_Bipartite_Matching/),
[Section 24.4](CLRSLean/FourthEdition/Chapter_24/Section_24_4_Push_Relabel/),
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

## Coverage boundary

The native sections supply the represented fourth-edition maximum-flow
sections (Lemma 24.5 net-flow/cut value, Lemmas 24.7--24.8 Edmonds-Karp
distance growth, the §24.4 preflow-push model with its height-bound and
correctness theorems, and Theorem 24.6 max-flow min-cut).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
