import Mathlib
import CLRSLean.Chapter_26.Section_26_3_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S1_Matching_API
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S2_Alternating_Paths
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S3_Simple_Paths
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S4_Matching_Flow
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S5_Residual_Translation
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S6_Berge_Flow_Method
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution

/-!
# 25.1. Maximum bipartite matching revisited

This section develops the native fourth-edition matching interface of CLRS
§25.1 on top of the flow reduction of §26.3
({name}`CLRS.Chapter26.maxMatching_eq_maxFlow_value`).  The flow development
proves that a maximum matching can be *computed*; this section supplies the
combinatorial characterisation of *when* a matching is maximum: Berge's
augmenting-path lemma.

Main results:

- `Matching.matchedLeft` / `Matching.matchedRight`: matched endpoint sets
- `Matching.IsMaximum`: a matching no other matching exceeds in size
- `IsAugmentingPath`: alternating paths with unmatched endpoints
- `Matching.exists_augment`: an augmenting path yields a matching that is
  larger by one
- `augmentingPath_of_hasAugmentingPath`: a residual augmenting path in the
  §26.3 flow network induces an augmenting path in the graph
- `berge_maximum_iff_no_augmentingPath` (Berge's lemma): a matching is
  maximum iff it admits no augmenting path
- `flowMethod_finds_maximum_matching`: a maximum matching exists and is
  certified by the flow method
- `flowMethod_finds_maximum_matching_with_bfs`: the BFS-selected unit-capacity
  run returns a maximum matching with at most `|V|` augmentations

The textbook adjacency-list `O(VE)` budget is stated arithmetically, but is
not claimed for the current Chapter 24 BFS, whose residual-neighbor operation
enumerates the finite vertex universe.  An instrumented adjacency-list BFS
and path-update erasure theorem remain a separate refinement task.

Notation conventions used in this section:

- `G` : bipartite graph (reused from §26.3)
- `M` : matching (reused from §26.3)
- `p` : vertex list representing an alternating path

## Implementation details

The section is split into the following sub-modules:

* [Matching API Extensions](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S1_Matching_API/)
* [Alternating Paths](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S2_Alternating_Paths/)
* [Simple-Path Extraction](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S3_Simple_Paths/)
* [Matching Flow Residuals](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S4_Matching_Flow/)
* [Residual Reachability Translation](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S5_Residual_Translation/)
* [Berge's Lemma and the Flow Method](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S6_Berge_Flow_Method/)
* [BFS Flow Execution](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/)
-/
