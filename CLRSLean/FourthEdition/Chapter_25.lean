import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage
import CLRSLean.FourthEdition.Chapter_25.Section_25_3_Hungarian_Algorithm

/-!
# Chapter 25 — Matchings in Bipartite Graphs

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 25.1, 25.2 and 25.3 are native fourth-edition sections.  Section 25.1
(maximum bipartite matching revisited) lives in the `CLRS.Chapter26.Matching`
and `CLRS.Matchings` namespaces, imported through
[Section 25.1](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/);
its sub-modules are:

* [Matching API Extensions](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S1_Matching_API/)
* [Alternating Paths](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S2_Alternating_Paths/)
* [Simple-Path Extraction](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S3_Simple_Paths/)
* [Matching Flow Residuals](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S4_Matching_Flow/)
* [Residual Reachability Translation](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S5_Residual_Translation/)
* [Berge's Lemma and the Flow Method](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S6_Berge_Flow_Method/)
* [BFS and Attached-Cost Flow Execution](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/FlowExecution/)

Section 25.2 (the stable-marriage problem) lives in the `CLRS.Matchings` and
`CLRS.StableMarriage` namespaces, imported through
[Section 25.2](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/);
its sub-modules are:

* [Preference Model](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S1_Preference_Model/)
* [Gale-Shapley Algorithm](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S2_Gale_Shapley/)
* [Optimality](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S3_Optimality/)

Section 25.3 (the Hungarian algorithm for the assignment problem) lives in the
`CLRS.AssignmentProblem` namespace:
[Section 25.3](CLRSLean/FourthEdition/Chapter_25/Section_25_3_Hungarian_Algorithm/).

## Coverage boundary

Status: complete.  Section 25.1 is formalized (Berge's augmenting-path lemma
and the flow-method certification, built on the §26.3 matching-to-flow
reduction), including the BFS-selected unit-capacity execution, integral
matching refinement at every step, at most `|V|` augmentations, and a separate
support-indexed execution whose counter is attached to adjacency construction,
residual bucket scans, parent-path recovery, graph-path projection, and
concrete matching updates.
The final bound is `O(V_f E_f)` for the constructed unit-capacity network.
Section 25.2 proves Gale-Shapley stability (Theorem 25.5),
stable-pairing existence, perfectness, man-optimality (Theorem 25.6), and
woman-pessimality.  Section 25.3 formalizes the assignment model and Lemma
25.8 (dual optimality via feasible potentials), the alternating tree, the
potential-adjustment step, the augmentation step (a tight edge to a free right
vertex enlarges the matching via Berge), the tree-growth step, and the local
progress theorem; the full adjustment-plus-augmentation loop is packaged as a
terminating recursion (`innerLoop` and `exists_perfect_tight`) whose perfect
tight matching is optimal by Lemma 25.8.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
