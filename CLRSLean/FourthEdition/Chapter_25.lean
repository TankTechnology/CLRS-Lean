import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching

/-!
# Chapter 25 — Matchings in Bipartite Graphs

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Section 25.1 (maximum bipartite matching revisited) is a native
fourth-edition section: its declarations live in the
`CLRS.Chapter26.Matching` and `CLRS.Matchings` namespaces and are imported
through [Section 25.1](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/).
The section is split into the sub-modules:

* [Matching API Extensions](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S1_Matching_API/)
* [Alternating Paths](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S2_Alternating_Paths/)
* [Simple-Path Extraction](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S3_Simple_Paths/)
* [Matching Flow Residuals](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S4_Matching_Flow/)
* [Residual Reachability Translation](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S5_Residual_Translation/)
* [Berge's Lemma and the Flow Method](CLRSLean/FourthEdition/Chapter_25/Section_25_1_Maximum_Bipartite_Matching/S6_Berge_Flow_Method/)

## Coverage boundary

Status: partial.  Section 25.1 is formalized (Berge's augmenting-path lemma
and the flow-method certification, built on the §26.3 matching-to-flow
reduction).  Sections 25.2 (stable marriage) and 25.3 (Hungarian algorithm)
are not-started.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
