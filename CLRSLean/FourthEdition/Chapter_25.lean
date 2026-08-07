import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching
import CLRSLean.FourthEdition.Chapter_25.Section_25_2_Stable_Marriage

/-!
# Chapter 25 — Matchings in Bipartite Graphs

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 25.1 and 25.2 are native fourth-edition sections.  Section 25.1
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

Section 25.2 (the stable-marriage problem) lives in the `CLRS.Matchings` and
`CLRS.StableMarriage` namespaces, imported through
[Section 25.2](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/);
its sub-modules are:

* [Preference Model](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S1_Preference_Model/)
* [Gale-Shapley Algorithm](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S2_Gale_Shapley/)
* [Optimality](CLRSLean/FourthEdition/Chapter_25/Section_25_2_Stable_Marriage/S3_Optimality/)

## Coverage boundary

Status: partial.  Section 25.1 is formalized (Berge's augmenting-path lemma
and the flow-method certification, built on the §26.3 matching-to-flow
reduction).  Section 25.2 proves Gale-Shapley stability (Theorem 25.5) and
stable-pairing existence; perfectness and man-optimality remain.  Section
25.3 (Hungarian algorithm) is not-started.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
