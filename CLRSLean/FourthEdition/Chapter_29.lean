import CLRSLean.Chapter_29
import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms
import CLRSLean.FourthEdition.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs
import CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality

/-!
# Chapter 29 — Linear Programming

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

Sections 29.1--29.3 are native fourth-edition sections (standard and slack
forms, formulating problems as linear programs, and duality), imported
directly from
[Section 29.1](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/),
[Section 29.2](CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs/),
and
[Section 29.3](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/).
The duality development builds on the online simplex machinery (legacy
Section 29.3), and the difference-constraints bridge imports the
fourth-edition single-source-shortest-paths sources (Chapter 22).
Declarations keep their current namespaces; the third-edition-numbered
imports {lit}`CLRSLean.Chapter_29` and
{lit}`CLRSLean.Chapter_29.Section_29_*` forward to these sources.

## Implementation details

The supporting implementation pages remain available outside the main sidebar:

* [Standard-Form Definitions](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Definitions/)
* [Canonical Slack Variables](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/SlackVariables/)
* [Standard/Slack Equivalence](CLRSLean/FourthEdition/Chapter_29/Section_29_1_Standard_And_Slack_Forms/Equivalence/)
* [Finite Network Model](CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs/NetworkFlow/)
* [Shortest Paths as an LP](CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs/ShortestPath/)
* [Maximum Flow as an LP](CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs/MaximumFlow/)
* [Minimum-Cost Flow as an LP](CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs/MinimumCostFlow/)
* [Multicommodity Flow as an LP](CLRSLean/FourthEdition/Chapter_29/Section_29_2_Formulating_Problems_As_Linear_Programs/MulticommodityFlow/)
* [Dual Feasibility](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/Definitions/)
* [Weak Duality](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/WeakDuality/)
* [Primal and Dual Optimality](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/Optimality/)
* [Complementary-Slackness Gap Identity](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/ComplementarySlackness/)
* [Terminal Dual Certificates](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/TerminalCertificate/)
* [Dictionary/Primal Bridge](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/DictionaryBridge/)
* [Strong Duality](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/StrongDuality/)
* [Complementary-Slackness Theorem](CLRSLean/FourthEdition/Chapter_29/Section_29_3_Duality/ComplementarySlacknessTheorem/)

## Coverage boundary

The native sections supply the represented fourth-edition linear-programming
sections (§29.1 formulations and algorithms, §29.2 formulating problems,
§29.3 duality with Theorems 29.8--29.10).  The detailed simplex algorithm
(legacy Section 29.3) and the initial basic feasible solution (legacy
Section 29.5) are retained as supplementary online material (reachable
through {lit}`CLRSLean.OnlineMaterial`).

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
