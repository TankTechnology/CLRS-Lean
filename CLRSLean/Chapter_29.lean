import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Definitions
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.SlackVariables
import CLRSLean.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Equivalence
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.Definitions
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.Semantics
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.BasicSolution
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary.InitialDictionary
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Definitions
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Algebra
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.SumLemmas
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.SemanticEquivalence
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Feasibility
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot.Objective
import CLRSLean.Chapter_29.Section_29_4_Duality
import CLRSLean.Chapter_29.Section_29_4_Duality.Definitions
import CLRSLean.Chapter_29.Section_29_4_Duality.WeakDuality

/-!
# Chapter 29 - Linear Programming

Chapter 29 develops linear-programming representations, SIMPLEX, and duality.
The current milestone represents standard/slack feasibility, the textbook
dictionary and PIVOT layer, and weak duality.

## Represented sections

* 29.1 Standard and slack forms: standard-form definitions and the
  slack-variable feasibility bridge.
* 29.3 The simplex algorithm: fixed-slot dictionaries with variable-label
  exchange, basic solutions, the initial dictionary, the PIVOT formulas,
  semantic equivalence, minimum-ratio feasibility, and objective progress.
* 29.4 Duality: dual feasibility and weak duality.

## Current gaps

Sections 29.2 and 29.5 are not represented.  Section 29.3 still needs
executable SIMPLEX control flow, unboundedness, Bland-rule termination, and
exit optimality.  Section 29.4 currently contains weak duality only; strong
duality and complementary slackness remain explicit gaps.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
