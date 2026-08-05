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
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.VariableOrder
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Entering
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Leaving
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Step
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Optimality
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Unboundedness
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Equivalence
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Run
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Pivot
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Reachability
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Trace
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.Coefficients
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Bland.NoCycle
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex.Termination
import CLRSLean.Chapter_29.Section_29_4_Duality
import CLRSLean.Chapter_29.Section_29_4_Duality.Definitions
import CLRSLean.Chapter_29.Section_29_4_Duality.WeakDuality
import CLRSLean.Chapter_29.Section_29_4_Duality.Optimality
import CLRSLean.Chapter_29.Section_29_4_Duality.ComplementarySlackness
import CLRSLean.Chapter_29.Section_29_4_Duality.TerminalCertificate
import CLRSLean.Chapter_29.Section_29_4_Duality.DictionaryBridge
import CLRSLean.Chapter_29.Section_29_4_Duality.StrongDuality
import CLRSLean.Chapter_29.Section_29_4_Duality.ComplementarySlacknessTheorem

/-!
# Chapter 29 - Linear Programming

Chapter 29 develops linear-programming representations, SIMPLEX, and duality.
The current milestone represents standard/slack feasibility, the complete
basic-feasible SIMPLEX algorithm, and weak duality.

## Represented sections

* 29.1 Standard and slack forms: standard-form definitions and the
  slack-variable feasibility bridge.
* 29.3 The simplex algorithm: fixed-slot dictionaries with variable-label
  exchange, basic solutions, the initial dictionary, the PIVOT formulas,
  semantic equivalence, Bland entering/leaving selection, optimal and
  unbounded exits, the textbook anti-cycling proof, and finite termination.
* 29.4 Duality: dual feasibility and weak duality.

## Current gaps

Sections 29.2 and 29.5 are not represented.  Section 29.4 currently contains
weak duality only; strong duality and complementary slackness remain explicit
gaps.  Section 29.5 will supply a basic-feasible dictionary before invoking
the completed Section 29.3 SIMPLEX core.
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
