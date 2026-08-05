import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Dictionary
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Pivot
import CLRSLean.Chapter_29.Section_29_3_The_Simplex_Algorithm.Simplex

/-!
# 29.3 The simplex algorithm

This milestone formalizes the algebraic core of the textbook simplex method.
A dictionary has fixed row and column slots together with an equivalence that
records which original variables are currently basic and nonbasic.  Its basic
assignment satisfies the dictionary equations, and the initial dictionary is
proved to represent the standard-form constraints and objective from Section
29.1.

The PIVOT operation exchanges one leaving and one entering label and implements
the textbook row, constraint, and objective formulas.  The proofs show that it
preserves exactly the represented assignments and objective expression.  For a
basic-feasible dictionary, the minimum-ratio choice preserves basic feasibility;
a positive reduced cost makes the basic objective value nondecreasing, and the
increase is strict for a positive leaving value.

The functional control layer implements Bland's stable variable order and
deterministic entering/leaving selectors.  Each step returns a certified
optimal, unbounded, or pivot outcome.  Optimality follows from nonpositive
reduced costs; unboundedness follows from the explicit entering ray.

The anti-cycling proof follows the textbook greatest-fickle-variable argument:
equivalent equal-basis endpoints force degenerate pivots, comparison of two
objective expressions yields a negative coefficient-row product, and the
resulting smaller-index minimum-ratio row contradicts Bland's leaving rule.
Consequently the public
{name (full := CLRS.Chapter29.Dictionary.simplex)}`Dictionary.simplex` exhausts
no fuel and returns
either an optimal assignment or an unboundedness certificate for every
basic-feasible dictionary.

## Implementation details

The proof is split into small pages that remain available outside the main
sidebar:

* [Dictionary layer](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/)
* [Dictionary definitions](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Definitions/)
* [Dictionary semantics](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/Semantics/)
* [Basic solutions](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/BasicSolution/)
* [Initial dictionary](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Dictionary/InitialDictionary/)
* [PIVOT layer](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/)
* [PIVOT definitions](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Definitions/)
* [PIVOT formulas](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Algebra/)
* [Finite-sum algebra](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/SumLemmas/)
* [PIVOT semantic equivalence](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/SemanticEquivalence/)
* [Minimum-ratio feasibility](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Feasibility/)
* [Objective progress](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Pivot/Objective/)
* [SIMPLEX control](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/)
* [Stable variable order](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/VariableOrder/)
* [Bland entering selection](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Entering/)
* [Bland leaving selection](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Leaving/)
* [Three-way SIMPLEX step](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Step/)
* [Optimal exit](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Optimality/)
* [Unbounded ray](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Unboundedness/)
* [Dictionary equivalence](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Equivalence/)
* [Fuelled runs](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Run/)
* [Bland anti-cycling layer](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Bland/)
* [Certified Bland pivots](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Bland/Pivot/)
* [Bland reachability](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Bland/Reachability/)
* [Fickle-variable traces](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Bland/Trace/)
* [Objective coefficient comparison](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Bland/Coefficients/)
* [Bland no-cycling theorem](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Bland/NoCycle/)
* [Finite termination and public SIMPLEX](CLRSLean/Chapter_29/Section_29_3_The_Simplex_Algorithm/Simplex/Termination/)
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
