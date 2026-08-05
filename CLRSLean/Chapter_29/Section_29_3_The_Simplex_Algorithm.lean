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

The remaining Section 29.3 boundary is executable SIMPLEX control flow:
entering/leaving selection, the unbounded outcome, exit optimality, and finite
termination under Bland's rule.

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
-/

namespace CLRS
namespace Chapter29
end Chapter29
end CLRS
