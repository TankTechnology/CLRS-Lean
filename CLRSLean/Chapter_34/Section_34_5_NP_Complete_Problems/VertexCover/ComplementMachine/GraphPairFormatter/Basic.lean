import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.WellFormedGuard.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Basic

/-!
# Empty-certificate graph-pair formatter: pure semantics
-/

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GraphPairFormatter

open PolyBuilder
open WellFormedGuard

/-- Reverse, append the existing left-pair separator, then reverse again. -/
def format (input : List CliqueSym) : List (Option CliqueSym) :=
  (OptionPairLeft.format input.reverse).reverse

/-- The three-stage formulation is exactly the empty-certificate pair encoding
expected by the reused CLIQUE graph checks. -/
theorem format_eq_graphPairEncoding (input : List CliqueSym) :
    format input = graphPairEncoding input := by
  simp [format, OptionPairLeft.format, graphPairEncoding, pairEncoding]

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.GraphPairFormatter
