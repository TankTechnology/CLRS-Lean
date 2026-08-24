import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.GraphPairFormatter
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Raw graph syntax-and-well-formedness pipeline

The pipeline composes the syntax normalizer, empty-certificate pair formatter,
and the reused CLIQUE graph-invariant guard.  It is total on raw graph strings;
parser failures become the ill-formed sentinel and therefore produce `false`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.RawWellFormed

open _root_.Turing
open SyntaxNormalizer
open GraphPairFormatter
open WellFormedGuard

/-- Exact Boolean specification computed by the composed machine. -/
def rawWellFormedPass (input : List CliqueSym) : Bool :=
  wellFormedPass []
    (encodeCliqueInstance (normalizedInstanceValue input))

/-- The total Boolean accepts exactly when the syntax-normalized typed graph is
well formed. -/
theorem rawWellFormedPass_eq_true_iff (input : List CliqueSym) :
    rawWellFormedPass input = true ↔
      (normalizedInstanceValue input).WellFormed := by
  exact wellFormedPass_encode_iff [] (normalizedInstanceValue input)

/-- Boolean equality form of the same exact specification. -/
theorem rawWellFormedPass_eq_decide (input : List CliqueSym) :
    rawWellFormedPass input =
      decide (normalizedInstanceValue input).WellFormed := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact rawWellFormedPass_eq_true_iff input

/-- First compose syntax normalization with the graph-pair formatter. -/
noncomputable def normalizedGraphPairComputableInPolyTime :
    TM2ComputableInPolyTime id graphPairEncoding
      (fun input => encodeCliqueInstance (normalizedInstanceValue input)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SyntaxNormalizer.computableInPolyTime
    GraphPairFormatter.typedComputableInPolyTime
  change TM2ComputableInPolyTime id graphPairEncoding
    (fun input => encodeCliqueInstance (normalizedInstanceValue input))
  simpa [Function.comp_def] using Classical.choice composed

/-- A fixed polynomial-time TM2 decides graph well-formedness from the original
raw graph string, including exact rejection of parser failures. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id TM2Comp.boolEncoding rawWellFormedPass := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizedGraphPairComputableInPolyTime
    WellFormedGuard.graphComputableInPolyTime
  change TM2ComputableInPolyTime id TM2Comp.boolEncoding
    (fun input => wellFormedPass []
      (encodeCliqueInstance (normalizedInstanceValue input)))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.RawWellFormed
