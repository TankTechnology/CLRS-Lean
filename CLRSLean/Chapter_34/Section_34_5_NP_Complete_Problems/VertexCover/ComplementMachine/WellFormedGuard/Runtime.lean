import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.WellFormedGuard.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.BaseChecks.Runtime

/-!
# Graph well-formedness guard: fixed polynomial-time TM2
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard

open _root_.Turing
open GeneralCliqueVerifier

private abbrev pairedEncoding :
    List CliqueSym × List CliqueSym → List (Option CliqueSym) :=
  fun pr => pairEncoding pr.1 pr.2

/-- The reusable same-input Boolean combiner joins the target-bound pass with
the already-combined edge-order/endpoint-bound passes. -/
noncomputable def pairComputableInPolyTime :
    TM2ComputableInPolyTime pairedEncoding TM2Comp.boolEncoding
      (fun pr => wellFormedPass pr.1 pr.2) := by
  simpa [pairedEncoding, wellFormedPass] using
    TM2AndOr.andOrComputableInPolyTime
      TargetBound.targetBoundPassComputableInPolyTime
      BaseChecks.graphChecksComputableInPolyTime
      Bool.and

/-- Empty-certificate pair encoding used when the guard is applied to a graph
stream alone. -/
abbrev graphPairEncoding (input : List CliqueSym) : List (Option CliqueSym) :=
  pairEncoding [] input

/-- The same fixed machine, specialized to a graph with the irrelevant
certificate component fixed to empty. -/
noncomputable def graphComputableInPolyTime :
    TM2ComputableInPolyTime graphPairEncoding TM2Comp.boolEncoding
      (wellFormedPass []) where
  tm := pairComputableInPolyTime.tm
  inputAlphabet := pairComputableInPolyTime.inputAlphabet
  outputAlphabet := pairComputableInPolyTime.outputAlphabet
  time := pairComputableInPolyTime.time
  outputsFun := fun input => by
    simpa [graphPairEncoding, pairedEncoding] using
      pairComputableInPolyTime.outputsFun ([], input)

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.WellFormedGuard
