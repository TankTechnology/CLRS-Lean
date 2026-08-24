import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.TypedTotal.Core
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Ordinary.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchClassifier.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchSelector.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams

/-!
# VERTEX-COVER to HAM-CYCLE: total typed runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.TypedTotal

open _root_.Turing
open PolyBuilder

def branchPairLeft (I : VertexCoverInstance) : List (Option CliqueSym) :=
  OptionPairLeft.format [(branch I).symbol]

def candidatePairRight (I : VertexCoverInstance) : List (Option CliqueSym) :=
  (Ordinary.stream I).map some

theorem selectorInput_eq (I : VertexCoverInstance) :
    branchPairLeft I ++ candidatePairRight I =
      BranchSelector.inputEncoding (selectorData I) := by
  simp [branchPairLeft, candidatePairRight, BranchSelector.inputEncoding,
    selectorData, OptionPairLeft.format, pairEncoding]

private noncomputable def branchPairLeftComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id branchPairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    BranchClassifier.computableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime encodeVertexCoverInstance id
    (fun I : VertexCoverInstance =>
      OptionPairLeft.format [(branch I).symbol])
  exact Classical.choice composed

private noncomputable def candidatePairRightComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id
      candidatePairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    Ordinary.computableInPolyTime
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  change TM2ComputableInPolyTime encodeVertexCoverInstance id
    (fun I : VertexCoverInstance => (Ordinary.stream I).map some)
  exact Classical.choice composed

/-- A fixed machine builds the selector's tagged pair from the same source. -/
noncomputable def selectorDataComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance
      BranchSelector.inputEncoding selectorData := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    GeneralCliqueVerifier.AdjacencyPipeline.encodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    branchPairLeftComputableInPolyTime candidatePairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        have output := joined.outputsFun I
        rw [selectorInput_eq I] at output
        simpa using output }

/-- One fixed polynomial-time TM2 emits the exact total typed target. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id stream := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    selectorDataComputableInPolyTime BranchSelector.computableInPolyTime
  change TM2ComputableInPolyTime encodeVertexCoverInstance id
    (fun I : VertexCoverInstance =>
      BranchSelector.selectedOutput (selectorData I))
  exact Classical.choice composed

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.TypedTotal
