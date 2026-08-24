import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.RawTotal.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.TypedTotal.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.BranchSelector.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams

/-!
# VERTEX-COVER to HAM-CYCLE: guarded raw runtime
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.RawTotal

open _root_.Turing
open PolyBuilder
open VertexCover.ComplementMachine
open VertexCover.ComplementMachine.NonedgeFilter

def guardSymbol (accept : Bool) : CliqueSym :=
  (guardBranch accept).symbol

def flagPairLeft (input : List VertexCoverSym) :
    List (Option CliqueSym) :=
  OptionPairLeft.format
    ((TM2Comp.boolEncoding (RawWellFormed.rawWellFormedPass input)).map
      guardSymbol)

def candidatePairRight (input : List VertexCoverSym) :
    List (Option CliqueSym) :=
  (normalizedTarget input).map some

theorem selectorInput_eq (input : List VertexCoverSym) :
    flagPairLeft input ++ candidatePairRight input =
      BranchSelector.inputEncoding (selectorData input) := by
  cases hpass : RawWellFormed.rawWellFormedPass input <;>
    simp [flagPairLeft, candidatePairRight, BranchSelector.inputEncoding,
      selectorData, guardBranch, guardSymbol, TM2Comp.boolEncoding,
      OptionPairLeft.format, pairEncoding, hpass]

private noncomputable def rawWellFormedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun input => TM2Comp.boolEncoding
        (RawWellFormed.rawWellFormedPass input)) := by
  let machine := RawWellFormed.computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa using output }

private noncomputable def flagPairLeftComputableInPolyTime :
    TM2ComputableInPolyTime id id flagPairLeft := by
  let taggedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawWellFormedStreamComputableInPolyTime
    (listMap_computableInPolyTime guardSymbol)
  let tagged := Classical.choice taggedExists
  let pairedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch tagged
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime id id
    (fun input => OptionPairLeft.format
      ((TM2Comp.boolEncoding (RawWellFormed.rawWellFormedPass input)).map
        guardSymbol))
  simpa [Function.comp_def] using Classical.choice pairedExists

private noncomputable def normalizedTargetComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedTarget := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SyntaxNormalizer.computableInPolyTime TypedTotal.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => TypedTotal.stream
      (SyntaxNormalizer.normalizedInstanceValue input))
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def candidatePairRightComputableInPolyTime :
    TM2ComputableInPolyTime id id candidatePairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizedTargetComputableInPolyTime
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  exact Classical.choice composed

/-- A fixed machine builds the exact guarded-selector input from one raw
source word. -/
noncomputable def selectorDataComputableInPolyTime :
    TM2ComputableInPolyTime id BranchSelector.inputEncoding selectorData := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    GeneralCliqueVerifier.AdjacencyPipeline.encodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    flagPairLeftComputableInPolyTime candidatePairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [selectorInput_eq input] at output
        simpa using output }

/-- One fixed polynomial-time TM2 computes the total raw reduction map. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id machineVertexCoverToHamiltonianMap := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    selectorDataComputableInPolyTime BranchSelector.computableInPolyTime
  exact Classical.choice composed

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.RawTotal
