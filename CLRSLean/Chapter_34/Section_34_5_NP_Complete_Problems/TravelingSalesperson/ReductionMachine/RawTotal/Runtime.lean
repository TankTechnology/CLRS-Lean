import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawTotal.Semantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.RawSelector.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Codec
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft.Runtime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-! # Total raw HAM-CYCLE-to-TSP fixed runtime -/

noncomputable section

namespace CLRS.Chapter34.Turing.TSPReduction.RawTotal

open _root_.Turing
open PolyBuilder
open VertexCover.ComplementMachine

def flagPairLeft (input : List HamiltonianCycleSym) :
    List (Option TSPSym) :=
  OptionPairLeft.format
    ((TM2Comp.boolEncoding (RawValidity.validPass input)).map
      RawSelector.guardSymbol)

def candidatePairRight (input : List HamiltonianCycleSym) :
    List (Option TSPSym) :=
  (normalizedCandidate input).map some

theorem selectorInput_eq (input : List HamiltonianCycleSym) :
    flagPairLeft input ++ candidatePairRight input =
      RawSelector.inputEncoding (selectorData input) := by
  simp [flagPairLeft, candidatePairRight, RawSelector.inputEncoding,
    selectorData, TM2Comp.boolEncoding, OptionPairLeft.format, pairEncoding]

private noncomputable def normalizedCandidateComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedCandidate := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SyntaxNormalizer.computableInPolyTime Typed.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => Typed.stream
      (SyntaxNormalizer.normalizedInstanceValue input))
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def rawValidityStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (fun input => TM2Comp.boolEncoding (RawValidity.validPass input)) := by
  let machine := RawValidity.computableInPolyTime
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
    rawValidityStreamComputableInPolyTime
    (listMap_computableInPolyTime RawSelector.guardSymbol)
  let tagged := Classical.choice taggedExists
  let pairedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch tagged
    (OptionPairLeft.computableInPolyTime TSPSym)
  change TM2ComputableInPolyTime id id
    (fun input => OptionPairLeft.format
      ((TM2Comp.boolEncoding (RawValidity.validPass input)).map
        RawSelector.guardSymbol))
  simpa [Function.comp_def] using Classical.choice pairedExists

private noncomputable def candidatePairRightComputableInPolyTime :
    TM2ComputableInPolyTime id id candidatePairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizedCandidateComputableInPolyTime
    (listMap_computableInPolyTime (some : TSPSym → Option TSPSym))
  exact Classical.choice composed

/-- One fixed machine assembles the validity tag and complete typed candidate
from the same original word. -/
noncomputable def selectorDataComputableInPolyTime :
    TM2ComputableInPolyTime id RawSelector.inputEncoding selectorData := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeOptionTSPSymPair decodeOptionTSPSymPair
    decode_encodeOptionTSPSymPair
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

private noncomputable def machineMapComputableInPolyTime :
    TM2ComputableInPolyTime id id machineMap := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    selectorDataComputableInPolyTime RawSelector.computableInPolyTime
  change TM2ComputableInPolyTime id id
    (fun input => RawSelector.selectedOutput (selectorData input))
  simpa [Function.comp_def] using Classical.choice composed

/-- The public total serialized textbook reduction is computed by one fixed
polynomial-time TM2 on every raw HAM-CYCLE word. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id
      CLRS.Chapter34.TSPReduction.rawHamiltonianToTSP := by
  let machine := machineMapComputableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        rw [machineMap_eq_rawHamiltonianToTSP input] at output
        simpa using output }

end CLRS.Chapter34.Turing.TSPReduction.RawTotal
