import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.TypedComplement
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.RawWellFormed
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.GuardSelector
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Total concrete CLIQUE-to-VERTEX-COVER machine

This module assembles the raw well-formedness bit and the normalized complement
candidate, feeds both to the fixed guarded selector, and identifies the result
with the semantic total reduction on every raw word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Total

open _root_.Turing
open PolyBuilder
open NonedgeFilter

def normalizedComplement (input : List CliqueSym) : List CliqueSym :=
  encodeCliqueInstance
    (SyntaxNormalizer.normalizedInstanceValue input).complementForVertexCover

def selectorData (input : List CliqueSym) : Bool × List CliqueSym :=
  (RawWellFormed.rawWellFormedPass input, normalizedComplement input)

def flagPairLeft (input : List CliqueSym) : List (Option CliqueSym) :=
  OptionPairLeft.format
    ((TM2Comp.boolEncoding (RawWellFormed.rawWellFormedPass input)).map
      bitSymbol)

def candidatePairRight (input : List CliqueSym) : List (Option CliqueSym) :=
  (normalizedComplement input).map some

theorem selectorInput_eq (input : List CliqueSym) :
    flagPairLeft input ++ candidatePairRight input =
      GuardSelector.inputEncoding (selectorData input) := by
  simp [flagPairLeft, candidatePairRight, GuardSelector.inputEncoding,
    selectorData, TM2Comp.boolEncoding, OptionPairLeft.format, pairEncoding]

noncomputable def normalizedComplementComputableInPolyTime :
    TM2ComputableInPolyTime id id normalizedComplement := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    SyntaxNormalizer.computableInPolyTime
    TypedComplement.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simpa [normalizedComplement, Function.comp_def] using output }

noncomputable def rawWellFormedStreamComputableInPolyTime :
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

noncomputable def flagPairLeftComputableInPolyTime :
    TM2ComputableInPolyTime id id flagPairLeft := by
  let taggedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    rawWellFormedStreamComputableInPolyTime
    (listMap_computableInPolyTime bitSymbol)
  let tagged := Classical.choice taggedExists
  let pairedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch tagged
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime id id
    (fun input => OptionPairLeft.format
      ((TM2Comp.boolEncoding (RawWellFormed.rawWellFormedPass input)).map
        bitSymbol))
  simpa [Function.comp_def] using Classical.choice pairedExists

noncomputable def candidatePairRightComputableInPolyTime :
    TM2ComputableInPolyTime id id candidatePairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizedComplementComputableInPolyTime
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  exact Classical.choice composed

/-- A fixed machine assembles exactly the tagged selector input from the same
raw source word. -/
noncomputable def selectorDataComputableInPolyTime :
    TM2ComputableInPolyTime id GuardSelector.inputEncoding selectorData := by
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

/-- The selector formulation agrees with the public total raw reduction on
parser failures, ill-formed decoded graphs, and well-formed graphs. -/
theorem selectedOutput_eq_reduction (input : List CliqueSym) :
    GuardSelector.selectedOutput (selectorData input) =
      cliqueToVertexCoverMap input := by
  cases hdecode : decodeCliqueInstance input with
  | none =>
      have hnormalized : SyntaxNormalizer.normalizedInstanceValue input =
          SyntaxNormalizer.malformedGraphSentinel :=
        SyntaxNormalizer.normalizedInstanceValue_of_decode_none hdecode
      have hflag : RawWellFormed.rawWellFormedPass input = false := by
        rw [RawWellFormed.rawWellFormedPass_eq_decide]
        simp [hnormalized,
          SyntaxNormalizer.malformedGraphSentinel_not_wellFormed]
      simp [GuardSelector.selectedOutput, selectorData, hflag,
        cliqueToVertexCoverMap, guardedGraphComplementMap, hdecode]
  | some I =>
      have hnormalized : SyntaxNormalizer.normalizedInstanceValue input = I :=
        SyntaxNormalizer.normalizedInstanceValue_of_decode_some hdecode
      by_cases hI : I.WellFormed
      · have hflag : RawWellFormed.rawWellFormedPass input = true := by
          rw [RawWellFormed.rawWellFormedPass_eq_decide]
          simp [hnormalized, hI]
        simp [GuardSelector.selectedOutput, selectorData, normalizedComplement,
          hflag, hnormalized, cliqueToVertexCoverMap,
          guardedGraphComplementMap, hdecode, hI]
      · have hflag : RawWellFormed.rawWellFormedPass input = false := by
          rw [RawWellFormed.rawWellFormedPass_eq_decide]
          simp [hnormalized, hI]
        simp [GuardSelector.selectedOutput, selectorData, hflag,
          cliqueToVertexCoverMap, guardedGraphComplementMap, hdecode, hI]

/-- The textbook total CLIQUE-to-VERTEX-COVER reduction is computed by one
fixed polynomial-time TM2 on all raw graph strings. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id cliqueToVertexCoverMap := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    selectorDataComputableInPolyTime GuardSelector.computableInPolyTime
  let machine := Classical.choice composed
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun input => by
        have output := machine.outputsFun input
        simp only [Function.comp_apply, id_eq] at output
        rw [selectedOutput_eq_reduction input] at output
        simpa using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.Total
