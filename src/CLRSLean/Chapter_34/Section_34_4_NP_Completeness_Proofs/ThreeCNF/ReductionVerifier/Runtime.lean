import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.ThreeCNF.ReductionVerifier.Input
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairSecondProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-!
# Fixed machine for the reduction-backed 3-CNF verifier

Both branches consume the original separator-encoded certificate/formula
pair.  One projects and translates the certificate; the other projects and
reduces the formula.  Their paired output is composed with the existing fixed
general-CLIQUE verifier.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.ThreeCNFVerifier

open _root_.Turing
open PolyBuilder

def certificatePairLeft (input : RawInput) : List (Option CliqueSym) :=
  OptionPairLeft.format (cnfToCliqueCertificate input.1)

def instancePairRight (input : RawInput) : List (Option CliqueSym) :=
  (threeCNFToGeneralCliqueMap input.2).map some

theorem reducedCliqueInput_stream_eq (input : RawInput) :
    certificatePairLeft input ++ instancePairRight input =
      pairEncoding (reducedCliqueInput input).1
        (reducedCliqueInput input).2 := by
  simp [certificatePairLeft, instancePairRight, reducedCliqueInput,
    OptionPairLeft.format, pairEncoding, List.append_assoc]

/-- Project and translate the source-alphabet certificate, then append the
unique target pair separator. -/
noncomputable def certificatePairLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id certificatePairLeft := by
  let projected := PairFirstProjection.computableInPolyTime CNFSym
  let translatedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    projected (listMap_computableInPolyTime cnfToCliqueCertificateSymbol)
  let translated := Classical.choice translatedExists
  let formattedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    translated (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime
    (fun input : RawInput => pairEncoding input.1 input.2) id
    (fun input => OptionPairLeft.format
      (cnfToCliqueCertificate input.1))
  simpa [cnfToCliqueCertificate, Function.comp_def] using
    Classical.choice formattedExists

/-- Project the raw formula, compute its honest CLIQUE instance, and tag the
result as the right pair half. -/
noncomputable def instancePairRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id instancePairRight := by
  let projected := PairSecondProjection.computableInPolyTime CNFSym
  let reducedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch projected
    TMClique.threeCNFToGeneralCliqueComputableInPolyTime
  let reduced := Classical.choice reducedExists
  let taggedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch reduced
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  change TM2ComputableInPolyTime
    (fun input : RawInput => pairEncoding input.1 input.2) id
    (fun input => (threeCNFToGeneralCliqueMap input.2).map some)
  simpa [Function.comp_def] using Classical.choice taggedExists

/-- Construct exactly the separator-encoded input expected by the CLIQUE
verifier. -/
noncomputable def reducedCliqueInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun input : List CliqueSym × List CliqueSym =>
        pairEncoding input.1 input.2)
      reducedCliqueInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    GeneralCliqueVerifier.AdjacencyPipeline.encodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    certificatePairLeftComputableInPolyTime
    instancePairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [reducedCliqueInput_stream_eq input] at output
        simpa [reducedCliqueInput] using output }

/-- One fixed polynomial-time TM2 computes the complete reduction-backed
3-CNF verifier on the original raw certificate/formula pair. -/
noncomputable def reductionVerifierComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => threeCNFReductionVerifier input.1 input.2) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    reducedCliqueInputComputableInPolyTime
    GeneralCliqueVerifier.cliqueVerifierComputableInPolyTime
  simpa [reducedCliqueInput, threeCNFReductionVerifier,
    Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.ThreeCNFVerifier
