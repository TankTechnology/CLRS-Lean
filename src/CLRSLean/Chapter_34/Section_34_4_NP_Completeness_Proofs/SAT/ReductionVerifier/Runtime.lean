import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.SAT.ReductionVerifier.Input
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairSecondProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-! # Fixed machine for the reduction-backed SAT verifier -/

noncomputable section

namespace CLRS.Chapter34.Turing.SATVerifier

open _root_.Turing
open PolyBuilder

def certificatePairLeft (input : RawInput) : List (Option CNFSym) :=
  OptionPairLeft.format (formulaToCNFCertificate input.1)

def formulaPairRight (input : RawInput) : List (Option CNFSym) :=
  (satToThreeCNFMap input.2).map some

theorem reducedThreeCNFInput_stream_eq (input : RawInput) :
    certificatePairLeft input ++ formulaPairRight input =
      pairEncoding (reducedThreeCNFInput input).1
        (reducedThreeCNFInput input).2 := by
  simp [certificatePairLeft, formulaPairRight, reducedThreeCNFInput,
    OptionPairLeft.format, pairEncoding, List.append_assoc]

/-- Six-symbol fixed pair code for `Option CNFSym`. -/
def encodeOptionCNFSymPair :
    Option CNFSym → UnaryFrameSym × UnaryFrameSym
  | none => (.frameEnd, .frameEnd)
  | some .clauseMark => (.tick, .tick)
  | some .posMark => (.tick, .separator)
  | some .negMark => (.tick, .frameEnd)
  | some .varMark => (.separator, .tick)
  | some .endMark => (.separator, .separator)

def decodeOptionCNFSymPair :
    UnaryFrameSym → UnaryFrameSym → Option CNFSym
  | .frameEnd, .frameEnd => none
  | .tick, .tick => some .clauseMark
  | .tick, .separator => some .posMark
  | .tick, .frameEnd => some .negMark
  | .separator, .tick => some .varMark
  | .separator, .separator => some .endMark
  | _, _ => some .endMark

@[simp] theorem decode_encodeOptionCNFSymPair (symbol : Option CNFSym) :
    decodeOptionCNFSymPair (encodeOptionCNFSymPair symbol).1
      (encodeOptionCNFSymPair symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol => cases symbol <;> rfl

noncomputable def certificatePairLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id certificatePairLeft := by
  let projected := PairFirstProjection.computableInPolyTime FormulaSym
  let translatedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    projected (listMap_computableInPolyTime formulaToCNFCertificateSymbol)
  let translated := Classical.choice translatedExists
  let formattedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    translated (OptionPairLeft.computableInPolyTime CNFSym)
  change TM2ComputableInPolyTime
    (fun input : RawInput => pairEncoding input.1 input.2) id
    (fun input => OptionPairLeft.format
      (formulaToCNFCertificate input.1))
  simpa [formulaToCNFCertificate, Function.comp_def] using
    Classical.choice formattedExists

noncomputable def formulaPairRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id formulaPairRight := by
  let projected := PairSecondProjection.computableInPolyTime FormulaSym
  let reducedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch projected
    TM3CNF.satTo3CNFComputableInPolyTime
  let reduced := Classical.choice reducedExists
  let taggedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch reduced
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime CNFSym)
  change TM2ComputableInPolyTime
    (fun input : RawInput => pairEncoding input.1 input.2) id
    (fun input => (satToThreeCNFMap input.2).map some)
  simpa [satToThreeCNFMap, Function.comp_def] using
    Classical.choice taggedExists

noncomputable def reducedThreeCNFInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      ThreeCNFVerifier.rawEncoding reducedThreeCNFInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    encodeOptionCNFSymPair decodeOptionCNFSymPair
    decode_encodeOptionCNFSymPair
    certificatePairLeftComputableInPolyTime
    formulaPairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [reducedThreeCNFInput_stream_eq input] at output
        simpa [reducedThreeCNFInput, ThreeCNFVerifier.rawEncoding] using output }

/-- One fixed polynomial-time TM2 computes the complete reduction-backed SAT
verifier on the original raw certificate/formula pair. -/
noncomputable def reductionVerifierComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => satReductionVerifier input.1 input.2) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    reducedThreeCNFInputComputableInPolyTime
    ThreeCNFVerifier.reductionVerifierComputableInPolyTime
  simpa [reducedThreeCNFInput, satReductionVerifier,
    Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.SATVerifier
