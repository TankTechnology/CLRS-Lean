import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.Total
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairFirstProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.PairSecondProjection
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.OptionPairLeft
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-!
# VERTEX-COVER verifier input pipeline

The NP certificate is the clique left outside a vertex cover.  This module
projects the raw graph from the public certificate/input pair, constructs its
normalized complement, and pairs that graph with the unchanged certificate.
Every stage is a fixed polynomial-time TM2, so the already verified general
CLIQUE verifier can be reused without weakening the raw-input contract.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.VerifierMachine

open _root_.Turing
open PolyBuilder

abbrev RawInput := List VertexCoverSym × List VertexCoverSym

def rawEncoding (input : RawInput) : List (Option CliqueSym) :=
  pairEncoding input.1 input.2

def normalizedCliqueInput (input : RawInput) : List CliqueSym × List CliqueSym :=
  (input.1, ComplementMachine.Total.normalizedComplement input.2)

def certificatePairLeft (input : RawInput) : List (Option CliqueSym) :=
  OptionPairLeft.format input.1

def complementPairRight (input : RawInput) : List (Option CliqueSym) :=
  (ComplementMachine.Total.normalizedComplement input.2).map some

theorem normalizedCliqueInput_stream_eq (input : RawInput) :
    certificatePairLeft input ++ complementPairRight input =
      pairEncoding (normalizedCliqueInput input).1
        (normalizedCliqueInput input).2 := by
  simp [certificatePairLeft, complementPairRight, normalizedCliqueInput,
    OptionPairLeft.format, pairEncoding, List.append_assoc]

/-- Project the original graph half and decide its typed well-formedness. -/
noncomputable def rawWellFormedComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => ComplementMachine.RawWellFormed.rawWellFormedPass input.2) := by
  let projected := PairSecondProjection.computableInPolyTime CliqueSym
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch projected
    ComplementMachine.RawWellFormed.computableInPolyTime
  change TM2ComputableInPolyTime
    (fun input : List CliqueSym × List CliqueSym =>
      pairEncoding input.1 input.2)
    TM2Comp.boolEncoding
    (fun input => ComplementMachine.RawWellFormed.rawWellFormedPass input.2)
  simpa [Function.comp_def] using Classical.choice composed

/-- Project the certificate half and append the unique pair separator. -/
noncomputable def certificatePairLeftComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id certificatePairLeft := by
  let projected := PairFirstProjection.computableInPolyTime CliqueSym
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch projected
    (OptionPairLeft.computableInPolyTime CliqueSym)
  change TM2ComputableInPolyTime
    (fun input : List CliqueSym × List CliqueSym =>
      pairEncoding input.1 input.2)
    id (fun input => OptionPairLeft.format input.1)
  simpa [Function.comp_def] using Classical.choice composed

/-- Project the graph half, complement it, and tag it as the right pair half. -/
noncomputable def complementPairRightComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding id complementPairRight := by
  let projected := PairSecondProjection.computableInPolyTime CliqueSym
  let complementedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    projected ComplementMachine.Total.normalizedComplementComputableInPolyTime
  let complemented := Classical.choice complementedExists
  let taggedExists := TM2Comp.TM2ComputableInPolyTime.comp_scratch complemented
    (GeneralCliqueVerifier.AdjacencyPipeline.someMapComputableInPolyTime
      CliqueSym)
  change TM2ComputableInPolyTime
    (fun input : List CliqueSym × List CliqueSym =>
      pairEncoding input.1 input.2)
    id (fun input =>
      (ComplementMachine.Total.normalizedComplement input.2).map some)
  simpa [Function.comp_def] using Classical.choice taggedExists

/-- A fixed TM2 constructs exactly the paired input expected by the reused
general CLIQUE verifier. -/
noncomputable def normalizedCliqueInputComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding
      (fun input : List CliqueSym × List CliqueSym =>
        pairEncoding input.1 input.2)
      normalizedCliqueInput := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    GeneralCliqueVerifier.AdjacencyPipeline.encodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decodeOptionCliqueSymPair
    GeneralCliqueVerifier.AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    certificatePairLeftComputableInPolyTime
    complementPairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [normalizedCliqueInput_stream_eq input] at output
        simpa [normalizedCliqueInput] using output }

/-- Run the complete general CLIQUE verifier on the complement graph. -/
noncomputable def complementCliqueCheckComputableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => cliqueVerifier input.1
        (ComplementMachine.Total.normalizedComplement input.2)) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    normalizedCliqueInputComputableInPolyTime
    GeneralCliqueVerifier.cliqueVerifierComputableInPolyTime
  simpa [normalizedCliqueInput, Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.VertexCover.VerifierMachine
