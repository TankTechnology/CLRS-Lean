import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-!
# VERTEX-COVER complement machine: nonedge-filter input

This module assembles, from one canonical graph input, the fixed-pair stream
consumed by the nonedge filter: every normalized candidate query on the left
and the unchanged graph encoding on the right.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter

open _root_.Turing
open PolyBuilder
open GeneralCliqueVerifier

/-- Complete typed candidate family for one graph. -/
def candidatePairs (I : CliqueInstance) : List (Nat × Nat) :=
  vertexCoverNormalizedPairs I.vertexCount

/-- Literal candidate edge stream. -/
def candidateStream (I : CliqueInstance) : List CliqueSym :=
  (candidatePairs I).flatMap encodeCliqueEdge

/-- Exact paired input expected by a repeated graph-lookup filter. -/
def inputStream (I : CliqueInstance) : List (Option CliqueSym) :=
  pairEncoding (candidateStream I) (encodeCliqueInstance I)

/-- The desired semantic result is precisely the filter of this candidate
family by failed source-edge membership. -/
theorem complementEdges_eq_filter (I : CliqueInstance) :
    vertexCoverComplementEdges I =
      (candidatePairs I).filter fun edge => edge ∉ I.edges := by
  rfl

/-- Pair generator exposed at its literal stream boundary. -/
noncomputable def candidateStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id candidateStream := by
  let pairs := PairStream.computableInPolyTime
  exact
    { tm := pairs.tm
      inputAlphabet := pairs.inputAlphabet
      outputAlphabet := pairs.outputAlphabet
      time := pairs.time
      outputsFun := fun I => by
        simpa [candidateStream, candidatePairs] using pairs.outputsFun I }

/-- Identity graph branch at the literal stream boundary. -/
noncomputable def graphStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id encodeCliqueInstance := by
  let copy := scanCopy_computableInPolyTime (Γ := CliqueSym)
  exact
    { tm := copy.tm
      inputAlphabet := copy.inputAlphabet
      outputAlphabet := copy.outputAlphabet
      time := copy.time
      outputsFun := fun I => by
        simpa using copy.outputsFun (encodeCliqueInstance I) }

/-- Candidate branch with its unique pair separator appended. -/
def candidatePairLeft (I : CliqueInstance) : List (Option CliqueSym) :=
  OptionPairLeft.format (candidateStream I)

/-- Graph branch tagged for the right half of the pair. -/
def graphPairRight (I : CliqueInstance) : List (Option CliqueSym) :=
  (encodeCliqueInstance I).map some

noncomputable def candidatePairLeftComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id candidatePairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    candidateStreamComputableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  exact Classical.choice composed

noncomputable def graphPairRightComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id graphPairRight := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    graphStreamComputableInPolyTime
    (AdjacencyPipeline.someMapComputableInPolyTime CliqueSym)
  exact Classical.choice composed

/-- A fixed polynomial-time TM2 constructs the exact candidate/graph pair
from the original canonical graph string. -/
noncomputable def inputStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance id inputStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    AdjacencyPipeline.encodeOptionCliqueSymPair
    AdjacencyPipeline.decodeOptionCliqueSymPair
    AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    candidatePairLeftComputableInPolyTime
    graphPairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        have output := joined.outputsFun I
        have heq : candidatePairLeft I ++ graphPairRight I =
            inputStream I := by
          simp [candidatePairLeft, graphPairRight, inputStream,
            OptionPairLeft.format, pairEncoding, List.append_assoc]
        rw [heq] at output
        simpa using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.NonedgeFilter
