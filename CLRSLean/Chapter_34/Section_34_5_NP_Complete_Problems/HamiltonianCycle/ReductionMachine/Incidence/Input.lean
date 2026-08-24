import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate.Runtime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Instance
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.VerifierMachine.AdjacencyPipeline.RawStreams
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-!
# VERTEX-COVER to HAM-CYCLE machine: incidence scanner input

Both incidence-dependent edge families need the source edges grouped by
source vertex.  This module builds the one shared physical input for that
scan: the canonical vertex queries `0, ..., vertexCount - 1`, followed by the
unchanged graph encoding.  The separator is represented by `none`, exactly as
in the already verified batch graph-lookup pipeline.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence

open _root_.Turing
open PolyBuilder
open GeneralCliqueVerifier

/-- Canonical source-vertex query stream. -/
def vertexQueryStream (I : VertexCoverInstance) : List CliqueSym :=
  encodeCliqueCertificate (List.range I.vertexCount)

/-- The shared query/graph input consumed by the incidence scanner. -/
def inputStream (I : VertexCoverInstance) : List (Option CliqueSym) :=
  pairEncoding (vertexQueryStream I) (encodeVertexCoverInstance I)

/-- Left branch with its unique pair separator appended. -/
def vertexQueryPairLeft (I : VertexCoverInstance) :
    List (Option CliqueSym) :=
  OptionPairLeft.format (vertexQueryStream I)

/-- Right branch tagged as ordinary pair payload. -/
def graphPairRight (I : VertexCoverInstance) : List (Option CliqueSym) :=
  (encodeVertexCoverInstance I).map some

/-- The existing range controller computes the exact query stream. -/
noncomputable def vertexQueryStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id vertexQueryStream := by
  let rangeMachine :=
    VertexCover.ComplementMachine.PairStream.RangeCertificate.computableInPolyTime
  exact
    { tm := rangeMachine.tm
      inputAlphabet := rangeMachine.inputAlphabet
      outputAlphabet := rangeMachine.outputAlphabet
      time := rangeMachine.time
      outputsFun := fun I => by
        simpa [vertexQueryStream,
          VertexCover.ComplementMachine.PairStream.RangeCertificate.rangeCertificate]
          using rangeMachine.outputsFun I }

noncomputable def vertexQueryPairLeftComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id
      vertexQueryPairLeft := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    vertexQueryStreamComputableInPolyTime
    (OptionPairLeft.computableInPolyTime CliqueSym)
  exact Classical.choice composed

noncomputable def graphPairRightComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id graphPairRight := by
  let copied : TM2ComputableInPolyTime encodeVertexCoverInstance id
      encodeVertexCoverInstance := by
    let machine := scanCopy_computableInPolyTime (Γ := CliqueSym)
    exact
      { tm := machine.tm
        inputAlphabet := machine.inputAlphabet
        outputAlphabet := machine.outputAlphabet
        time := machine.time
        outputsFun := fun I => by
          have output := machine.outputsFun (encodeVertexCoverInstance I)
          simpa using output }
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch copied
    (AdjacencyPipeline.someMapComputableInPolyTime CliqueSym)
  exact Classical.choice composed

/-- A fixed polynomial-time TM2 constructs the exact shared scanner input
from the original canonical VERTEX-COVER encoding. -/
noncomputable def inputStreamComputableInPolyTime :
    TM2ComputableInPolyTime encodeVertexCoverInstance id inputStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    AdjacencyPipeline.encodeOptionCliqueSymPair
    AdjacencyPipeline.decodeOptionCliqueSymPair
    AdjacencyPipeline.decode_encodeOptionCliqueSymPair
    vertexQueryPairLeftComputableInPolyTime
    graphPairRightComputableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        have output := joined.outputsFun I
        have heq : vertexQueryPairLeft I ++ graphPairRight I =
            inputStream I := by
          simp [vertexQueryPairLeft, graphPairRight, inputStream,
            OptionPairLeft.format, pairEncoding, List.append_assoc]
        rw [heq] at output
        simpa using output }

theorem inputStream_encode (I : VertexCoverInstance) :
    inputStream I =
      pairEncoding
        (encodeCliqueCertificate (List.range I.vertexCount))
        (encodeCliqueInstance I) := by
  rfl

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence
