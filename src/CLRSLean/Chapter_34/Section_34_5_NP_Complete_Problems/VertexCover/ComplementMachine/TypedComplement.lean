import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.Header
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.NonedgeFilter.Pipeline
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Header

/-!
# Complete typed complement-instance machine

The transformed `n, n-k` header and the generated nonedge table are computed
from the same canonical source word and joined by the reusable fixed-pair
concatenator.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.TypedComplement

open _root_.Turing
open PolyBuilder

def serializedComplement (I : CliqueInstance) : List CliqueSym :=
  Header.complementHeader I ++
    (vertexCoverComplementEdges I).flatMap encodeCliqueEdge

theorem serializedComplement_eq (I : CliqueInstance) :
    serializedComplement I =
      encodeCliqueInstance I.complementForVertexCover := by
  simp [serializedComplement, Header.complementHeader,
    CliqueInstance.complementForVertexCover, encodeCliqueInstance,
    prependCliqueTicks_append]

/-- A fixed polynomial-time TM2 computes the complete canonical complement
instance from a canonical CLIQUE instance. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance encodeCliqueInstance
      CliqueInstance.complementForVertexCover := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    Header.computableInPolyTime NonedgeFilter.computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun I => by
        have output := joined.outputsFun I
        have hsemantic := serializedComplement_eq I
        change Header.complementHeader I ++
            (vertexCoverComplementEdges I).flatMap encodeCliqueEdge = _
          at hsemantic
        rw [hsemantic] at output
        simpa using output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.TypedComplement
