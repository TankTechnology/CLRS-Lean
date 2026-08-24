import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Header
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.WidgetEdges.Formatter

/-!
# VERTEX-COVER to HAM-CYCLE machine: verified nondegenerate prefix

This module joins the target header and the complete internal-widget edge
family.  Both components read the same raw source word; their concatenation
is therefore implemented by the reusable fixed-pair same-input closure.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.NondegeneratePrefix

open _root_.Turing
open PolyBuilder
open HamiltonianCycleReduction

/-- The currently verified prefix of the ordinary CLRS target encoding. -/
def stream (input : List CliqueSym) : List CliqueSym :=
  Header.header input ++ WidgetEdges.widgetEdgeStream input

/-- A single fixed polynomial-time TM2 computes the verified target prefix. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime id id stream := by
  exact fixedPairSameInputConcat_computableInPolyTime
    TMClique.encodeCliqueSymPair TMClique.decodeCliqueSymPair
    TMClique.decode_encodeCliqueSymPair
    Header.computableInPolyTime WidgetEdges.computableInPolyTime

/-- Exact canonical semantics: the two unary header fields are followed by
all fourteen internal edges of every source-edge gadget. -/
theorem stream_encode (I : VertexCoverInstance) :
    stream (encodeVertexCoverInstance I) =
      (.instanceMark ::
        prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
          (.fieldSep ::
            prependCliqueTicks (selectorBase I.edges.length + I.targetSize)
              [.fieldSep])) ++
        (allGlobalWidgetEdges I.edges.length).flatMap encodeCliqueEdge := by
  rw [stream, Header.header_encode, WidgetEdges.widgetEdgeStream_encode]

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.NondegeneratePrefix
