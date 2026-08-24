import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.RangeCertificate
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.PairStream.Semantics
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# VERTEX-COVER complement machine: polynomial pair stream

The graph-to-range-certificate controller composes with the existing verified
general-CLIQUE certificate-pair generator.  The semantic equality identifies
the result with the exact normalized-pair family used by the complement map.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream

open _root_.Turing
open GeneralCliqueVerifier

/-- A fixed polynomial-time TM2 maps a canonical graph encoding directly to
the complete canonical normalized-pair edge stream. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime encodeCliqueInstance
      (fun edges : List (Nat × Nat) => edges.flatMap encodeCliqueEdge)
      (fun I : CliqueInstance =>
        vertexCoverNormalizedPairs I.vertexCount) := by
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    RangeCertificate.computableInPolyTime
    GeneralCliqueVerifier.PairGenerator.rawPairs_computableInPolyTime
  let raw := Classical.choice composed
  exact
    { tm := raw.tm
      inputAlphabet := raw.inputAlphabet
      outputAlphabet := raw.outputAlphabet
      time := raw.time
      outputsFun := fun I => by
        have output := raw.outputsFun I
        simpa [Function.comp_def,
          certificateRangeRawPairs_eq_vertexCoverNormalizedPairs] using
            output }

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.PairStream
