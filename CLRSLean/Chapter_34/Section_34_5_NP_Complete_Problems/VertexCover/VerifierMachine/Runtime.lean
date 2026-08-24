import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.VerifierMachine.Input
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.AndOr

/-!
# VERTEX-COVER verifier machine and runtime

The final verifier accepts precisely when the original raw graph is well
formed and the supplied certificate is a clique in its normalized complement.
The two Boolean branches share the original separator-encoded input and are
combined by the generic fixed TM2 conjunction construction.
-/

noncomputable section

namespace CLRS.Chapter34

/-- Concrete VERTEX-COVER verifier using the clique outside the cover as its
certificate. -/
def vertexCoverCliqueVerifier
    (certificate input : List VertexCoverSym) : Bool :=
  Turing.VertexCover.ComplementMachine.RawWellFormed.rawWellFormedPass input &&
    cliqueVerifier certificate
      (Turing.VertexCover.ComplementMachine.Total.normalizedComplement input)

namespace Turing.VertexCover.VerifierMachine

open _root_.Turing

/-- One fixed polynomial-time TM2 computes the complete raw VERTEX-COVER
verifier. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime rawEncoding TM2Comp.boolEncoding
      (fun input => vertexCoverCliqueVerifier input.1 input.2) := by
  let combined := Turing.TM2AndOr.andOrComputableInPolyTime
    rawWellFormedComputableInPolyTime
    complementCliqueCheckComputableInPolyTime
    Bool.and
  simpa [vertexCoverCliqueVerifier] using combined

end Turing.VertexCover.VerifierMachine
end CLRS.Chapter34
