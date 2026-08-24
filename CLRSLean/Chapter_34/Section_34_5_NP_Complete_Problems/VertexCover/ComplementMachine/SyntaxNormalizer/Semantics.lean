import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementMachine.SyntaxNormalizer.Run
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Canonicality

/-!
# Raw graph syntax normalizer: decoder semantics
-/

namespace CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer

open GeneralCliqueVerifier

/-- Total decoded graph, using the deliberately ill-formed sentinel exactly
when the complete parser fails. -/
def normalizedInstanceValue (input : List CliqueSym) : CliqueInstance :=
  (decodeCliqueInstance input).getD malformedGraphSentinel

/-- Successful decoding is preserved as the exact typed value. -/
theorem normalizedInstanceValue_of_decode_some {input : List CliqueSym}
    {I : CliqueInstance} (hdecode : decodeCliqueInstance input = some I) :
    normalizedInstanceValue input = I := by
  simp [normalizedInstanceValue, hdecode]

/-- Parser failure becomes the fixed ill-formed sentinel. -/
theorem normalizedInstanceValue_of_decode_none {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = none) :
    normalizedInstanceValue input = malformedGraphSentinel := by
  simp [normalizedInstanceValue, hdecode]

/-- In particular, parser failure cannot silently become a well-formed graph. -/
theorem normalizedInstanceValue_not_wellFormed_of_decode_none
    {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = none) :
    ¬(normalizedInstanceValue input).WellFormed := by
  rw [normalizedInstanceValue_of_decode_none hdecode]
  exact malformedGraphSentinel_not_wellFormed

/-- The controller's pure stream is exactly the canonical encoding of its
total typed value on every raw input. -/
theorem normalizedStream_eq (input : List CliqueSym) :
    normalizedStream input =
      encodeCliqueInstance (normalizedInstanceValue input) := by
  cases hdecode : decodeCliqueInstance input with
  | none =>
      have haccepts :
          accepts (scanSymbols initialInstanceParseMode input) = false := by
        apply Bool.eq_false_of_not_eq_true
        intro htrue
        have hsyntax : instanceSyntaxAccepts input = true := by
          simpa [instanceSyntaxAccepts, accepts] using htrue
        rcases (instanceSyntaxAccepts_eq_true_iff input).1 hsyntax with
          ⟨I, hI⟩
        rw [hdecode] at hI
        contradiction
      simp [normalizedStream, haccepts, normalizedInstanceValue, hdecode]
  | some I =>
      have hsyntax : instanceSyntaxAccepts input = true :=
        (instanceSyntaxAccepts_eq_true_iff input).2 ⟨I, hdecode⟩
      have haccepts :
          accepts (scanSymbols initialInstanceParseMode input) = true := by
        simpa [instanceSyntaxAccepts, accepts] using hsyntax
      rw [normalizedStream, if_pos haccepts]
      simp only [normalizedInstanceValue, hdecode, Option.getD_some]
      exact (encodeCliqueInstance_eq_of_decode_eq_some input I hdecode).symm

end CLRS.Chapter34.Turing.VertexCover.ComplementMachine.SyntaxNormalizer
