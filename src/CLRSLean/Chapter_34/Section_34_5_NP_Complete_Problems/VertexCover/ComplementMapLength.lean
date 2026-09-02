import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.RawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ReverseRawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement.EncodingBounds

/-!
# Polynomial output-size bounds for the total complement maps

Both directions use the same shared graph grammar and complement construction.
Successful decodings expose the unary vertex count inside the original input;
all other inputs use a fixed constant-size no-instance.
-/

namespace CLRS
namespace Chapter34

private theorem canonicalVertexCoverNoInstance_encoding_length :
    (encodeVertexCoverInstance canonicalVertexCoverNoInstance).length = 9 := by
  rw [encodeCliqueInstance_length]
  norm_num [canonicalVertexCoverNoInstance, cliqueEdgesEncodingLength]

private theorem noCliqueInstance_encoding_length :
    (encodeCliqueInstance noCliqueInstance).length = 7 := by
  rw [encodeCliqueInstance_length]
  norm_num [noCliqueInstance, cliqueEdgesEncodingLength]

/-- The total CLIQUE-to-VERTEX-COVER map emits at most a cubic number of unary
symbols, including on malformed and ill-formed inputs. -/
theorem cliqueToVertexCoverMap_length_le (input : List CliqueSym) :
    (cliqueToVertexCoverMap input).length ≤
      10 * (input.length + 1) ^ 3 := by
  cases hdecode : decodeCliqueInstance input with
  | none =>
      rw [show cliqueToVertexCoverMap input =
          encodeVertexCoverInstance canonicalVertexCoverNoInstance by
        exact guardedGraphComplementMap_of_decode_none hdecode]
      rw [canonicalVertexCoverNoInstance_encoding_length]
      have hcube : 1 ≤ (input.length + 1) ^ 3 := Nat.one_le_pow' 3 input.length
      nlinarith
  | some I =>
      by_cases hI : I.WellFormed
      · rw [show cliqueToVertexCoverMap input =
            encodeVertexCoverInstance I.complementForVertexCover by
          exact guardedGraphComplementMap_of_decode_wellFormed hdecode hI]
        have hout := encode_complementForVertexCover_length_le I
        have hfields := decodeCliqueInstance_fields_le_length hdecode
        have hvertex : I.vertexCount + 1 ≤ input.length + 1 := by omega
        have hcubic := Nat.pow_le_pow_left hvertex 3
        exact Nat.le_trans hout (by nlinarith)
      · rw [show cliqueToVertexCoverMap input =
            encodeVertexCoverInstance canonicalVertexCoverNoInstance by
          exact guardedGraphComplementMap_of_decode_not_wellFormed hdecode hI]
        rw [canonicalVertexCoverNoInstance_encoding_length]
        have hcube : 1 ≤ (input.length + 1) ^ 3 := Nat.one_le_pow' 3 input.length
        nlinarith

/-- The total VERTEX-COVER-to-CLIQUE map satisfies the same cubic output bound
on every raw input. -/
theorem vertexCoverToCliqueMap_length_le (input : List VertexCoverSym) :
    (vertexCoverToCliqueMap input).length ≤
      10 * (input.length + 1) ^ 3 := by
  cases hdecode : decodeVertexCoverInstance input with
  | none =>
      rw [show vertexCoverToCliqueMap input =
          encodeCliqueInstance noCliqueInstance by
        exact guardedGraphComplementMap_of_decode_none hdecode]
      rw [noCliqueInstance_encoding_length]
      have hcube : 1 ≤ (input.length + 1) ^ 3 := Nat.one_le_pow' 3 input.length
      nlinarith
  | some I =>
      by_cases hI : I.WellFormed
      · rw [show vertexCoverToCliqueMap input =
            encodeCliqueInstance I.complementForVertexCover by
          exact guardedGraphComplementMap_of_decode_wellFormed hdecode hI]
        have hout := encode_complementForVertexCover_length_le I
        have hfields := decodeCliqueInstance_fields_le_length hdecode
        have hvertex : I.vertexCount + 1 ≤ input.length + 1 := by omega
        have hcubic := Nat.pow_le_pow_left hvertex 3
        exact Nat.le_trans hout (by nlinarith)
      · rw [show vertexCoverToCliqueMap input =
            encodeCliqueInstance noCliqueInstance by
          exact guardedGraphComplementMap_of_decode_not_wellFormed hdecode hI]
        rw [noCliqueInstance_encoding_length]
        have hcube : 1 ≤ (input.length + 1) ^ 3 := Nat.one_le_pow' 3 input.length
        nlinarith

end Chapter34
end CLRS
