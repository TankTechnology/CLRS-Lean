import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.RawReduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.EncodingBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding.Canonicality

/-!
# Polynomial output length of the raw HAM-CYCLE reduction

Successful source parses are canonical, so their physical length bounds the
vertex count, target, and number of stored edge occurrences simultaneously.
Combining that parser fact with the typed gadget bound yields one cubic theorem
for all raw words; rejecting branches emit a fixed constant-size graph.

Main result:

- Theorem `vertexCoverToHamiltonianMap_length_le`: cubic all-input output
  length of the total raw reduction.
-/

namespace CLRS.Chapter34

open HamiltonianCycleReduction

/-- Every stored edge occurrence contributes at least one symbol to the shared
unary graph encoding. -/
theorem cliqueEdges_length_le_encodingLength (edges : List (Nat × Nat)) :
    edges.length ≤ cliqueEdgesEncodingLength edges := by
  induction edges with
  | nil => simp [cliqueEdgesEncodingLength]
  | cons edge edges ih =>
      change edges.length + 1 ≤
        edge.1 + edge.2 + 3 + cliqueEdgesEncodingLength edges
      omega

/-- The fixed HAM-CYCLE fallback path has nineteen symbols in the shared unary
graph grammar. -/
theorem canonicalHamiltonianNoInstance_encoding_length :
    (encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance).length =
      19 := by
  rw [encodeCliqueInstance_length]
  norm_num [canonicalHamiltonianNoInstance, cliqueEdgesEncodingLength]

/-- The total VERTEX-COVER-to-HAM-CYCLE map emits at most a cubic number of
symbols on every raw source word. -/
theorem vertexCoverToHamiltonianMap_length_le
    (input : List VertexCoverSym) :
    (vertexCoverToHamiltonianMap input).length ≤
      1000 * (input.length + 1) ^ 3 := by
  cases hdecode : decodeVertexCoverInstance input with
  | none =>
      rw [show vertexCoverToHamiltonianMap input =
          encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance by
        simp [vertexCoverToHamiltonianMap, hdecode]]
      rw [canonicalHamiltonianNoInstance_encoding_length]
      have hcube : 1 ≤ (input.length + 1) ^ 3 :=
        Nat.one_le_pow' 3 input.length
      nlinarith
  | some I =>
      by_cases hI : I.WellFormed
      · rw [show vertexCoverToHamiltonianMap input =
            encodeHamiltonianCycleInstance
              (vertexCoverToHamiltonianInstance I) by
          simp [vertexCoverToHamiltonianMap, hdecode, hI]]
        have hout := encode_vertexCoverToHamiltonianInstance_length_le I
        have hedgeCount := cliqueEdges_length_le_encodingLength I.edges
        have hcanonical :=
          encodeCliqueInstance_eq_of_decode_eq_some input I hdecode
        have hsourceSize :
            I.vertexCount + I.targetSize + I.edges.length + 1 ≤
              input.length := by
          rw [← hcanonical, encodeCliqueInstance_length]
          omega
        have hsourceSize' :
            I.vertexCount + I.targetSize + I.edges.length + 1 ≤
              input.length + 1 := Nat.le_trans hsourceSize (Nat.le_succ _)
        have hcubic := Nat.pow_le_pow_left hsourceSize' 3
        exact Nat.le_trans hout (Nat.mul_le_mul_left 1000 hcubic)
      · rw [show vertexCoverToHamiltonianMap input =
            encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance by
          simp [vertexCoverToHamiltonianMap, hdecode, hI]]
        rw [canonicalHamiltonianNoInstance_encoding_length]
        have hcube : 1 ≤ (input.length + 1) ^ 3 :=
          Nat.one_le_pow' 3 input.length
        nlinarith

end CLRS.Chapter34
