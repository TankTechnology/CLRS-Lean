import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Instance

/-!
# Deterministic graph complement for the CLIQUE-to-VERTEX-COVER reduction

This module reuses the canonical normalized-pair order of the general CLIQUE
development, filters out source edges, and constructs the graph-plus-target
instance used by the textbook complement reduction.  Sharing this order is
important at the machine boundary: the already verified certificate-pair
controller can generate the exact complement-map edge order.

Main results:

- `mem_vertexCoverNormalizedPairs_iff`: exact pair-enumeration semantics.
- `mem_vertexCoverComplementEdges_iff`: exact complement-edge characterization.
- `CliqueInstance.complementForVertexCover_wellFormed`: the reduction preserves
  graph-instance well-formedness.

Current gaps:

- The clique/cover semantic equivalence is proved in the following modules.
-/

namespace CLRS
namespace Chapter34

/-! ## Deterministic normalized pair enumeration -/

/-- The normalized pairs in row `u`, ordered by increasing second endpoint.
This local view remains useful for membership arguments even though the public
enumeration below uses the chapter-wide canonical upper-endpoint order. -/
def vertexCoverNormalizedPairRow (n u : Nat) : List (Nat × Nat) :=
  (List.range (n - u - 1)).map fun offset => (u, u + offset + 1)

/-- Exact membership characterization for one row of normalized pairs. -/
theorem mem_vertexCoverNormalizedPairRow_iff {n u a b : Nat} :
    (a, b) ∈ vertexCoverNormalizedPairRow n u ↔
      a = u ∧ u < b ∧ b < n := by
  simp only [vertexCoverNormalizedPairRow, List.mem_map, List.mem_range,
    Prod.mk.injEq]
  constructor
  · rintro ⟨offset, hoffset, rfl, rfl⟩
    omega
  · rintro ⟨ha, hub, hbn⟩
    subst a
    refine ⟨b - u - 1, ?_, rfl, ?_⟩ <;> omega

/-- Every normalized pair `(u,v)` with `u < v < n`, in the same canonical
upper-endpoint order used by the general CLIQUE occurrence graph. -/
def vertexCoverNormalizedPairs (n : Nat) : List (Nat × Nat) :=
  match n with
  | 0 => []
  | n + 1 =>
      vertexCoverNormalizedPairs n ++ (List.range n).map fun u => (u, n)

/-- Exact membership characterization for the complete normalized pair list. -/
theorem mem_vertexCoverNormalizedPairs_iff {n u v : Nat} :
    (u, v) ∈ vertexCoverNormalizedPairs n ↔ u < v ∧ v < n := by
  induction n with
  | zero => simp [vertexCoverNormalizedPairs]
  | succ n ih =>
      simp only [vertexCoverNormalizedPairs, List.mem_append, ih,
        List.mem_map, List.mem_range]
      constructor
      · rintro (⟨huv, hvn⟩ | ⟨w, hwn, hpair⟩)
        · exact ⟨huv, Nat.lt_succ_of_lt hvn⟩
        · cases hpair
          exact ⟨hwn, by omega⟩
      · rintro ⟨huv, hvn⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hvn) with hvn' | rfl
        · exact Or.inl ⟨huv, hvn'⟩
        · exact Or.inr ⟨u, huv, rfl⟩

/-! ## Complement construction -/

/-- The normalized nonedges of `I`, in deterministic canonical order. -/
def vertexCoverComplementEdges (I : CliqueInstance) : List (Nat × Nat) :=
  (vertexCoverNormalizedPairs I.vertexCount).filter fun edge => edge ∉ I.edges

/-- A pair is emitted as a complement edge exactly when it is normalized,
in range, and absent from the source edge list. -/
theorem mem_vertexCoverComplementEdges_iff {I : CliqueInstance} {u v : Nat} :
    (u, v) ∈ vertexCoverComplementEdges I ↔
      u < v ∧ v < I.vertexCount ∧ (u, v) ∉ I.edges := by
  simp [vertexCoverComplementEdges, mem_vertexCoverNormalizedPairs_iff,
    and_assoc]

namespace CliqueInstance

/-- The graph complement with target `|V| - k`, used by the textbook
CLIQUE-to-VERTEX-COVER reduction. -/
def complementForVertexCover (I : CliqueInstance) : CliqueInstance where
  vertexCount := I.vertexCount
  targetSize := I.vertexCount - I.targetSize
  edges := vertexCoverComplementEdges I

/-- The deterministic complement construction produces a well-formed
graph-plus-target instance from every well-formed source instance. -/
theorem complementForVertexCover_wellFormed {I : CliqueInstance}
    (hI : I.WellFormed) : I.complementForVertexCover.WellFormed := by
  refine ⟨Nat.sub_le _ _, ?_⟩
  intro edge hedge
  rcases edge with ⟨u, v⟩
  exact ⟨(mem_vertexCoverComplementEdges_iff.mp hedge).1,
    (mem_vertexCoverComplementEdges_iff.mp hedge).2.1⟩

end CliqueInstance

end Chapter34
end CLRS
