import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Instance

/-!
# Deterministic graph complement for the CLIQUE-to-VERTEX-COVER reduction

This module enumerates normalized vertex pairs in a deterministic row-major
order, filters out source edges, and constructs the graph-plus-target instance
used by the textbook complement reduction.

Main results:

- `mem_normalizedPairs_iff`: exact pair-enumeration semantics.
- `mem_complementEdges_iff`: exact complement-edge characterization.
- `CliqueInstance.complementForVertexCover_wellFormed`: the reduction preserves
  graph-instance well-formedness.

Current gaps:

- The clique/cover semantic equivalence is proved in the following modules.
-/

namespace CLRS
namespace Chapter34

/-! ## Deterministic normalized pair enumeration -/

/-- The normalized pairs in row `u`, ordered by increasing second endpoint. -/
def normalizedPairRow (n u : Nat) : List (Nat × Nat) :=
  (List.range (n - u - 1)).map fun offset => (u, u + offset + 1)

/-- Exact membership characterization for one row of normalized pairs. -/
theorem mem_normalizedPairRow_iff {n u a b : Nat} :
    (a, b) ∈ normalizedPairRow n u ↔
      a = u ∧ u < b ∧ b < n := by
  simp only [normalizedPairRow, List.mem_map, List.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨offset, hoffset, rfl, rfl⟩
    omega
  · rintro ⟨ha, hub, hbn⟩
    subst a
    refine ⟨b - u - 1, ?_, rfl, ?_⟩ <;> omega

/-- Every normalized pair `(u,v)` with `u < v < n` appears exactly in the
row-major enumeration. -/
def normalizedPairs (n : Nat) : List (Nat × Nat) :=
  (List.range n).flatMap (normalizedPairRow n)

/-- Exact membership characterization for the complete normalized pair list. -/
theorem mem_normalizedPairs_iff {n u v : Nat} :
    (u, v) ∈ normalizedPairs n ↔ u < v ∧ v < n := by
  simp only [normalizedPairs, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨row, hrow, hmem⟩
    rcases mem_normalizedPairRow_iff.mp hmem with ⟨hu, hrowv, hvn⟩
    subst row
    exact ⟨hrowv, hvn⟩
  · rintro ⟨huv, hvn⟩
    exact ⟨u, Nat.lt_trans huv hvn,
      mem_normalizedPairRow_iff.mpr ⟨rfl, huv, hvn⟩⟩

/-! ## Complement construction -/

/-- The normalized nonedges of `I`, in deterministic row-major order. -/
def complementEdges (I : CliqueInstance) : List (Nat × Nat) :=
  (normalizedPairs I.vertexCount).filter fun edge => edge ∉ I.edges

/-- A pair is emitted as a complement edge exactly when it is normalized,
in range, and absent from the source edge list. -/
theorem mem_complementEdges_iff {I : CliqueInstance} {u v : Nat} :
    (u, v) ∈ complementEdges I ↔
      u < v ∧ v < I.vertexCount ∧ (u, v) ∉ I.edges := by
  simp [complementEdges, mem_normalizedPairs_iff, and_assoc]

namespace CliqueInstance

/-- The graph complement with target `|V| - k`, used by the textbook
CLIQUE-to-VERTEX-COVER reduction. -/
def complementForVertexCover (I : CliqueInstance) : CliqueInstance where
  vertexCount := I.vertexCount
  targetSize := I.vertexCount - I.targetSize
  edges := complementEdges I

/-- The deterministic complement construction produces a well-formed
graph-plus-target instance from every well-formed source instance. -/
theorem complementForVertexCover_wellFormed {I : CliqueInstance}
    (hI : I.WellFormed) : I.complementForVertexCover.WellFormed := by
  refine ⟨Nat.sub_le _ _, ?_⟩
  intro edge hedge
  rcases edge with ⟨u, v⟩
  exact ⟨(mem_complementEdges_iff.mp hedge).1,
    (mem_complementEdges_iff.mp hedge).2.1⟩

end CliqueInstance

end Chapter34
end CLRS
