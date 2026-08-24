import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Language

/-!
# Total raw CLIQUE-to-VERTEX-COVER semantic reduction

The map in this module is total on raw graph strings.  Well-formed decodings
are complemented; malformed and decoded-but-ill-formed inputs map to one fixed
VERTEX-COVER no-instance.  This is the semantic function that a later
polynomial-time machine must compute exactly.
-/

namespace CLRS
namespace Chapter34

/-! ## Canonical fallback no-instance -/

/-- A well-formed graph that cannot have a vertex cover of size zero. -/
def canonicalVertexCoverNoInstance : VertexCoverInstance where
  vertexCount := 2
  targetSize := 0
  edges := [(0, 1)]

/-- The fallback instance satisfies the shared graph encoding invariants. -/
theorem canonicalVertexCoverNoInstance_wellFormed :
    canonicalVertexCoverNoInstance.WellFormed := by
  simp [canonicalVertexCoverNoInstance, CliqueInstance.WellFormed]

/-- The fallback instance has no cover within its zero target. -/
theorem canonicalVertexCoverNoInstance_not_hasVertexCover :
    ¬canonicalVertexCoverNoInstance.HasVertexCover := by
  rintro ⟨vertices, hcard, hcover⟩
  have hvertices : vertices = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
  have hedge := hcover.2 (0, 1) (by simp [canonicalVertexCoverNoInstance])
  simpa [hvertices] using hedge

/-- The canonical encoding of the fallback is outside VERTEX-COVER. -/
theorem canonicalVertexCoverNoInstance_not_mem :
    encodeVertexCoverInstance canonicalVertexCoverNoInstance ∉ VERTEXCOVER := by
  rw [encodeVertexCoverInstance_mem_generalVERTEXCOVER_iff]
  exact fun h => canonicalVertexCoverNoInstance_not_hasVertexCover h.2

/-! ## Total raw reduction -/

/-- Decode the shared graph grammar, complement a well-formed instance, and
send every other input to the canonical VERTEX-COVER no-instance. -/
def cliqueToVertexCoverMap (input : List CliqueSym) : List VertexCoverSym :=
  match decodeCliqueInstance input with
  | some I =>
      if I.WellFormed then
        encodeVertexCoverInstance I.complementForVertexCover
      else
        encodeVertexCoverInstance canonicalVertexCoverNoInstance
  | none => encodeVertexCoverInstance canonicalVertexCoverNoInstance

/-- The total raw map preserves membership on every input string.  The source
language is `GeneralCLIQUE`, the language denoted by the public `CLIQUE`
facade. -/
theorem cliqueToVertexCoverMap_mem_VERTEXCOVER_iff (input : List CliqueSym) :
    cliqueToVertexCoverMap input ∈ VERTEXCOVER ↔ input ∈ GeneralCLIQUE := by
  cases hdecode : decodeCliqueInstance input with
  | none =>
      have hsource : input ∉ GeneralCLIQUE :=
        not_mem_generalCLIQUE_of_decode_none hdecode
      have hmap : cliqueToVertexCoverMap input =
          encodeVertexCoverInstance canonicalVertexCoverNoInstance := by
        simp [cliqueToVertexCoverMap, hdecode]
      rw [hmap]
      exact iff_of_false canonicalVertexCoverNoInstance_not_mem hsource
  | some I =>
      by_cases hI : I.WellFormed
      · have hmap : cliqueToVertexCoverMap input =
            encodeVertexCoverInstance I.complementForVertexCover := by
          simp [cliqueToVertexCoverMap, hdecode, hI]
        rw [hmap, encodeVertexCoverInstance_mem_generalVERTEXCOVER_iff]
        have hcomplementWellFormed := I.complementForVertexCover_wellFormed hI
        rw [and_iff_right hcomplementWellFormed]
        rw [← I.hasClique_iff_complement_hasVertexCover hI]
        simp [GeneralCLIQUE, hdecode, hI]
      · have hsource : input ∉ GeneralCLIQUE := by
          simp [GeneralCLIQUE, hdecode, hI]
        have hmap : cliqueToVertexCoverMap input =
            encodeVertexCoverInstance canonicalVertexCoverNoInstance := by
          simp [cliqueToVertexCoverMap, hdecode, hI]
        rw [hmap]
        exact iff_of_false canonicalVertexCoverNoInstance_not_mem hsource

end Chapter34
end CLRS
