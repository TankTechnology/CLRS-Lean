import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.BidirectionalSemantics
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Language
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Encoding

/-!
# Total raw VERTEX-COVER-to-CLIQUE semantic reduction

Well-formed graph strings are sent to their deterministic complement.  Every
malformed or decoded-but-ill-formed input is sent to the existing fixed
well-formed CLIQUE no-instance.
-/

namespace CLRS
namespace Chapter34

/-- The canonical encoding of the shared fixed CLIQUE no-instance lies
outside the honest general CLIQUE language. -/
theorem noCliqueInstance_not_mem_generalCLIQUE :
    encodeCliqueInstance noCliqueInstance ∉ GeneralCLIQUE := by
  rw [encodeCliqueInstance_mem_generalCLIQUE_iff]
  exact fun h => noCliqueInstance_not_hasClique h.2

/-- Decode the shared graph grammar, complement a well-formed VERTEX-COVER
instance, and send every other input to the canonical CLIQUE no-instance. -/
def vertexCoverToCliqueMap (input : List VertexCoverSym) : List CliqueSym :=
  match decodeVertexCoverInstance input with
  | some I =>
      if I.WellFormed then
        encodeCliqueInstance I.complementForVertexCover
      else
        encodeCliqueInstance noCliqueInstance
  | none => encodeCliqueInstance noCliqueInstance

/-- The total reverse map preserves membership on every raw input string. -/
theorem vertexCoverToCliqueMap_mem_CLIQUE_iff
    (input : List VertexCoverSym) :
    vertexCoverToCliqueMap input ∈ GeneralCLIQUE ↔
      input ∈ VERTEXCOVER := by
  cases hdecode : decodeVertexCoverInstance input with
  | none =>
      have hsource : input ∉ VERTEXCOVER :=
        not_mem_generalVERTEXCOVER_of_decode_none hdecode
      have hmap : vertexCoverToCliqueMap input =
          encodeCliqueInstance noCliqueInstance := by
        simp [vertexCoverToCliqueMap, hdecode]
      rw [hmap]
      exact iff_of_false noCliqueInstance_not_mem_generalCLIQUE hsource
  | some I =>
      by_cases hI : I.WellFormed
      · have hmap : vertexCoverToCliqueMap input =
            encodeCliqueInstance I.complementForVertexCover := by
          simp [vertexCoverToCliqueMap, hdecode, hI]
        rw [hmap, encodeCliqueInstance_mem_generalCLIQUE_iff]
        have hcomplementWellFormed := I.complementForVertexCover_wellFormed hI
        rw [and_iff_right hcomplementWellFormed]
        rw [← I.hasVertexCover_iff_complement_hasClique hI]
        simp [GeneralVERTEXCOVER, hdecode, hI]
      · have hsource : input ∉ VERTEXCOVER := by
          simp [GeneralVERTEXCOVER, hdecode, hI]
        have hmap : vertexCoverToCliqueMap input =
            encodeCliqueInstance noCliqueInstance := by
          simp [vertexCoverToCliqueMap, hdecode, hI]
        rw [hmap]
        exact iff_of_false noCliqueInstance_not_mem_generalCLIQUE hsource

end Chapter34
end CLRS
