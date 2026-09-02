import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.ComplementSemantics

/-!
# The honest serialized VERTEX-COVER language

VERTEX-COVER and general CLIQUE share the graph-plus-target grammar but use
different acceptance predicates.  This language accepts exactly complete
decodings of well-formed instances that have a cover of size at most the
encoded target.
-/

namespace CLRS
namespace Chapter34

/-- General graph-plus-target VERTEX-COVER over the shared `CliqueSym`
grammar. -/
def GeneralVERTEXCOVER : Language VertexCoverSym :=
  { input |
      ∃ I, decodeVertexCoverInstance input = some I ∧
        I.WellFormed ∧ I.HasVertexCover }

/-- Exact raw-string membership characterization for VERTEX-COVER. -/
theorem mem_generalVERTEXCOVER_iff (input : List VertexCoverSym) :
    input ∈ GeneralVERTEXCOVER ↔
      ∃ I, decodeVertexCoverInstance input = some I ∧
        I.WellFormed ∧ I.HasVertexCover := by
  rfl

/-- A canonical graph encoding belongs to VERTEX-COVER exactly when its typed
instance is well formed and has a sufficiently small cover. -/
theorem encodeVertexCoverInstance_mem_generalVERTEXCOVER_iff
    (I : VertexCoverInstance) :
    encodeVertexCoverInstance I ∈ GeneralVERTEXCOVER ↔
      I.WellFormed ∧ I.HasVertexCover := by
  simp [GeneralVERTEXCOVER, decode_encodeCliqueInstance]

/-- Parser rejection places a raw string outside VERTEX-COVER. -/
theorem not_mem_generalVERTEXCOVER_of_decode_none
    {input : List VertexCoverSym}
    (hdecode : decodeVertexCoverInstance input = none) :
    input ∉ GeneralVERTEXCOVER := by
  simp [GeneralVERTEXCOVER, hdecode]

/-- The textbook serialized VERTEX-COVER language. -/
abbrev VERTEXCOVER : Language VertexCoverSym := GeneralVERTEXCOVER

end Chapter34
end CLRS
