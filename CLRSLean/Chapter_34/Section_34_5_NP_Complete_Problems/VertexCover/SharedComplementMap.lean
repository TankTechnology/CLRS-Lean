import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Complement

/-!
# Shared guarded graph-complement map

The total CLIQUE-to-VERTEX-COVER and VERTEX-COVER-to-CLIQUE maps use the same
raw graph grammar and the same successful branch.  Their only difference is
the fixed no-instance emitted when parsing or well-formedness validation
fails.  This module isolates that common semantic function so a later fixed
machine can be proved correct once and specialized by its fallback constant.
-/

namespace CLRS
namespace Chapter34

/-- Parse a raw graph, validate the shared graph invariants, and encode its
deterministic complement.  Every rejected input is sent to the supplied fixed
fallback instance. -/
def guardedGraphComplementMap (fallback : CliqueInstance)
    (input : List CliqueSym) : List CliqueSym :=
  match decodeCliqueInstance input with
  | some I =>
      if I.WellFormed then
        encodeCliqueInstance I.complementForVertexCover
      else
        encodeCliqueInstance fallback
  | none => encodeCliqueInstance fallback

/-- A successful well-formed decoding selects the complement branch. -/
theorem guardedGraphComplementMap_of_decode_wellFormed
    {fallback I : CliqueInstance} {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = some I)
    (hI : I.WellFormed) :
    guardedGraphComplementMap fallback input =
      encodeCliqueInstance I.complementForVertexCover := by
  simp [guardedGraphComplementMap, hdecode, hI]

/-- A decoded but ill-formed graph selects the supplied fallback. -/
theorem guardedGraphComplementMap_of_decode_not_wellFormed
    {fallback I : CliqueInstance} {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = some I)
    (hI : ¬I.WellFormed) :
    guardedGraphComplementMap fallback input =
      encodeCliqueInstance fallback := by
  simp [guardedGraphComplementMap, hdecode, hI]

/-- Parser failure selects the supplied fallback. -/
theorem guardedGraphComplementMap_of_decode_none
    {fallback : CliqueInstance} {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = none) :
    guardedGraphComplementMap fallback input =
      encodeCliqueInstance fallback := by
  simp [guardedGraphComplementMap, hdecode]

end Chapter34
end CLRS
