import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Language
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.VertexCover.Language

/-!
# Total raw VERTEX-COVER-to-HAM-CYCLE reduction

This module lifts the typed CLRS edge-gadget construction to the shared raw
graph grammar.  Complete well-formed source instances use the construction;
parser failures and decoded ill-formed instances use one fixed HAM-CYCLE
no-instance.  The resulting map preserves membership on every raw word.

Main results:

- Theorem `vertexCoverToHamiltonianMap_mem_HAMCYCLE_iff`: exact all-input
  language semantics of the total raw reduction.
-/

namespace CLRS.Chapter34

open HamiltonianCycleReduction

/-- The fixed three-vertex path encoding is outside HAM-CYCLE. -/
theorem canonicalHamiltonianNoInstance_not_mem_HAMCYCLE :
    encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance ∉
      (HAMCYCLE : Language HamiltonianCycleSym) := by
  rw [encodeHamiltonianCycleInstance_mem_iff]
  exact fun h =>
    not_canonicalHamiltonianNoInstance_hasHamiltonianCycle h.2.2

/-- Every branch of the total typed reduction uses the graph-only HAM-CYCLE
header convention `targetSize = vertexCount`. -/
theorem vertexCoverToHamiltonianInstance_target_eq_vertexCount
    (I : VertexCoverInstance) :
    (vertexCoverToHamiltonianInstance I).targetSize =
      (vertexCoverToHamiltonianInstance I).vertexCount := by
  simp only [vertexCoverToHamiltonianInstance]
  split
  · rfl
  · split
    · rfl
    · exact clrsHamiltonianInstance_target_eq_vertexCount I

/-- Decode a raw VERTEX-COVER instance, apply the typed CLRS construction when
the source is well formed, and otherwise emit the fixed HAM-CYCLE no-instance. -/
def vertexCoverToHamiltonianMap
    (input : List VertexCoverSym) : List HamiltonianCycleSym :=
  match decodeVertexCoverInstance input with
  | some I =>
      if I.WellFormed then
        encodeHamiltonianCycleInstance (vertexCoverToHamiltonianInstance I)
      else
        encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance
  | none => encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance

/-- The total raw CLRS construction preserves membership on parser failures,
ill-formed decoded graphs, degenerate instances, and ordinary instances. -/
theorem vertexCoverToHamiltonianMap_mem_HAMCYCLE_iff
    (input : List VertexCoverSym) :
    vertexCoverToHamiltonianMap input ∈
        (HAMCYCLE : Language HamiltonianCycleSym) ↔
      input ∈ (VERTEXCOVER : Language VertexCoverSym) := by
  cases hdecode : decodeVertexCoverInstance input with
  | none =>
      have hsource : input ∉ VERTEXCOVER :=
        not_mem_generalVERTEXCOVER_of_decode_none hdecode
      have hmap : vertexCoverToHamiltonianMap input =
          encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance := by
        simp [vertexCoverToHamiltonianMap, hdecode]
      rw [hmap]
      exact iff_of_false canonicalHamiltonianNoInstance_not_mem_HAMCYCLE hsource
  | some I =>
      by_cases hI : I.WellFormed
      · have hmap : vertexCoverToHamiltonianMap input =
            encodeHamiltonianCycleInstance
              (vertexCoverToHamiltonianInstance I) := by
          simp [vertexCoverToHamiltonianMap, hdecode, hI]
        rw [hmap, encodeHamiltonianCycleInstance_mem_iff]
        have htarget :=
          vertexCoverToHamiltonianInstance_target_eq_vertexCount I
        have htargetWellFormed :=
          vertexCoverToHamiltonianInstance_wellFormed I
        rw [and_iff_right htargetWellFormed, and_iff_right htarget]
        rw [← vertexCoverToHamiltonianInstance_correct hI]
        simp [GeneralVERTEXCOVER, hdecode, hI]
      · have hsource : input ∉ VERTEXCOVER := by
          simp [GeneralVERTEXCOVER, hdecode, hI]
        have hmap : vertexCoverToHamiltonianMap input =
            encodeHamiltonianCycleInstance canonicalHamiltonianNoInstance := by
          simp [vertexCoverToHamiltonianMap, hdecode, hI]
        rw [hmap]
        exact iff_of_false canonicalHamiltonianNoInstance_not_mem_HAMCYCLE hsource

end CLRS.Chapter34
