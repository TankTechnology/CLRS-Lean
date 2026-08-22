import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.Normalize
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToCliqueMachine

/-!
# Canonical occurrence-descriptor stream

The existing linear occurrence relabeler is reused after raw CNF
normalization.  The resulting stream contains an explicit `vertexMark` before
each decoded literal and retains clause boundaries, polarity, and unary
variable indices.  It is the canonical machine input for the later numeric
edge generator.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

/-- Canonical occurrence stream of the CNF decoded from an arbitrary input. -/
def canonicalOccurrenceStream (input : List CNFSym) : List GraphSym :=
  relabel (normalizeCNFInput input)

/-- Pure identification of the descriptor stream with the decoded CNF. -/
theorem canonicalOccurrenceStream_eq (input : List CNFSym) :
    canonicalOccurrenceStream input = relabel (encCNF (decodeCNF input)) := by
  simp [canonicalOccurrenceStream, normalizeCNFInput_eq_encCNF_decodeCNF]

/-- Normalization followed by occurrence marking is one composed
polynomial-time TM2. -/
noncomputable def canonicalOccurrenceStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      canonicalOccurrenceStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      normalizeCNFInput_computableInPolyTime
      cliqueComputableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => relabel (normalizeCNFInput input))
  simpa [Function.comp_def] using Classical.choice composed

end TMClique
end Turing
end Chapter34
end CLRS
