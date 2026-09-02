import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding

/-!
# The honest serialized general CLIQUE language

The language accepts exactly complete decodings of well-formed finite graphs
that contain a clique of the explicitly encoded target size.  Malformed and
decoded-but-ill-formed strings are no-instances.
-/

namespace CLRS
namespace Chapter34

/-! ## Raw language and typed bridge -/

/-- General graph-plus-{lit}`k` CLIQUE over the unique {lit}`CliqueSym` grammar. -/
def GeneralCLIQUE : Language CliqueSym :=
  { input |
      ∃ I, decodeCliqueInstance input = some I ∧ I.WellFormed ∧ I.HasClique }

/-- Exact raw-string membership characterization for general CLIQUE. -/
theorem mem_generalCLIQUE_iff (input : List CliqueSym) :
    input ∈ GeneralCLIQUE ↔
      ∃ I, decodeCliqueInstance input = some I ∧ I.WellFormed ∧ I.HasClique := by
  rfl

/-- A canonical instance encoding belongs to general CLIQUE exactly when the
underlying graph representation is well formed and has the requested clique. -/
theorem encodeCliqueInstance_mem_generalCLIQUE_iff (I : CliqueInstance) :
    encodeCliqueInstance I ∈ GeneralCLIQUE ↔ I.WellFormed ∧ I.HasClique := by
  simp [GeneralCLIQUE, decode_encodeCliqueInstance]

/-- A string rejected by the complete instance parser is outside general
CLIQUE. -/
theorem not_mem_generalCLIQUE_of_decode_none {input : List CliqueSym}
    (hdecode : decodeCliqueInstance input = none) : input ∉ GeneralCLIQUE := by
  simp [GeneralCLIQUE, hdecode]

end Chapter34
end CLRS
