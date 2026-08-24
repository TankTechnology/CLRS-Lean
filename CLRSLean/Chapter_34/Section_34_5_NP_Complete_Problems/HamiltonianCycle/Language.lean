import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Instance
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Encoding

/-! # Honest serialized HAM-CYCLE language -/

namespace CLRS.Chapter34

/-- Canonical graph-only HAM-CYCLE instances use the shared graph encoding
with `targetSize = vertexCount`. -/
def GeneralHAMCYCLE : Language HamiltonianCycleSym :=
  { input |
      ∃ I, decodeHamiltonianCycleInstance input = some I ∧
        I.WellFormed ∧ I.targetSize = I.vertexCount ∧
        I.HasHamiltonianCycle }

theorem mem_generalHAMCYCLE_iff (input : List HamiltonianCycleSym) :
    input ∈ GeneralHAMCYCLE ↔
      ∃ I, decodeHamiltonianCycleInstance input = some I ∧
        I.WellFormed ∧ I.targetSize = I.vertexCount ∧
        I.HasHamiltonianCycle := by
  rfl

theorem encodeHamiltonianCycleInstance_mem_iff (I : HamiltonianCycleInstance) :
    encodeHamiltonianCycleInstance I ∈ GeneralHAMCYCLE ↔
      I.WellFormed ∧ I.targetSize = I.vertexCount ∧
        I.HasHamiltonianCycle := by
  constructor
  · rintro ⟨J, hdecode, hJ, htarget, hcycle⟩
    have hJI : J = I := by
      have : some J = some I := hdecode.symm.trans
        (decode_encodeCliqueInstance I)
      exact Option.some.inj this
    subst J
    exact ⟨hJ, htarget, hcycle⟩
  · rintro ⟨hI, htarget, hcycle⟩
    exact ⟨I, decode_encodeCliqueInstance I, hI, htarget, hcycle⟩

abbrev HAMCYCLE : Language HamiltonianCycleSym := GeneralHAMCYCLE

end CLRS.Chapter34
