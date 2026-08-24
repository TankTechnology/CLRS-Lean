import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.MainTheorem
import CLRSLean.Chapter_34.Section_34_3_NP_Completeness_And_Reducibility.Hardness

/-! # General CIRCUIT-SAT to SAT: many-one reduction -/

namespace CLRS.Chapter34

/-- The direct consistency-formula construction is a genuine polynomial-time
many-one reduction on the honest raw languages. -/
theorem generalCircuitSAT_reducible_to_SAT :
    PolyTimeReducible GeneralCircuitSAT SAT := by
  refine ⟨generalCircuitToSATMap,
    ⟨Turing.GeneralCircuitToSAT.computableInPolyTime⟩, ?_⟩
  intro input
  exact (generalCircuitToSATMap_mem_SAT_iff input).symm

/-- SAT is NP-hard, obtained directly from the completed Cook--Levin target
and the verified general-circuit-to-formula machine. -/
theorem SAT_npHard : NPHard SAT :=
  NPHard.of_reducible Turing.CookLevin.generalCircuitSAT_npHard
    generalCircuitSAT_reducible_to_SAT

end CLRS.Chapter34
