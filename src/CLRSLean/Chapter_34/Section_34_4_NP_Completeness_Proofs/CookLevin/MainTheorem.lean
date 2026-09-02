import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Textbook
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorCompleteCircuitCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.NP

/-!
# The Cook--Levin main theorem

This module closes the textbook semantic circuitization with the concrete
raw-input compiler.  The resulting explicit map is a genuine polynomial-time
many-one reduction, yielding NP-hardness and NP-completeness of the honest
serialized general-circuit satisfiability language.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- The concrete Cook--Levin map is a polynomial-time many-one reduction for
every normalized verifier witness. -/
theorem cookLevin_polyTimeReducible
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    PolyTimeReducible L GeneralCircuitSAT :=
  cookLevin_polyTimeReducible_of_computable W
    (cookLevinMap_polyTimeComputable W)

/-- **Cook--Levin theorem.** Every polynomially verifiable language reduces
in polynomial time to general Boolean-circuit satisfiability. -/
theorem cookLevin_theorem {Γ : Type} {L : Language Γ}
    (hL : PolyTimeVerifiable L) :
    PolyTimeReducible L GeneralCircuitSAT :=
  cookLevin_polyTimeReducible (VerifierWitness.ofPolyTimeVerifiable hL)

/-- General circuit satisfiability is NP-hard. -/
theorem generalCircuitSAT_npHard : NPHard GeneralCircuitSAT := by
  intro Γ L hL
  exact cookLevin_theorem hL

/-- General circuit satisfiability is NP-complete. -/
theorem generalCircuitSAT_npComplete : NPComplete GeneralCircuitSAT :=
  ⟨generalCircuitSAT_polyTimeVerifiable, generalCircuitSAT_npHard⟩

end

end CLRS.Chapter34.Turing.CookLevin
