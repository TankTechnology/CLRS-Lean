import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryEndSource

/-!
# Static branch selection for the accepting boundary

The verifier requests the one-symbol Boolean output `true`, while the
published tableau height is always at least one.  Consequently the apparent
input-dependent admissibility test in the accepting constructor is exactly
one machine-static alphabet-membership proposition.  It can therefore be
resolved once when the fixed reduction machine is built.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- The fixed output-tape symbol representing Boolean acceptance. -/
def verifierAcceptingSymbol
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    W.machine.tm.Γ W.machine.tm.k₁ :=
  W.machine.outputAlphabet.invFun true

@[simp] theorem verifierAcceptingOutput_eq_singleton
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    verifierAcceptingOutput W = [verifierAcceptingSymbol W] := by
  rfl

/-- Every published verifier tableau has room for the one-symbol output. -/
theorem verifierHeight_one_le
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    1 ≤ (verifierHeight W).eval n := by
  have hpadding := verifierHeight_actionPadding_le W n
  omega

/-- Admissibility of the accepting target is independent of the raw input. -/
theorem verifierAcceptingOutputFits_iff
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    AcceptingOutputFits W.machine.tm
        ((verifierHeight W).eval input.length)
        (verifierAcceptingOutput W) ↔
      verifierAcceptingSymbol W ∈
        reachableAlphabet W.machine.tm W.machine.tm.k₁ := by
  rw [verifierAcceptingOutput_eq_singleton]
  unfold AcceptingOutputFits
  constructor
  · intro hfit
    exact hfit.1 (verifierAcceptingSymbol W) (by simp)
  · intro hmember
    refine ⟨?_, ?_⟩
    ·
      intro symbol hsymbol
      have heq : symbol = verifierAcceptingSymbol W := by
        simpa only [List.mem_singleton] using hsymbol
      simpa [heq] using hmember
    · simpa using verifierHeight_one_le W input.length

/-- Canonical admissibility witness reconstructed from the static symbol
membership fact. -/
theorem verifierAcceptingOutputFitsOfSymbol
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁) :
    AcceptingOutputFits W.machine.tm
      ((verifierHeight W).eval input.length)
      (verifierAcceptingOutput W) :=
  (verifierAcceptingOutputFits_iff W input).2 hmember

/-- In the static negative case the canonical accepting operand is `none`
for every raw input. -/
theorem compileVerifierAcceptingBoundaryFrames_eq_none
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmissing : verifierAcceptingSymbol W ∉
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    compileVerifierAcceptingBoundaryFrames W input = none := by
  classical
  unfold compileVerifierAcceptingBoundaryFrames
  rw [dif_neg]
  exact (verifierAcceptingOutputFits_iff W input).not.mpr hmissing

/-- In the static positive case the canonical accepting operand is always
the complete-row equality family, with the canonical fit witness. -/
theorem compileVerifierAcceptingBoundaryFrames_eq_some
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    compileVerifierAcceptingBoundaryFrames W input =
      some (affineEqFinCanonicalFrames
        (verifierInputBoundary W input).builder.gates.length
        (cfgBitCount W.machine.tm
          ((verifierHeight W).eval input.length))
        (fun i =>
          (verifierRows W input).rows
            (Fin.last ((verifierHorizon W).eval input.length))
            ((cfgSlotEquivFin W.machine.tm
              ((verifierHeight W).eval input.length)).symm i))
        (fun i => verifierAcceptingTargetWires W input
          (verifierAcceptingOutputFitsOfSymbol W input hmember)
          ((cfgSlotEquivFin W.machine.tm
            ((verifierHeight W).eval input.length)).symm i))) := by
  classical
  unfold compileVerifierAcceptingBoundaryFrames
  rw [dif_pos (verifierAcceptingOutputFitsOfSymbol W input hmember)]

/-- The semantic accepting-boundary start is the independently generated
input-boundary endpoint. -/
theorem verifierAcceptingBoundary_start_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundary W input).builder.gates.length =
      verifierInputBoundaryEnd W input :=
  verifierInputBoundary_gates_length_eq_end W input

end CLRS.Chapter34.Turing.CookLevin
