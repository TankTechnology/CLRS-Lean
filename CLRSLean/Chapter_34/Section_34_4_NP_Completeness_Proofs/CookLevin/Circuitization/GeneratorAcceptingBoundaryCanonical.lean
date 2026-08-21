import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundarySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotEnumeration
import Mathlib.Tactic

/-!
# Builder-free canonical accepting frames

This module removes the proof-carrying builder coordinates from the positive
accepting branch.  The old semantic equality family is identified with the
explicit public-slot order, the independently generated input-boundary end,
and the polynomial first wire of the last tableau row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Canonical accepting equality frame attached to one public row slot. -/
def verifierAcceptingSlotFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ)
    (slot : CfgSlot W.machine.tm ((verifierHeight W).eval input.length)) :
    AffineEqFinPairFrame :=
  let coordinate :=
    (cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval input.length) slot).val
  let previous := verifierInputBoundaryEnd W input + 6 * coordinate
  { eqStart := previous + 1
    left := (verifierLastRowStartPolynomial W).eval input.length + coordinate
    right := verifierAcceptingTargetWires W input
      (verifierAcceptingOutputFitsOfSymbol W input hmember) slot
    matched := previous + 5
    previous := previous }

/-- The semantic positive-branch canonical family is exactly the explicit
public-slot map with no remaining builder-derived start or row wire. -/
theorem verifierAcceptingCanonicalFrames_eq_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    affineEqFinCanonicalFrames
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
            ((verifierHeight W).eval input.length)).symm i)) =
      (transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierAcceptingSlotFrame W hmember input) := by
  rw [affineEqFinCanonicalFrames_eq_ofFn]
  rw [transitionEqPublicSlots_eq_canonical, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext coordinate
  unfold verifierAcceptingSlotFrame
  rw [verifierInputBoundary_gates_length_eq_end]
  rw [verifierRowWire_eq]
  simp only [verifierLastRowStartPolynomial_eval]
  simp
  omega

/-- The actual optional accepting operand selects precisely the explicit
slot-map family in the static positive case. -/
theorem compileVerifierAcceptingBoundaryFrames_eq_some_slotFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁)
    (input : List Γ) :
    compileVerifierAcceptingBoundaryFrames W input =
      some ((transitionEqPublicSlots W.machine.tm
        ((verifierHeight W).eval input.length)).map
          (verifierAcceptingSlotFrame W hmember input)) := by
  rw [compileVerifierAcceptingBoundaryFrames_eq_some W hmember input]
  rw [verifierAcceptingCanonicalFrames_eq_slotFrames W hmember input]

end CLRS.Chapter34.Turing.CookLevin
