import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmCoordinates

/-!
# Closed runtime frames of verifier-input arms

This module closes the remaining builder-dependent field of every input-arm
frame.  Its start is the separator endpoint plus the exact cumulative cost of
the preceding candidate lengths, while its wires are the arithmetic
coordinates established in the preceding module.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Exact gate cost of all candidate-length arms preceding `length`.  This is
pure arithmetic: no circuit builder occurs in the definition. -/
def verifierInputArmPrefixCost
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (inputLength length : Nat) : Nat :=
  ∑ previous : Fin length,
    verifierInputArmGateCost ((verifierHeight W).eval inputLength)
      inputLength previous.val

/-- Pure runtime conjunction frame at one candidate certificate length. -/
def verifierInputArmArithmeticFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    AffineConjunctionFrame :=
  { start := (verifierInputArmsStartPolynomial W).eval input.length +
      verifierInputArmPrefixCost W input.length arm.val
    wires := verifierInputArmArithmeticWires W input arm }

/-- At an actual verifier word, the semantic recursive builder reaches one
arm at exactly its closed arithmetic start. -/
theorem verifierInputArmBuilderStart_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    let rows := verifierRows W input
    let pool := verifierPool W input
    let validity := verifierValidity W input
    let transitions := verifierTransitions W input
    let initial := verifierInitialBoundary W input
    let extension := pool.extension.trans (validity.extension.trans
      (transitions.extension.trans initial.extension))
    let row := rows.rows (verifierFirstRow _)
    let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
    let separatorNots := VerifierInput.buildSeparatorNots initial.builder
      (row.stack W.machine.tm.k₀) (hrow.stack _)
      (verifierInputCode W none)
    let pool' := (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans initial.extension))).mono
        separatorNots.extension
    let hstack' := (hrow.stack W.machine.tm.k₀).mono
      separatorNots.extension
    let hseparatorEval := fun inputs cell => by
      rw [separatorNots.eval, separatorNots.extension.evalWire_eq inputs
        ((hrow.stack W.machine.tm.k₀).cell cell
          (verifierInputCode W none))]
    (VerifierInput.buildInputArms W
      ((verifierHeight W).eval input.length) input separatorNots.builder
      pool' (row.stack W.machine.tm.k₀) hstack' separatorNots.wires
      separatorNots.valid hseparatorEval arm.val).builder.gates.length =
        (verifierInputArmsStartPolynomial W).eval input.length +
          verifierInputArmPrefixCost W input.length arm.val := by
  dsimp only
  rw [VerifierInput.InputArmsResult.gate_delta]
  rw [verifierInputArmsStartPolynomial_eval_eq_separatorBuilder]
  rfl

/-- The complete semantic arm-frame family is pointwise the pure arithmetic
family.  In particular every optional entry is present and no proof-carrying
builder remains in its runtime representation. -/
theorem verifierInputBoundaryScript_armFrames_eq_arithmetic
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundaryScript W input).armFrames =
      List.ofFn fun arm :
          Fin (W.certificateBound.eval input.length + 1) =>
        some (verifierInputArmArithmeticFrame W input arm) := by
  unfold verifierInputBoundaryScript compileVerifierInputShapeScript
  dsimp only
  rw [VerifierInput.compileInputArmFrames_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext arm
  unfold VerifierInput.compileInputArmEntry
  rw [dif_pos (verifierInputArm_fits W input arm)]
  unfold verifierInputArmArithmeticFrame
  dsimp only
  congr 1
  congr 1
  · exact verifierInputArmBuilderStart_eq W input arm
  · exact verifierInputArmWires_eq_arithmetic W input arm

end CLRS.Chapter34.Turing.CookLevin
