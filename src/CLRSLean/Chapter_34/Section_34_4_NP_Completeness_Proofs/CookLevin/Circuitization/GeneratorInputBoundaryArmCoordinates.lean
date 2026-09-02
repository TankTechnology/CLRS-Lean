import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorBoundaryStarts

/-!
# Arithmetic coordinates of verifier-input arms

This module removes proof-carrying row and separator builders from the source
wire list of every candidate-length conjunction.  The resulting four blocks
depend only on fixed machine constants, the raw word, its length, and the arm
ordinal.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Pure arithmetic wire list consumed by one candidate-length conjunction. -/
def verifierInputArmArithmeticWires
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) : List Nat :=
  let tm := W.machine.tm
  let H := (verifierHeight W).eval input.length
  let width := (reachableAlphabet tm tm.k₀).card + 1
  [1 + (labelCount tm + 1) + stateCount tm +
      cfgStackBitOffset tm H tm.k₀ + (arm.val + 1 + input.length)] ++
    List.ofFn (fun prefixIndex : Fin arm.val =>
      (verifierInitialBoundaryEndPolynomial W).eval input.length +
        prefixIndex.val) ++
    [1 + (labelCount tm + 1) + stateCount tm +
      cfgStackBitOffset tm H tm.k₀ +
        ((H + 1) + ((verifierInputCode W none).val + width * arm.val))] ++
    List.ofFn (fun index : Fin input.length =>
      1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H tm.k₀ +
          ((H + 1) +
            ((verifierInputCode W (some (input.get index))).val +
              width * (arm.val + 1 + index.val))))

/-- Closed first-row formula for a public-input stack height coordinate. -/
theorem verifierFirstRowInputStackHeightWire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (index : Fin ((verifierHeight W).eval input.length + 1)) :
    (((verifierRows W input).rows (verifierFirstRow _)).stack
      W.machine.tm.k₀).height index =
      1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
        cfgStackBitOffset W.machine.tm
          ((verifierHeight W).eval input.length) W.machine.tm.k₀ + index.val := by
  change (verifierRows W input).rows (verifierFirstRow _)
      (CfgSlot.stackHeight W.machine.tm.k₀ index) = _
  rw [verifierRowStackHeightWire_eq]
  simp [verifierFirstRow]

/-- Closed first-row formula for a public-input stack cell coordinate. -/
theorem verifierFirstRowInputStackCellWire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ)
    (cell : Fin ((verifierHeight W).eval input.length))
    (symbol : Fin
      ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1)) :
    (((verifierRows W input).rows (verifierFirstRow _)).stack
      W.machine.tm.k₀).cell cell symbol =
      1 + (labelCount W.machine.tm + 1) + stateCount W.machine.tm +
        cfgStackBitOffset W.machine.tm
          ((verifierHeight W).eval input.length) W.machine.tm.k₀ +
        (((verifierHeight W).eval input.length + 1) +
          (symbol.val +
            ((reachableAlphabet W.machine.tm W.machine.tm.k₀).card + 1) *
              cell.val)) := by
  change (verifierRows W input).rows (verifierFirstRow _)
      (CfgSlot.stackCell W.machine.tm.k₀ cell symbol) = _
  rw [verifierRowStackCellWire_eq]
  simp [verifierFirstRow]

/-- The semantic first-row stack and freshly built separator NOTs yield
exactly the pure arithmetic arm coordinates. -/
theorem verifierInputArmWires_eq_arithmetic
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
    VerifierInput.inputArmWires W ((verifierHeight W).eval input.length)
        input (row.stack W.machine.tm.k₀) separatorNots.wires arm.val
        (verifierInputArm_fits W input arm) =
      verifierInputArmArithmeticWires W input arm := by
  dsimp only
  unfold VerifierInput.inputArmWires verifierInputArmArithmeticWires
  rw [verifierFirstRowInputStackHeightWire_eq]
  simp_rw [VerifierInput.buildSeparatorNots_wires_eq]
  rw [verifierInitialBoundaryEndPolynomial_eval_eq_builder]
  simp_rw [verifierFirstRowInputStackCellWire_eq]

end CLRS.Chapter34.Turing.CookLevin
