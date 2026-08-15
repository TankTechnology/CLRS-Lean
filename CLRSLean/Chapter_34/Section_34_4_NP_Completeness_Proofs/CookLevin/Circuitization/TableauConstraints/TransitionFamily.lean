import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits

/-!
# Cook--Levin whole-tableau transition family

This module serializes the verified local transition circuit across every
adjacent pair in a finite public tableau.  It introduces neither boundary
constraints nor a final conjunction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Proof-carrying result of serializing the local transition circuit across
the adjacent pairs in an already allocated finite row family. -/
structure TransitionCircuitFamilyResult (tm : _root_.Turing.FinTM2) (H T : Nat)
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H) where
  /-- Builder after all adjacent-row transition circuits. -/
  builder : CircuitBuilder
  /-- One transition output for each adjacent pair. -/
  outputs : Fin T → CircuitBuilder.Wire
  /-- The complete public-row prefix is preserved. -/
  extension : base.Extends builder
  /-- Every transition output belongs to the common final builder. -/
  outputsValid : ∀ step, builder.WireValid (outputs step)
  /-- Exactly one local transition cost is paid per adjacent pair. -/
  gate_delta : builder.gates.length =
    base.gates.length + T * transitionCircuitGateCost tm H
  /-- Each output has the local stuttering-step semantics for any successfully
  decoded adjacent public rows. -/
  eval : ∀ (inputs : Nat → Bool) (step : Fin T) {current next : tm.Cfg}
      (hcurrent : (rows step.castSucc).ValidIn base)
      (hnext : (rows step.succ).ValidIn base),
      evalBundle base inputs (rows step.castSucc) hcurrent = some current →
      evalBundle base inputs (rows step.succ) hnext = some next →
      (builder.evalWire inputs (outputs step) = true ↔
        next = stutterStep tm current)

private def buildTransitionCircuitFamily
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder) :
    (T : Nat) → (rows : Fin (T + 1) → CfgWires tm H) →
      (∀ row, (rows row).ValidIn base) →
      TransitionCircuitFamilyResult tm H T base rows
  | 0, rows, _ =>
      { builder := base
        outputs := fun step => Fin.elim0 step
        extension := CircuitBuilder.Extends.refl base
        outputsValid := fun step => Fin.elim0 step
        gate_delta := by simp
        eval := fun _ step => Fin.elim0 step }
  | T + 1, rows, hrows => by
      let prefixRows : Fin (T + 1) → CfgWires tm H :=
        fun row => rows row.castSucc
      let previous := buildTransitionCircuitFamily tm H base T prefixRows
        (fun row => hrows row.castSucc)
      let currentRow : Fin (T + 2) := (Fin.last T).castSucc
      let nextRow : Fin (T + 2) := Fin.last (T + 1)
      have hcurrent : (rows currentRow).ValidIn previous.builder :=
        (hrows currentRow).mono previous.extension
      have hnext : (rows nextRow).ValidIn previous.builder :=
        (hrows nextRow).mono previous.extension
      let last := transitionCircuit tm H previous.builder
        (rows currentRow) (rows nextRow) hcurrent hnext
      let outputs : Fin (T + 1) → CircuitBuilder.Wire := fun step =>
        if hstep : step.val < T then previous.outputs ⟨step.val, hstep⟩
        else last.wire
      refine
        { builder := last.builder
          outputs := outputs
          extension := previous.extension.trans last.extension
          outputsValid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro step
        simp only [outputs]
        split
        next hstep =>
          exact last.extension.wireValid
            (previous.outputsValid ⟨step.val, hstep⟩)
        next => exact last.valid
      · rw [last.gate_delta, previous.gate_delta]
        ring
      · intro inputs step current next hcurrentBase hnextBase
          hcurrentDecoded hnextDecoded
        simp only [outputs]
        split
        next hstep =>
          let oldStep : Fin T := ⟨step.val, hstep⟩
          have hindex : oldStep.castSucc = step := by
            apply Fin.ext
            rfl
          rw [last.extension.evalWire_eq inputs
            (previous.outputsValid oldStep)]
          have hsemantic := previous.eval inputs oldStep hcurrentBase hnextBase
            hcurrentDecoded hnextDecoded
          simpa only [prefixRows, hindex] using hsemantic
        next hstep =>
          have hlastStep : step = Fin.last T := by
            apply Fin.ext
            simp
            omega
          subst step
          have hnextIndex : (Fin.last T).succ = nextRow := by
            apply Fin.ext
            rfl
          have hcurrentBase' :
              evalBundle base inputs (rows currentRow) (hrows currentRow) =
                some current := by
            simpa only [currentRow] using hcurrentDecoded
          have hnextBase' :
              evalBundle base inputs (rows nextRow) (hrows nextRow) =
                some next := by
            rw [← hnextIndex]
            exact hnextDecoded
          have hcurrentPrevious :
              evalBundle previous.builder inputs (rows currentRow) hcurrent =
                some current := by
            rw [evalBundle_extends previous.extension inputs
              (rows currentRow) (hrows currentRow)]
            exact hcurrentBase'
          have hnextPrevious :
              evalBundle previous.builder inputs (rows nextRow) hnext =
                some next := by
            rw [evalBundle_extends previous.extension inputs
              (rows nextRow) (hrows nextRow)]
            exact hnextBase'
          exact transitionCircuit_eval_iff tm H previous.builder inputs
            (rows currentRow) (rows nextRow) hcurrent hnext
            hcurrentPrevious hnextPrevious

/-- Build one local transition output for every adjacent pair in the public
rows, serially in time order. -/
def transitionCircuitFamily
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    TransitionCircuitFamilyResult tm H T base rows :=
  buildTransitionCircuitFamily tm H base T rows hrows

/-- The empty adjacent-pair family leaves the builder unchanged. -/
@[simp] theorem transitionCircuitFamily_zero_builder
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder)
    (rows : Fin 1 → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (transitionCircuitFamily tm H base rows hrows).builder = base := by
  rfl

/-- A successor transition family is its prefix family followed by the final
adjacent-row local transition circuit. -/
theorem transitionCircuitFamily_succ_builder
    (tm : _root_.Turing.FinTM2) (H : Nat) (base : CircuitBuilder)
    (T : Nat) (rows : Fin (T + 2) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    let prefixRows : Fin (T + 1) → CfgWires tm H :=
      fun row => rows row.castSucc
    let previous := transitionCircuitFamily tm H base prefixRows
      (fun row => hrows row.castSucc)
    let currentRow : Fin (T + 2) := (Fin.last T).castSucc
    let nextRow : Fin (T + 2) := Fin.last (T + 1)
    let hcurrent : (rows currentRow).ValidIn previous.builder :=
      (hrows currentRow).mono previous.extension
    let hnext : (rows nextRow).ValidIn previous.builder :=
      (hrows nextRow).mono previous.extension
    (transitionCircuitFamily tm H base rows hrows).builder =
      (transitionCircuit tm H previous.builder (rows currentRow)
        (rows nextRow) hcurrent hnext).builder := by
  rfl

/-- Serial transition construction preserves the original builder. -/
theorem transitionCircuitFamily_extends
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    base.Extends (transitionCircuitFamily tm H base rows hrows).builder :=
  (transitionCircuitFamily tm H base rows hrows).extension

/-- Every serial transition output belongs to the common final builder. -/
theorem transitionCircuitFamily_outputs_valid
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) (step : Fin T) :
    (transitionCircuitFamily tm H base rows hrows).builder.WireValid
      ((transitionCircuitFamily tm H base rows hrows).outputs step) :=
  (transitionCircuitFamily tm H base rows hrows).outputsValid step

/-- Serial transition construction pays exactly the local transition cost once
per adjacent pair. -/
theorem transitionCircuitFamily_gate_delta
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (transitionCircuitFamily tm H base rows hrows).builder.gates.length =
      base.gates.length + T * transitionCircuitGateCost tm H :=
  (transitionCircuitFamily tm H base rows hrows).gate_delta

/-- Every old row has the same complete bit evaluation after all transition
circuits have been appended. -/
theorem transitionCircuitFamily_evalCfgBits
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (inputs : Nat → Bool) (row : Fin (T + 1)) :
    evalCfgBits (transitionCircuitFamily tm H base rows hrows).builder inputs
        (rows row) = evalCfgBits base inputs (rows row) :=
  evalCfgBits_extends (transitionCircuitFamily tm H base rows hrows).extension
    inputs (rows row) (hrows row)

/-- Successful decoding of every old row is stable after all transition
circuits have been appended. -/
theorem transitionCircuitFamily_evalBundle
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (inputs : Nat → Bool) (row : Fin (T + 1)) :
    evalBundle (transitionCircuitFamily tm H base rows hrows).builder inputs
        (rows row)
        ((hrows row).mono
          (transitionCircuitFamily tm H base rows hrows).extension) =
      evalBundle base inputs (rows row) (hrows row) :=
  evalBundle_extends (transitionCircuitFamily tm H base rows hrows).extension
    inputs (rows row) (hrows row)

/-- A transition-family output is true exactly when the decoded next row is
the total stuttering successor of the decoded current row. -/
theorem transitionCircuitFamily_eval_iff
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (inputs : Nat → Bool) (configs : Fin (T + 1) → tm.Cfg)
    (hdecoded : ∀ row,
      evalBundle base inputs (rows row) (hrows row) = some (configs row))
    (step : Fin T) :
    (transitionCircuitFamily tm H base rows hrows).builder.evalWire inputs
        ((transitionCircuitFamily tm H base rows hrows).outputs step) = true ↔
      configs step.succ = stutterStep tm (configs step.castSucc) := by
  exact (transitionCircuitFamily tm H base rows hrows).eval inputs step
    (hrows step.castSucc) (hrows step.succ)
    (hdecoded step.castSucc) (hdecoded step.succ)

/-- Serial transition construction is independent of the supplied row-validity
proof. -/
theorem transitionCircuitFamily_proof_irrel
    (tm : _root_.Turing.FinTM2) (H : Nat) {T : Nat}
    (base : CircuitBuilder) (rows : Fin (T + 1) → CfgWires tm H)
    (hrows₁ hrows₂ : ∀ row, (rows row).ValidIn base) :
    transitionCircuitFamily tm H base rows hrows₁ =
      transitionCircuitFamily tm H base rows hrows₂ := by
  congr

end

end CLRS.Chapter34.Turing.CookLevin
