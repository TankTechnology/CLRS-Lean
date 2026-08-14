import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity

/-!
# Cook--Levin whole-tableau validity family

This module serializes the verified one-row canonical-validity circuit across
a finite family of already allocated public rows.  It introduces neither
boundary constraints nor a final conjunction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Pure gate-order trace of canonical-validity circuits serialized across a
finite family of public tableau rows. -/
structure ValidCfgCircuitFamilyGateTrace (n : Nat) where
  gates : List CircuitGate
  outputs : Fin n → CircuitBuilder.Wire

/-- Append one exact single-row validity trace per row, in finite-index order. -/
def validCfgCircuitFamilyGateTrace
    {tm : _root_.Turing.FinTM2} {H : Nat} (start : Nat) :
    (n : Nat) → (rows : Fin n → CfgWires tm H) →
      ValidCfgCircuitFamilyGateTrace n
  | 0, _ =>
      { gates := []
        outputs := fun row => Fin.elim0 row }
  | n + 1, rows =>
      let previous := validCfgCircuitFamilyGateTrace start n
        (fun row => rows row.castSucc)
      let last := canonicalValidityGateTrace
        (start + previous.gates.length) (rows (Fin.last n))
      { gates := previous.gates ++ last.gates
        outputs := fun row =>
          if hrow : row.val < n then previous.outputs ⟨row.val, hrow⟩
          else last.wire }

/-- A family trace pays the exact canonical row-validity cost once per row. -/
@[simp] theorem validCfgCircuitFamilyGateTrace_length
    {tm : _root_.Turing.FinTM2} {H : Nat} (start n : Nat)
    (rows : Fin n → CfgWires tm H) :
    (validCfgCircuitFamilyGateTrace start n rows).gates.length =
      n * validCfgGateCost tm H := by
  induction n with
  | zero => simp [validCfgCircuitFamilyGateTrace]
  | succ n ih =>
      simp only [validCfgCircuitFamilyGateTrace, List.length_append,
        canonicalValidityGateTrace_length, ih]
      ring

/-- Proof-carrying result of serializing the canonical-validity circuit across
an already allocated finite row family. -/
structure ValidCfgCircuitFamilyResult (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (n : Nat) (rows : Fin n → CfgWires tm H) where
  /-- Builder after all row-validity circuits. -/
  builder : CircuitBuilder
  /-- One canonical-validity output per public row. -/
  outputs : Fin n → CircuitBuilder.Wire
  /-- The complete public-row prefix is preserved. -/
  extension : base.Extends builder
  /-- Every family output belongs to the final builder. -/
  outputsValid : ∀ row, builder.WireValid (outputs row)
  /-- Exactly one local validity cost is paid per row. -/
  gate_delta : builder.gates.length =
    base.gates.length + n * validCfgGateCost tm H
  /-- Each output recognizes canonical evaluated row bits in the original
  builder, even after all later family members have been appended. -/
  eval : ∀ inputs row,
    builder.evalWire inputs (outputs row) = true ↔
      (evalCfgBits base inputs (rows row)).Canonical

private def buildValidCfgCircuitFamily
    {tm : _root_.Turing.FinTM2} {H : Nat} (base : CircuitBuilder) :
    (n : Nat) → (rows : Fin n → CfgWires tm H) →
      (∀ row, (rows row).ValidIn base) →
      ValidCfgCircuitFamilyResult tm H base n rows
  | 0, rows, _ =>
      { builder := base
        outputs := fun row => Fin.elim0 row
        extension := CircuitBuilder.Extends.refl base
        outputsValid := fun row => Fin.elim0 row
        gate_delta := by simp
        eval := fun _ row => Fin.elim0 row }
  | n + 1, rows, hrows => by
      let prefixRows : Fin n → CfgWires tm H := fun row => rows row.castSucc
      let previous := buildValidCfgCircuitFamily base n prefixRows
        (fun row => hrows row.castSucc)
      have hlast : (rows (Fin.last n)).ValidIn previous.builder :=
        (hrows (Fin.last n)).mono previous.extension
      let last := validCfgCircuit previous.builder (rows (Fin.last n)) hlast
      let outputs : Fin (n + 1) → CircuitBuilder.Wire := fun row =>
        if hrow : row.val < n then previous.outputs ⟨row.val, hrow⟩
        else last.wire
      refine
        { builder := last.builder
          outputs := outputs
          extension := previous.extension.trans last.extension
          outputsValid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro row
        simp only [outputs]
        split
        next hrow =>
          exact last.extension.wireValid
            (previous.outputsValid ⟨row.val, hrow⟩)
        next => exact last.valid
      · rw [validCfgCircuit_gate_delta, previous.gate_delta]
        ring
      · intro inputs row
        simp only [outputs]
        split
        next hrow =>
          rw [last.extension.evalWire_eq inputs
            (previous.outputsValid ⟨row.val, hrow⟩)]
          rw [previous.eval]
          have hindex : (⟨row.val, hrow⟩ : Fin n).castSucc = row := by
            apply Fin.ext
            rfl
          simp only [prefixRows, hindex]
        next hrow =>
          have hlastRow : row = Fin.last n := by
            apply Fin.ext
            simp
            omega
          subst row
          rw [validCfgCircuit_eval_iff, evalBundle_isSome_iff_canonical]
          rw [evalCfgBits_extends previous.extension inputs
            (rows (Fin.last n)) (hrows (Fin.last n))]

/-- Build one canonical-validity output for every public row, serially in row
order. -/
def validCfgCircuitFamily
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    ValidCfgCircuitFamilyResult tm H base n rows :=
  buildValidCfgCircuitFamily base n rows hrows

private theorem buildValidCfgCircuitFamily_trace_eq
    {tm : _root_.Turing.FinTM2} {H : Nat} (base : CircuitBuilder)
    (n : Nat) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (buildValidCfgCircuitFamily base n rows hrows).builder.gates =
        base.gates ++
          (validCfgCircuitFamilyGateTrace base.gates.length n rows).gates ∧
      ∀ row, (buildValidCfgCircuitFamily base n rows hrows).outputs row =
        (validCfgCircuitFamilyGateTrace base.gates.length n rows).outputs row := by
  induction n with
  | zero =>
      simp [buildValidCfgCircuitFamily, validCfgCircuitFamilyGateTrace]
  | succ n ih =>
      let prefixRows : Fin n → CfgWires tm H := fun row => rows row.castSucc
      let previous := buildValidCfgCircuitFamily base n prefixRows
        (fun row => hrows row.castSucc)
      let purePrevious := validCfgCircuitFamilyGateTrace base.gates.length
        n prefixRows
      rcases ih prefixRows (fun row => hrows row.castSucc) with
        ⟨hpreviousGates, hpreviousOutputs⟩
      have hpreviousLength : previous.builder.gates.length =
          base.gates.length + purePrevious.gates.length := by
        rw [hpreviousGates]
        simp only [List.length_append]
        rfl
      have hlast : (rows (Fin.last n)).ValidIn previous.builder :=
        (hrows (Fin.last n)).mono previous.extension
      let last := validCfgCircuit previous.builder (rows (Fin.last n)) hlast
      let pureLast := canonicalValidityGateTrace
        (base.gates.length + purePrevious.gates.length) (rows (Fin.last n))
      have hlastGates : last.builder.gates =
          previous.builder.gates ++ pureLast.gates := by
        rw [validCfgCircuit_gates_eq]
        simp only [pureLast, hpreviousLength]
      have hlastWire : last.wire = pureLast.wire := by
        rw [validCfgCircuit_wire_eq_trace]
        simp only [pureLast, hpreviousLength]
      simp only [buildValidCfgCircuitFamily,
        validCfgCircuitFamilyGateTrace]
      constructor
      · rw [hlastGates, hpreviousGates]
        simp only [prefixRows, purePrevious, pureLast, List.append_assoc]
      · intro row
        split
        next hrow => exact hpreviousOutputs ⟨row.val, hrow⟩
        next => exact hlastWire

/-- Serial row validation appends exactly the corresponding pure family trace. -/
theorem validCfgCircuitFamily_gates_eq
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (validCfgCircuitFamily base rows hrows).builder.gates =
      base.gates ++
        (validCfgCircuitFamilyGateTrace base.gates.length n rows).gates :=
  (buildValidCfgCircuitFamily_trace_eq base n rows hrows).1

/-- Every row-validity output agrees with the corresponding family trace. -/
theorem validCfgCircuitFamily_output_eq_trace
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) (row : Fin n) :
    (validCfgCircuitFamily base rows hrows).outputs row =
      (validCfgCircuitFamilyGateTrace base.gates.length n rows).outputs row :=
  (buildValidCfgCircuitFamily_trace_eq base n rows hrows).2 row

/-- Serial row validation preserves the original builder. -/
theorem validCfgCircuitFamily_extends
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    base.Extends (validCfgCircuitFamily base rows hrows).builder :=
  (validCfgCircuitFamily base rows hrows).extension

/-- Every serial row-validity output belongs to the common final builder. -/
theorem validCfgCircuitFamily_outputs_valid
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) (row : Fin n) :
    (validCfgCircuitFamily base rows hrows).builder.WireValid
      ((validCfgCircuitFamily base rows hrows).outputs row) :=
  (validCfgCircuitFamily base rows hrows).outputsValid row

/-- Serial row validation pays exactly the local validity cost once per row. -/
theorem validCfgCircuitFamily_gate_delta
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base) :
    (validCfgCircuitFamily base rows hrows).builder.gates.length =
      base.gates.length + n * validCfgGateCost tm H :=
  (validCfgCircuitFamily base rows hrows).gate_delta

/-- Every old row has the same complete bit evaluation in the final family
builder as in the original builder. -/
theorem validCfgCircuitFamily_evalCfgBits
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (inputs : Nat → Bool) (row : Fin n) :
    evalCfgBits (validCfgCircuitFamily base rows hrows).builder inputs (rows row) =
      evalCfgBits base inputs (rows row) :=
  evalCfgBits_extends (validCfgCircuitFamily base rows hrows).extension
    inputs (rows row) (hrows row)

/-- Successful decoding of every old row is stable in the final family
builder. -/
theorem validCfgCircuitFamily_evalBundle
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (inputs : Nat → Bool) (row : Fin n) :
    evalBundle (validCfgCircuitFamily base rows hrows).builder inputs (rows row)
        ((hrows row).mono (validCfgCircuitFamily base rows hrows).extension) =
      evalBundle base inputs (rows row) (hrows row) :=
  evalBundle_extends (validCfgCircuitFamily base rows hrows).extension
    inputs (rows row) (hrows row)

/-- A row-family output is true exactly when that original public row decodes
as a canonical machine configuration. -/
theorem validCfgCircuitFamily_eval_iff
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows : ∀ row, (rows row).ValidIn base)
    (inputs : Nat → Bool) (row : Fin n) :
    (validCfgCircuitFamily base rows hrows).builder.evalWire inputs
        ((validCfgCircuitFamily base rows hrows).outputs row) = true ↔
      (evalBundle base inputs (rows row) (hrows row)).isSome = true := by
  exact (validCfgCircuitFamily base rows hrows).eval inputs row |>.trans
    (evalBundle_isSome_iff_canonical base inputs (rows row) (hrows row)).symm

/-- Serial row validation is independent of the supplied row-validity proof. -/
theorem validCfgCircuitFamily_proof_irrel
    {tm : _root_.Turing.FinTM2} {H n : Nat}
    (base : CircuitBuilder) (rows : Fin n → CfgWires tm H)
    (hrows₁ hrows₂ : ∀ row, (rows row).ValidIn base) :
    validCfgCircuitFamily base rows hrows₁ =
      validCfgCircuitFamily base rows hrows₂ := by
  congr

end

end CLRS.Chapter34.Turing.CookLevin
