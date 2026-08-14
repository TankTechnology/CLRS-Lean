import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Assembly.Core

/-!
# Structural contracts of the assembled verifier circuit

The final circuit is closed only after every whole-tableau constraint has been
conjoined.  This layer proves well-formedness and records the exact emitted
gate count; semantic correctness is proved separately.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Exact number of gates emitted by the complete verifier circuit. -/
def verifierCircuitGateCost {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) : Nat :=
  let H := (verifierHeight W).eval x.length
  let T := (verifierHorizon W).eval x.length
  tableauInputCount W.machine.tm H T + 2 +
    (T + 1) * validCfgGateCost W.machine.tm H +
    T * transitionCircuitGateCost W.machine.tm H +
    (6 * cfgBitCount W.machine.tm H + 1) +
    verifierInputShapeGateCost W H x +
    acceptingOutputCircuitGateCost W.machine.tm H
      (List.map W.machine.outputAlphabet.invFun (boolEncoding true)) +
    ((T + 1) + T + 3 + 1)

/-- Close the append-only verifier builder at its final conjunction wire. -/
def verifierCircuit {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) : Circuit :=
  let accepting := verifierAcceptingBoundary W x
  let wires := verifierConstraintWires W x
  let hvalid := verifierConstraintWires_valid W x
  let final := accepting.builder.conjunction wires hvalid
  final.1.finish final.2
    (CircuitBuilder.conjunction_wireValid accepting.builder wires hvalid)

/-- The generated verifier circuit has no dangling or forward references. -/
theorem verifierCircuit_wellFormed {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierCircuit W x).WellFormed := by
  unfold verifierCircuit
  exact CircuitBuilder.finish_wellFormed _ _ _

/-- The collected constraint list contains one output per row, one per
adjacent step, and three boundary outputs. -/
@[simp] theorem verifierConstraintWires_length {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierConstraintWires W x).length =
      ((verifierHorizon W).eval x.length + 1) +
        (verifierHorizon W).eval x.length + 3 := by
  simp [verifierConstraintWires, verifierValidity, verifierTransitions,
    verifierRows, tableauRowCount]
  omega

private theorem verifierAcceptingBoundary_gate_delta
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierAcceptingBoundary W x).builder.gates.length =
      (verifierInputBoundary W x).builder.gates.length +
        acceptingOutputCircuitGateCost W.machine.tm
          ((verifierHeight W).eval x.length)
          (List.map W.machine.outputAlphabet.invFun (boolEncoding true)) := by
  unfold verifierAcceptingBoundary
  exact acceptingOutputCircuit_gate_delta _ _ _ _ _ _ _

private theorem verifierInputBoundary_gate_delta
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierInputBoundary W x).builder.gates.length =
      (verifierInitialBoundary W x).builder.gates.length +
        verifierInputShapeGateCost W ((verifierHeight W).eval x.length) x := by
  unfold verifierInputBoundary
  exact verifierInputShapeCircuit_gate_delta _ _ _ _ _ _ _

private theorem verifierInitialBoundary_gate_delta
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierInitialBoundary W x).builder.gates.length =
      (verifierTransitions W x).builder.gates.length +
        (6 * cfgBitCount W.machine.tm
          ((verifierHeight W).eval x.length) + 1) := by
  unfold verifierInitialBoundary
  exact symbolicInitialCfgCircuit_gate_delta _ _ _ _ _ _ _ _

private theorem verifierTransitions_gate_delta
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierTransitions W x).builder.gates.length =
      (verifierValidity W x).builder.gates.length +
        (verifierHorizon W).eval x.length * transitionCircuitGateCost
          W.machine.tm ((verifierHeight W).eval x.length) := by
  unfold verifierTransitions
  exact transitionCircuitFamily_gate_delta _ _ _ _ _

private theorem verifierValidity_gate_delta
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierValidity W x).builder.gates.length =
      (verifierPool W x).builder.gates.length +
        ((verifierHorizon W).eval x.length + 1) * validCfgGateCost
          W.machine.tm ((verifierHeight W).eval x.length) := by
  unfold verifierValidity
  simpa [tableauRowCount] using validCfgCircuitFamily_gate_delta
    (verifierPool W x).builder (verifierRows W x).rows
      (fun row => ((verifierRows W x).rowValid row).mono
        (verifierPool W x).extension)

private theorem verifierPool_gate_delta {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierPool W x).builder.gates.length =
      (verifierRows W x).builder.gates.length + 2 := by
  unfold verifierPool
  exact CircuitBuilder.allocateBoolWirePool_gate_delta _

private theorem verifierRows_gate_delta {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierRows W x).builder.gates.length = tableauInputCount W.machine.tm
      ((verifierHeight W).eval x.length)
      ((verifierHorizon W).eval x.length) := by
  unfold verifierRows
  exact allocateTableauRows_gate_delta _ _ _

/-- The final circuit gate list has the exact compositional cost above. -/
theorem verifierCircuit_gate_count_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (x : List Γ) :
    (verifierCircuit W x).gates.length = verifierCircuitGateCost W x := by
  classical
  change (verifierConjunction W x).1.gates.length = _
  rw [show verifierConjunction W x =
      (verifierAcceptingBoundary W x).builder.conjunction
        (verifierConstraintWires W x) (verifierConstraintWires_valid W x) by
    rfl]
  rw [CircuitBuilder.conjunction_gate_delta]
  rw [verifierAcceptingBoundary_gate_delta]
  rw [verifierInputBoundary_gate_delta]
  rw [verifierInitialBoundary_gate_delta]
  rw [verifierTransitions_gate_delta]
  rw [verifierValidity_gate_delta]
  rw [verifierPool_gate_delta]
  rw [verifierRows_gate_delta]
  simp only [verifierConstraintWires_length]
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
