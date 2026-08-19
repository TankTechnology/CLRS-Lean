import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRows
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.TableauConstraints.TransitionFamilyTrace

/-!
# Exact semantic target for transition-family generation

This module freezes the byte stream that a concrete transition generator must
emit. It deliberately does not claim TM execution yet: the executable
controller must later prove equality with this exact dimension-only suffix.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Dimension-only tableau allocation used by the transition target. -/
def arithmeticRowsAt (tm : _root_.Turing.FinTM2) (H T : Nat) :=
  allocateTableauRows tm H T

/-- Dimension-only shared Boolean pool used by validity and transitions. -/
def arithmeticPoolAt (tm : _root_.Turing.FinTM2) (H T : Nat) :=
  CircuitBuilder.allocateBoolWirePool (arithmeticRowsAt tm H T).builder

/-- Dimension-only completed validity result. -/
def arithmeticValidityAt (tm : _root_.Turing.FinTM2) (H T : Nat) :=
  let rows := arithmeticRowsAt tm H T
  let pool := arithmeticPoolAt tm H T
  validCfgCircuitFamily pool.builder rows.rows
    (fun row => (rows.rowValid row).mono pool.extension)

/-- Dimension-only transition family immediately following validity. -/
def arithmeticTransitionsAt (tm : _root_.Turing.FinTM2) (H T : Nat) :=
  let rows := arithmeticRowsAt tm H T
  let pool := arithmeticPoolAt tm H T
  let validity := arithmeticValidityAt tm H T
  transitionCircuitFamily tm H validity.builder rows.rows (fun row =>
    (rows.rowValid row).mono (pool.extension.trans validity.extension))

/-- Explicit structural transition-family trace at dimension-only rows. -/
def transitionFamilyGateTraceAt (tm : _root_.Turing.FinTM2) (H T : Nat) :
    List CircuitGate :=
  let rows := arithmeticRowsAt tm H T
  let pool := arithmeticPoolAt tm H T
  let validity := arithmeticValidityAt tm H T
  transitionCircuitFamilyGateTrace tm H validity.builder T rows.rows
    (fun row =>
      (rows.rowValid row).mono (pool.extension.trans validity.extension))

/-- The exact unencoded transition-gate suffix after completed validity. -/
def transitionGateListAt (tm : _root_.Turing.FinTM2) (H T : Nat) :
    List CircuitGate :=
  (arithmeticTransitionsAt tm H T).builder.gates.drop
    (arithmeticValidityAt tm H T).builder.gates.length

/-- The exact encoded transition-family suffix at explicit dimensions. -/
def transitionGateStreamAt (tm : _root_.Turing.FinTM2) (H T : Nat) :
    List CircuitSym :=
  (transitionGateListAt tm H T).flatMap encodeCircuitGate

/-- The earlier suffix-based target is exactly the explicit recursive family
trace; `List.drop` is no longer part of the transition acceptance surface. -/
theorem transitionGateListAt_eq_trace
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    transitionGateListAt tm H T = transitionFamilyGateTraceAt tm H T := by
  let rows := arithmeticRowsAt tm H T
  let pool := arithmeticPoolAt tm H T
  let validity := arithmeticValidityAt tm H T
  have hgates :
      (arithmeticTransitionsAt tm H T).builder.gates =
        validity.builder.gates ++ transitionFamilyGateTraceAt tm H T := by
    simpa [arithmeticTransitionsAt, rows, pool, validity,
      transitionFamilyGateTraceAt, arithmeticRowsAt, arithmeticPoolAt,
      arithmeticValidityAt] using
      transitionCircuitFamily_gates_eq tm H validity.builder T rows.rows
        (fun row =>
          (rows.rowValid row).mono
            (pool.extension.trans validity.extension))
  unfold transitionGateListAt
  rw [hgates]
  simp [validity, arithmeticValidityAt]

/-- The encoded transition target is the encoding of the explicit recursive
family trace. -/
theorem transitionGateStreamAt_eq_trace
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    transitionGateStreamAt tm H T =
      (transitionFamilyGateTraceAt tm H T).flatMap encodeCircuitGate := by
  rw [transitionGateStreamAt, transitionGateListAt_eq_trace]

/-- Transition construction is literally validity followed by the frozen
transition suffix. -/
theorem arithmeticValidity_append_transitionGateStream
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    (arithmeticValidityAt tm H T).builder.gates.flatMap encodeCircuitGate ++
        transitionGateStreamAt tm H T =
      (arithmeticTransitionsAt tm H T).builder.gates.flatMap
        encodeCircuitGate := by
  rcases (arithmeticTransitionsAt tm H T).extension with
    ⟨_, suffix, hgates⟩
  unfold transitionGateStreamAt transitionGateListAt
  rw [hgates]
  simp [List.flatMap_append]

/-- The frozen suffix contains exactly one local transition circuit per
adjacent tableau-row pair. -/
@[simp] theorem transitionGateListAt_length
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    (transitionGateListAt tm H T).length =
      T * transitionCircuitGateCost tm H := by
  unfold transitionGateListAt
  rw [List.length_drop, (arithmeticTransitionsAt tm H T).gate_delta]
  omega

/-- Verifier-specialized transition stream; source symbols influence it only
through the encoded input length. -/
def verifierTransitionGateStreamByLength
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (inputLength : Nat) : List CircuitSym :=
  transitionGateStreamAt W.machine.tm
    ((verifierHeight W).eval inputLength)
    ((verifierHorizon W).eval inputLength)

/-- Concrete-input wrapper for the dimension-only transition stream. -/
def verifierTransitionGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List CircuitSym :=
  verifierTransitionGateStreamByLength W input.length

theorem verifierTransitionGateStream_eq_byLength
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionGateStream W input =
      verifierTransitionGateStreamByLength W input.length := rfl

/-- The verifier's proof-carrying transition builder appends exactly the
dimension-only frozen stream. -/
theorem verifierValidity_append_transitionGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierValidity W input).builder.gates.flatMap encodeCircuitGate ++
        verifierTransitionGateStream W input =
      (verifierTransitions W input).builder.gates.flatMap
        encodeCircuitGate := by
  simpa [verifierValidity, verifierTransitions, verifierRows, verifierPool,
    verifierTransitionGateStream, verifierTransitionGateStreamByLength,
    arithmeticRowsAt, arithmeticPoolAt, arithmeticValidityAt,
    arithmeticTransitionsAt] using
      arithmeticValidity_append_transitionGateStream W.machine.tm
        ((verifierHeight W).eval input.length)
        ((verifierHorizon W).eval input.length)

/-- Exact circuit prefix through both validity and all adjacent-row
transition constraints. -/
def verifierCircuitTransitionPrefix
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List CircuitSym :=
  verifierCircuitValidityPrefix W input ++
    verifierTransitionGateStream W input

/-- The transition prefix agrees literally with the semantic transition
builder, including the exact circuit input header. -/
theorem verifierCircuitTransitionPrefix_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierCircuitTransitionPrefix W input =
      encNat (verifierCircuit W input).inputCount ++
        (verifierTransitions W input).builder.gates.flatMap
          encodeCircuitGate := by
  rw [verifierCircuitTransitionPrefix, verifierCircuitValidityPrefix_eq]
  rw [List.append_assoc, verifierValidity_append_transitionGateStream]

end

end CLRS.Chapter34.Turing.CookLevin
