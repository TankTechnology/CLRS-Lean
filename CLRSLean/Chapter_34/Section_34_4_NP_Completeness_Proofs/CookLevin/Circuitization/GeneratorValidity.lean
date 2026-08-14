import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorHeader

/-!
# Exact Cook--Levin validity serialization prefix

The semantic validity builder now has a literal gate trace for every public
tableau row.  This module flattens that trace into the general-circuit wire
format, proves exact agreement with the proof-carrying validity family, and
advances the already verified header/input/pool prefix through the complete
validity phase.

Main results:

- {lit}`verifierValidityGateStream_eq` identifies the literal validity stream
  with the suffix appended by the semantic builder.
- {lit}`verifierCircuitValidityPrefix_eq` identifies the complete serialized
  prefix through row validity.
- {lit}`verifierCircuitValidityPrefix_isPrefix` proves that this stream is a
  literal prefix of the final verifier-circuit encoding.

Current gap:

- A concrete TM2 must compute {lit}`verifierValidityGateStream`; polynomial
  output length alone is deliberately not used as a computability argument.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-! ## Literal validity gate stream -/

/-- Serialized exact gate trace for canonical validity across all verifier
tableau rows. -/
def verifierValidityGateStream {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  let rows := verifierRows W input
  let pool := verifierPool W input
  let trace := validCfgCircuitFamilyGateTrace pool.builder.gates.length
    (tableauRowCount ((verifierHorizon W).eval input.length)) rows.rows
  trace.gates.flatMap encodeCircuitGate

/-- The literal stream is exactly the encoded suffix appended by the semantic
validity family. -/
theorem verifierValidityGateStream_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    (verifierPool W input).builder.gates.flatMap encodeCircuitGate ++
        verifierValidityGateStream W input =
      (verifierValidity W input).builder.gates.flatMap encodeCircuitGate := by
  rw [verifierValidityGateStream, verifierValidity]
  rw [validCfgCircuitFamily_gates_eq, List.flatMap_append]

/-! ## Prefix through canonical row validity -/

/-- Exact circuit prefix through tableau inputs, the Boolean pool, and every
canonical row-validity gate. -/
def verifierCircuitValidityPrefix {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) : List CircuitSym :=
  verifierCircuitPoolPrefix W input ++ verifierValidityGateStream W input

/-- The generated stream agrees exactly with the semantic validity builder. -/
theorem verifierCircuitValidityPrefix_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitValidityPrefix W input =
      encNat (verifierCircuit W input).inputCount ++
        (verifierValidity W input).builder.gates.flatMap encodeCircuitGate := by
  rw [verifierCircuitValidityPrefix, verifierCircuitPoolPrefix_eq]
  rw [List.append_assoc, verifierValidityGateStream_eq]

/-- The validity builder remains an append-only prefix of the final
conjunction builder. -/
private theorem verifierValidity_extends_conjunction {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) (input : List Γ) :
    (verifierValidity W input).builder.Extends
      (verifierConjunction W input).1 := by
  let transitionExtension := (verifierTransitions W input).extension
  let initialExtension := (verifierInitialBoundary W input).extension
  let inputExtension := (verifierInputBoundary W input).extension
  let acceptingExtension := (verifierAcceptingBoundary W input).extension
  let conjunctionExtension := CircuitBuilder.conjunction_extends
    (verifierAcceptingBoundary W input).builder
    (verifierConstraintWires W input) (verifierConstraintWires_valid W input)
  exact transitionExtension.trans (initialExtension.trans
    (inputExtension.trans (acceptingExtension.trans conjunctionExtension)))

/-- The exact validity-phase stream is a literal prefix of the complete
verifier-circuit encoding. -/
theorem verifierCircuitValidityPrefix_isPrefix
    {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (input : List Γ) :
    verifierCircuitValidityPrefix W input <+:
      encodeCircuit (verifierCircuit W input) := by
  rcases (verifierValidity_extends_conjunction W input) with
    ⟨_, suffix, hgates⟩
  refine ⟨suffix.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output, ?_⟩
  rw [verifierCircuitValidityPrefix_eq]
  change _ = encNat (verifierCircuit W input).inputCount ++
    (verifierCircuit W input).gates.flatMap encodeCircuitGate ++
      .outputMark :: encNat (verifierCircuit W input).output
  change (verifierCircuit W input).gates =
      (verifierValidity W input).builder.gates ++ suffix at hgates
  rw [hgates, List.flatMap_append]
  simp only [List.append_assoc]

end CLRS.Chapter34.Turing.CookLevin
