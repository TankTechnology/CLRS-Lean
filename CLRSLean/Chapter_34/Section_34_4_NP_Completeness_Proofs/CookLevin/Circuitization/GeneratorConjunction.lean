import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorAcceptingBoundary
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction

/-!
# Executable final verifier conjunction

The last gate family is the tail-first conjunction of every validity,
transition, and boundary output.  Its runtime frame is now tied directly to
the assembled verifier circuit.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open StateTransition
open PolyBuilder

/-- Canonical runtime frame for the final verifier conjunction. -/
def verifierFinalConjunctionFrame
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : AffineConjunctionFrame :=
  { start := (verifierAcceptingBoundary W x).builder.gates.length
    wires := verifierConstraintWires W x }

/-- Exact encoded gate suffix of the final conjunction. -/
def verifierFinalConjunctionGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  (CircuitBuilder.conjunctionGateTrace
    (verifierAcceptingBoundary W x).builder.gates.length
    (verifierConstraintWires W x)).gates.flatMap encodeCircuitGate

/-- The complete circuit gate list is the accepting-boundary prefix followed
by the literal final conjunction trace. -/
theorem verifierCircuit_gates_eq_finalConjunction
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    (verifierCircuit W x).gates =
      (verifierAcceptingBoundary W x).builder.gates ++
        (CircuitBuilder.conjunctionGateTrace
          (verifierAcceptingBoundary W x).builder.gates.length
          (verifierConstraintWires W x)).gates := by
  change (verifierConjunction W x).1.gates = _
  exact CircuitBuilder.conjunction_gates_eq
    (verifierAcceptingBoundary W x).builder
    (verifierConstraintWires W x)
    (verifierConstraintWires_valid W x)

/-- The runtime frame denotes exactly the semantic final-conjunction bytes. -/
theorem verifierFinalConjunctionFrame_gateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineConjunctionGateStream (verifierFinalConjunctionFrame W x) =
      verifierFinalConjunctionGateStream W x := by
  exact affineConjunctionGateStream_eq_trace
    (verifierFinalConjunctionFrame W x)

/-- The fixed tail-first conjunction controller executes the final verifier
gate family and preserves an arbitrary earlier reversed-output suffix. -/
def verifierFinalConjunctionFrame_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineConjunctionRevProgram)
      (affineConjunctionLoopCfg
        (encodeAffineConjunctionFrame
          (verifierFinalConjunctionFrame W x)) output)
      (some (haltCfg affineConjunctionRevProgram
        ((verifierFinalConjunctionGateStream W x).reverse ++ output)))
      (affineConjunctionRevSteps
        (verifierFinalConjunctionFrame W x)) := by
  simpa [verifierFinalConjunctionFrame_gateStream_eq] using
    affineConjunction_run (verifierFinalConjunctionFrame W x) output

/-- The final-conjunction run inherits the controller's explicit polynomial
bound in its exact runtime encoding. -/
theorem verifierFinalConjunctionFrame_steps_le
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineConjunctionRevSteps (verifierFinalConjunctionFrame W x) ≤
      1000 * (encodeAffineConjunctionFrame
        (verifierFinalConjunctionFrame W x)).length ^ 2 + 2 :=
  affineConjunctionRev_steps_le _

end

end CLRS.Chapter34.Turing.CookLevin
