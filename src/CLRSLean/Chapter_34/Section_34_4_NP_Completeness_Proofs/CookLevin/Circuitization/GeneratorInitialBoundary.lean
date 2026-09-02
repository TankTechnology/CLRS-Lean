import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransition
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionFamilyScript

/-!
# Executable symbolic initial-row boundary

The first boundary after all transition constraints is one complete-row
equality.  This module freezes its literal gate trace, extracts the canonical
`EqFin` runtime frames, and executes them with the existing fixed controller.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

open StateTransition
open PolyBuilder

/-- Exact complete-row equality trace appended by the symbolic initial
boundary. -/
def verifierInitialBoundaryGateTrace
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : CircuitBuilder.EqFinGateTrace :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let row := rows.rows (verifierFirstRow _)
  let inputStack := row.stack W.machine.tm.k₀
  let target := symbolicInitialCfgWires W.machine.tm
    ((verifierHeight W).eval x.length)
    (pool.pool.mono (validity.extension.trans transitions.extension))
    inputStack
  CircuitBuilder.eqFinGateTrace transitions.builder.gates.length
    (fun i => row ((cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval x.length)).symm i))
    (fun i => target ((cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval x.length)).symm i))

/-- The semantic initial-boundary builder appends exactly the frozen trace. -/
theorem verifierInitialBoundary_gates_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    (verifierInitialBoundary W x).builder.gates =
      (verifierTransitions W x).builder.gates ++
        (verifierInitialBoundaryGateTrace W x).gates := by
  simp only [verifierInitialBoundary, verifierInitialBoundaryGateTrace,
    symbolicInitialCfgCircuit, cfgEqBoundaryCircuit]
  apply cfgEq_gates_eq

/-- Exact encoded gate suffix of the symbolic initial-row boundary. -/
def verifierInitialBoundaryGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  (verifierInitialBoundaryGateTrace W x).gates.flatMap encodeCircuitGate

/-- Canonical runtime equality frames for the symbolic initial boundary. -/
def compileVerifierInitialBoundaryFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List AffineEqFinPairFrame :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let row := rows.rows (verifierFirstRow _)
  let inputStack := row.stack W.machine.tm.k₀
  let target := symbolicInitialCfgWires W.machine.tm
    ((verifierHeight W).eval x.length)
    (pool.pool.mono (validity.extension.trans transitions.extension))
    inputStack
  affineEqFinCanonicalFrames transitions.builder.gates.length _
    (fun i => row ((cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval x.length)).symm i))
    (fun i => target ((cfgSlotEquivFin W.machine.tm
      ((verifierHeight W).eval x.length)).symm i))

/-- Interpreting the canonical frames gives the exact semantic boundary
bytes. -/
theorem compileVerifierInitialBoundaryFrames_gateStream_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    affineEqFinGateStream (compileVerifierInitialBoundaryFrames W x) =
      verifierInitialBoundaryGateStream W x := by
  simpa [compileVerifierInitialBoundaryFrames,
    verifierInitialBoundaryGateStream, verifierInitialBoundaryGateTrace] using
    affineEqFinCanonicalGateStream_eq_trace
      (verifierTransitions W x).builder.gates.length
      (fun i =>
        let rows := verifierRows W x
        rows.rows (verifierFirstRow _)
          ((cfgSlotEquivFin W.machine.tm
            ((verifierHeight W).eval x.length)).symm i))
      (fun i =>
        let rows := verifierRows W x
        let pool := verifierPool W x
        let validity := verifierValidity W x
        let transitions := verifierTransitions W x
        let row := rows.rows (verifierFirstRow _)
        symbolicInitialCfgWires W.machine.tm
          ((verifierHeight W).eval x.length)
          (pool.pool.mono
            (validity.extension.trans transitions.extension))
          (row.stack W.machine.tm.k₀)
          ((cfgSlotEquivFin W.machine.tm
            ((verifierHeight W).eval x.length)).symm i))

/-- The fixed equality controller executes the complete symbolic initial
boundary and halts on its exact encoded suffix. -/
def compileVerifierInitialBoundaryFrames_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineEqFinRevProgram)
      (affineEqFinLoopCfg
        (encodeAffineEqFinFrames
          (compileVerifierInitialBoundaryFrames W x)) output)
      (some (haltCfg affineEqFinRevProgram
        ((verifierInitialBoundaryGateStream W x).reverse ++ output)))
      (affineEqFinRevSteps
        (compileVerifierInitialBoundaryFrames W x)) := by
  simpa [compileVerifierInitialBoundaryFrames_gateStream_eq] using
    affineEqFin_run (compileVerifierInitialBoundaryFrames W x) output

end

end CLRS.Chapter34.Turing.CookLevin
