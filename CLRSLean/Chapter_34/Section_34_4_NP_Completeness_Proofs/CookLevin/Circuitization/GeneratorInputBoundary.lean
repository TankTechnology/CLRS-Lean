import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInitialBoundary

/-!
# Exact verifier-input boundary target

This module specializes the generic three-phase input-shape trace to the
assembled verifier immediately after the symbolic initial-row boundary.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Literal separator-NOT, length-arm, and final-OR trace at the verifier's
actual first-row input stack. -/
def verifierInputBoundaryGateTrace
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitGate :=
  let rows := verifierRows W x
  let pool := verifierPool W x
  let validity := verifierValidity W x
  let transitions := verifierTransitions W x
  let initial := verifierInitialBoundary W x
  let extension := pool.extension.trans (validity.extension.trans
    (transitions.extension.trans initial.extension))
  let row := rows.rows (verifierFirstRow _)
  let hrow := (rows.rowValid (verifierFirstRow _)).mono extension
  verifierInputShapeGateTrace W ((verifierHeight W).eval x.length) x
    initial.builder
    (pool.pool.mono (validity.extension.trans
      (transitions.extension.trans initial.extension)))
    (row.stack W.machine.tm.k₀) (hrow.stack _)

/-- The assembled input-boundary builder appends exactly its literal
three-phase trace. -/
theorem verifierInputBoundary_gates_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) :
    (verifierInputBoundary W x).builder.gates =
      (verifierInitialBoundary W x).builder.gates ++
        verifierInputBoundaryGateTrace W x := by
  simpa [verifierInputBoundary, verifierInputBoundaryGateTrace] using
    verifierInputShapeCircuit_gates_eq W
      ((verifierHeight W).eval x.length) x
      (verifierInitialBoundary W x).builder
      ((verifierPool W x).pool.mono
        ((verifierValidity W x).extension.trans
          ((verifierTransitions W x).extension.trans
            (verifierInitialBoundary W x).extension)))
      (((verifierRows W x).rows (verifierFirstRow _)).stack
        W.machine.tm.k₀)
      ((((verifierRows W x).rowValid (verifierFirstRow _)).mono
          ((verifierPool W x).extension.trans
            ((verifierValidity W x).extension.trans
              ((verifierTransitions W x).extension.trans
                (verifierInitialBoundary W x).extension)))).stack
        W.machine.tm.k₀)

/-- Exact encoded byte suffix of the complete input-shape boundary. -/
def verifierInputBoundaryGateStream
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (x : List Γ) : List CircuitSym :=
  (verifierInputBoundaryGateTrace W x).flatMap encodeCircuitGate

end

end CLRS.Chapter34.Turing.CookLevin
