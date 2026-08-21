import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorFinalConstraintTransitionSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryEndSource

/-!
# Closed coordinates of the three boundary outputs

This module identifies the symbolic-initial, input-shape, and accepting
outputs collected by the final verifier conjunction.  The positive equality
branches end at their last fresh wire; the static negative accepting branch
reuses the shared false-pool wire.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem eqFinGateTrace_wire_eq_start_add_six
    (start : Nat) : ∀ (n : Nat)
      (left right : Fin n → CircuitBuilder.Wire),
      (CircuitBuilder.eqFinGateTrace start left right).wire =
        start + 6 * n := by
  intro n
  cases n with
  | zero => intro left right; rfl
  | succ n =>
      intro left right
      unfold CircuitBuilder.eqFinGateTrace
      simp only [CircuitBuilder.eqFinBodyGateTrace]
      rw [CircuitBuilder.eqFinBodyGateTrace_length,
        CircuitBuilder.boolEqGateTrace_length]
      ring

private theorem disjunctionGateTrace_wire_eq_start_add_length
    (start : Nat) : ∀ wires : List CircuitBuilder.Wire,
    (CircuitBuilder.disjunctionGateTrace start wires).wire =
      start + wires.length := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [CircuitBuilder.disjunctionGateTrace,
        CircuitBuilder.disjunctionGateTrace_length, ih]

/-- Exact polynomial coordinate of the symbolic-initial output. -/
def verifierInitialBoundaryOutputPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierTransitionEndPolynomial W +
    Polynomial.C 6 * verifierCfgBitCountPolynomial W

/-- The symbolic-initial output is its final equality-aggregate wire. -/
theorem verifierInitialBoundary_wire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInitialBoundary W input).wire =
      (verifierInitialBoundaryOutputPolynomial W).eval input.length := by
  unfold verifierInitialBoundary symbolicInitialCfgCircuit
    cfgEqBoundaryCircuit
  dsimp only
  rw [cfgEq_wire_eq_trace,
    eqFinGateTrace_wire_eq_start_add_six]
  rw [← verifierTransitionEndPolynomial_eval_eq_builder W input]
  simp [verifierInitialBoundaryOutputPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul]

/-- Builder-free coordinate of the final input-shape disjunction output. -/
def verifierInputBoundaryOutput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  verifierInputFinalOrStart W input +
    (verifierInputArmCountPolynomial W).eval input.length

/-- The input-shape output is the last wire of its false-seeded final OR. -/
theorem verifierInputBoundary_wire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierInputBoundary W input).wire =
      verifierInputBoundaryOutput W input := by
  have hwire :
      (verifierInputBoundary W input).wire =
        (verifierInputBoundaryScript W input).finalOrStart +
          (verifierInputBoundaryScript W input).finalOrWires.length := by
    unfold verifierInputBoundary verifierInputBoundaryScript
      compileVerifierInputShapeScript verifierInputShapeCircuit
    dsimp only
    rw [CircuitBuilder.disjunction_wire_eq_trace]
    rw [disjunctionGateTrace_wire_eq_start_add_length]
  rw [hwire, verifierInputBoundaryScript_finalOrStart_eq_arithmetic]
  simp [verifierInputBoundaryOutput,
    verifierInputBoundaryScript_finalOrWires_length]

/-- Builder-free coordinate of the total accepting-boundary output. -/
def verifierAcceptingBoundaryOutput
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  if verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁ then
    verifierInputBoundaryEnd W input +
      (Polynomial.C 6 * verifierCfgBitCountPolynomial W).eval input.length
  else
    (verifierInitialFalseWirePolynomial W).eval input.length

/-- The accepting output is either the last equality wire or the shared false
wire, according to the machine-static alphabet branch. -/
theorem verifierAcceptingBoundary_wire_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierAcceptingBoundary W input).wire =
      verifierAcceptingBoundaryOutput W input := by
  classical
  by_cases hmember : verifierAcceptingSymbol W ∈
      reachableAlphabet W.machine.tm W.machine.tm.k₁
  · have hfit := verifierAcceptingOutputFitsOfSymbol W input hmember
    unfold verifierAcceptingBoundary
    rw [show acceptingOutputCircuit W.machine.tm
          ((verifierHeight W).eval input.length)
          (verifierInputBoundary W input).builder
          ((verifierPool W input).pool.mono
            ((verifierValidity W input).extension.trans
              ((verifierTransitions W input).extension.trans
                ((verifierInitialBoundary W input).extension.trans
                  (verifierInputBoundary W input).extension))))
          ((verifierRows W input).rows
            (Fin.last ((verifierHorizon W).eval input.length)))
          _ (verifierAcceptingOutput W) =
        cfgEqBoundaryCircuit (verifierInputBoundary W input).builder
          ((verifierRows W input).rows
            (Fin.last ((verifierHorizon W).eval input.length)))
          (verifierAcceptingTargetWires W input hfit) _ _ by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    unfold cfgEqBoundaryCircuit
    dsimp only
    rw [cfgEq_wire_eq_trace,
      eqFinGateTrace_wire_eq_start_add_six]
    rw [verifierInputBoundary_gates_length_eq_end]
    simp [verifierAcceptingBoundaryOutput, hmember,
      Polynomial.eval_mul]
  · have hfit : ¬ AcceptingOutputFits W.machine.tm
        ((verifierHeight W).eval input.length)
        (verifierAcceptingOutput W) :=
      (verifierAcceptingOutputFits_iff W input).not.mpr hmember
    unfold verifierAcceptingBoundary
    rw [show acceptingOutputCircuit W.machine.tm
          ((verifierHeight W).eval input.length)
          (verifierInputBoundary W input).builder
          ((verifierPool W input).pool.mono
            ((verifierValidity W input).extension.trans
              ((verifierTransitions W input).extension.trans
                ((verifierInitialBoundary W input).extension.trans
                  (verifierInputBoundary W input).extension))))
          ((verifierRows W input).rows
            (Fin.last ((verifierHorizon W).eval input.length)))
          _ (verifierAcceptingOutput W) =
        falseBoundaryCircuit (verifierInputBoundary W input).builder
          ((verifierPool W input).pool.mono
            ((verifierValidity W input).extension.trans
              ((verifierTransitions W input).extension.trans
                ((verifierInitialBoundary W input).extension.trans
                  (verifierInputBoundary W input).extension)))) by
      simp only [acceptingOutputCircuit, hfit]
      rfl]
    change (verifierPool W input).pool.falseWire = _
    rw [verifierPool_falseWire_eq]
    simp [verifierAcceptingBoundaryOutput, hmember]

end CLRS.Chapter34.Turing.CookLevin
