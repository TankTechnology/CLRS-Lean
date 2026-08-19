import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransition
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds

/-!
# Runtime seeds for every Cook--Levin transition row

For a fixed verifier machine, the exact local-transition cost is polynomial
in the public tableau height.  This file derives that polynomial structurally
from the bundled statements, then uses the existing triple-progression TM2 to
emit every row-major `(height, gateStart, rowBase)` transition seed directly
from the raw verifier word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Exact local-transition cost polynomials -/

/-- Affine workspace-height polynomial for the fixed verifier machine. -/
def workHeightPolynomial (tm : _root_.Turing.FinTM2) : Polynomial Nat :=
  Polynomial.X + Polynomial.C (maxPushesPerStep tm)

@[simp] theorem workHeightPolynomial_eval
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (workHeightPolynomial tm).eval height = workHeight tm height := by
  simp [workHeightPolynomial, workHeight]

/-- Exact gate-cost polynomial of one fixed bundled statement on every
positive stack height.  Positivity removes the sole zero-height branch in
the wire-level pop cost. -/
def compileStmtGatePolynomial (tm : _root_.Turing.FinTM2) :
    _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ → Polynomial Nat
  | .push k _ continuation =>
      Polynomial.C
          (stateCount tm + (reachableAlphabet tm k).card) +
        compileStmtGatePolynomial tm continuation
  | .peek k _ continuation =>
      Polynomial.C
          (2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
            stateCount tm) +
        compileStmtGatePolynomial tm continuation
  | .pop k _ continuation =>
      Polynomial.C
          (1 + 2 * stateCount tm *
            ((reachableAlphabet tm k).card + 1) + stateCount tm) +
        compileStmtGatePolynomial tm continuation
  | .load _ continuation =>
      Polynomial.C (stateCount tm + stateCount tm) +
        compileStmtGatePolynomial tm continuation
  | .branch test whenTrue whenFalse =>
      Polynomial.C
          ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1) +
        compileStmtGatePolynomial tm whenTrue +
        compileStmtGatePolynomial tm whenFalse +
        (Polynomial.C 3 * cfgBitPolynomial tm + 1)
  | .goto _ => Polynomial.C (stateCount tm + (labelCount tm + 1))
  | .halt => 0

/-- The structural statement polynomial evaluates to the exact compiler cost
at every positive height. -/
theorem compileStmtGatePolynomial_eval
    (tm : _root_.Turing.FinTM2)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (height : Nat) (hheight : 0 < height) :
    (compileStmtGatePolynomial tm q).eval height =
      compileStmtGateCost tm height q := by
  induction q with
  | halt => simp [compileStmtGatePolynomial, compileStmtGateCost]
  | goto label => simp [compileStmtGatePolynomial, compileStmtGateCost]
  | load update continuation ih =>
      simp [compileStmtGatePolynomial, compileStmtGateCost, ih]
  | push k emit continuation ih =>
      simp [compileStmtGatePolynomial, compileStmtGateCost, ih]
  | peek k update continuation ih =>
      simp [compileStmtGatePolynomial, compileStmtGateCost, ih]
  | pop k update continuation ih =>
      cases height with
      | zero => omega
      | succ height =>
          simp [compileStmtGatePolynomial, compileStmtGateCost,
            ih, popStackWireGateCost]
          ring
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      simp [compileStmtGatePolynomial, compileStmtGateCost,
        ihTrue, ihFalse, cfgBitPolynomial_eval]

/-- Exact polynomial for a fixed suffix of the finite label dispatch. -/
def dispatchListGatePolynomial (tm : _root_.Turing.FinTM2) :
    List tm.Λ → Polynomial Nat
  | [] => 0
  | label :: labels =>
      (compileStmtGatePolynomial tm (tm.m label)).comp
          (workHeightPolynomial tm) +
        (Polynomial.C 3 *
            (cfgBitPolynomial tm).comp (workHeightPolynomial tm) + 1) +
        dispatchListGatePolynomial tm labels

/-- Exact polynomial for the complete fixed-machine label dispatch. -/
def dispatchGatePolynomial (tm : _root_.Turing.FinTM2) : Polynomial Nat :=
  dispatchListGatePolynomial tm (programLabels tm)

theorem dispatchListGatePolynomial_eval
    (tm : _root_.Turing.FinTM2) (labels : List tm.Λ)
    (height : Nat) (hwork : 0 < workHeight tm height) :
    (dispatchListGatePolynomial tm labels).eval height =
      dispatchListGateCost tm height labels := by
  induction labels with
  | nil => simp [dispatchListGatePolynomial, dispatchListGateCost]
  | cons label labels ih =>
      simp [dispatchListGatePolynomial, dispatchListGateCost,
        Polynomial.eval_comp, compileStmtGatePolynomial_eval _ _ _ hwork,
        workHeightPolynomial_eval, cfgBitPolynomial_eval, ih]

@[simp] theorem dispatchGatePolynomial_eval
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (hwork : 0 < workHeight tm height) :
    (dispatchGatePolynomial tm).eval height =
      dispatchGateCost tm height := by
  exact dispatchListGatePolynomial_eval tm (programLabels tm) height hwork

/-- Exact gate-cost polynomial of one complete local transition check. -/
def transitionCircuitGatePolynomial
    (tm : _root_.Turing.FinTM2) : Polynomial Nat :=
  2 + dispatchGatePolynomial tm +
    Polynomial.C (Fintype.card tm.K * maxPushesPerStep tm + 2) +
    (Polynomial.C 6 * cfgBitPolynomial tm + 1) + 1

@[simp] theorem transitionCircuitGatePolynomial_eval
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (hwork : 0 < workHeight tm height) :
    (transitionCircuitGatePolynomial tm).eval height =
      transitionCircuitGateCost tm height := by
  simp [transitionCircuitGatePolynomial, transitionCircuitGateCost,
    dispatchGatePolynomial_eval tm height hwork,
    cfgBitPolynomial_eval]

/-! ## Verifier-specialized transition progressions -/

/-- Every published verifier height is positive because its input envelope
contains the pair separator. -/
theorem verifierHeight_eval_pos
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    0 < (verifierHeight W).eval n := by
  rw [verifierHeight_eval, verifierInputBound_eval]
  omega

/-- Exact input-length polynomial for one local verifier transition cost. -/
def verifierTransitionCostPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  (transitionCircuitGatePolynomial W.machine.tm).comp (verifierHeight W)

@[simp] theorem verifierTransitionCostPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierTransitionCostPolynomial W).eval n =
      transitionCircuitGateCost W.machine.tm
        ((verifierHeight W).eval n) := by
  unfold verifierTransitionCostPolynomial
  rw [Polynomial.eval_comp, transitionCircuitGatePolynomial_eval]
  exact Nat.add_pos_left
    (verifierHeight_eval_pos W n) (maxPushesPerStep W.machine.tm)

/-- Exact first gate index of the transition phase. -/
def verifierTransitionStartPolynomial
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierTableauInputPolynomial W + 2 +
    verifierValidityGateCountPolynomial W

@[simp] theorem verifierTransitionStartPolynomial_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierTransitionStartPolynomial W).eval n =
      tableauInputCount W.machine.tm
          ((verifierHeight W).eval n) ((verifierHorizon W).eval n) + 2 +
        tableauRowCount ((verifierHorizon W).eval n) *
          validCfgGateCost W.machine.tm ((verifierHeight W).eval n) := by
  simp [verifierTransitionStartPolynomial, tableauRowCount]

/-- The transition-start polynomial is literally the completed validity
builder length at the same dimensions. -/
theorem verifierTransitionStartPolynomial_eval_eq_validity_length
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) (n : Nat) :
    (verifierTransitionStartPolynomial W).eval n =
      (arithmeticValidityAt W.machine.tm
        ((verifierHeight W).eval n)
        ((verifierHorizon W).eval n)).builder.gates.length := by
  rw [verifierTransitionStartPolynomial_eval]
  unfold arithmeticValidityAt arithmeticPoolAt arithmeticRowsAt
  rw [validCfgCircuitFamily_gate_delta,
    CircuitBuilder.allocateBoolWirePool_gate_delta,
    allocateTableauRows_gate_delta]

/-- Minimal primary coordinates of one adjacent-row transition script. -/
structure TransitionRowSeed where
  height : Nat
  start : Nat
  rowBase : Nat
deriving DecidableEq, Repr

/-- One simultaneous affine progression for transition height, gate start,
and current tableau-row base. -/
def verifierTransitionRowSeedProgression
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : AffineUnaryTripleProgression :=
  exactPolynomialAffineUnaryTripleProgression
    (verifierHeight W)
    (verifierTransitionStartPolynomial W)
    0
    0
    (verifierTransitionCostPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierHorizon W)
    input

/-- Natural row-major transition seeds decoded from the progression. -/
def verifierTransitionRowSeeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List TransitionRowSeed :=
  (affineUnaryTripleProgressionRows
    (verifierTransitionRowSeedProgression W input)).map fun row =>
      { height := row.1
        start := row.2.1
        rowBase := row.2.2 }

/-- Closed row-index formula for every primary transition coordinate. -/
theorem verifierTransitionRowSeedTriples_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineUnaryTripleProgressionRows
        (verifierTransitionRowSeedProgression W input) =
      List.ofFn fun row : Fin ((verifierHorizon W).eval input.length) =>
        ((verifierHeight W).eval input.length,
          (verifierTransitionStartPolynomial W).eval input.length +
            row.val * transitionCircuitGateCost W.machine.tm
              ((verifierHeight W).eval input.length),
          row.val * cfgBitCount W.machine.tm
            ((verifierHeight W).eval input.length)) := by
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  simp only [verifierTransitionRowSeedProgression,
    exactPolynomialAffineUnaryTripleProgression,
    verifierTransitionCostPolynomial_eval,
    verifierCfgBitCountPolynomial_eval, Polynomial.eval_zero]
  apply List.ofFn_inj.mpr
  funext row
  simp

/-! ## Concrete raw-input seed compiler -/

/-- Delimiter-bearing transition seed triples in adjacent-row order. -/
def verifierTransitionRowSeedFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialAffineUnaryTripleProgressionFrameStream
    (verifierHeight W)
    (verifierTransitionStartPolynomial W)
    0
    0
    (verifierTransitionCostPolynomial W)
    (verifierCfgBitCountPolynomial W)
    (verifierHorizon W)
    input

/-- The generated stream contains exactly the three primary fields of each
semantic transition seed. -/
theorem verifierTransitionRowSeedFrames_eq_seeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierTransitionRowSeedFrames W input =
      (verifierTransitionRowSeeds W input).flatMap fun seed =>
        encodeUnaryFrame [seed.height, seed.start, seed.rowBase] := by
  simp [verifierTransitionRowSeedFrames,
    exactPolynomialAffineUnaryTripleProgressionFrameStream,
    verifierTransitionRowSeeds, verifierTransitionRowSeedProgression,
    affineUnaryTripleProgressionFrameStream,
    affineUnaryTripleRowValues, List.flatMap_map]

/-- A fixed polynomial-time TM2 emits every primary transition seed directly
from the raw verifier word. -/
noncomputable def verifierTransitionRowSeedFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionRowSeedFrames W) := by
  letI : Fintype Γ := W.alphabetFintype
  exact
    exactPolynomialAffineUnaryTripleProgressionFrameStream_computableInPolyTime
      (verifierHeight W)
      (verifierTransitionStartPolynomial W)
      0
      0
      (verifierTransitionCostPolynomial W)
      (verifierCfgBitCountPolynomial W)
      (verifierHorizon W)

end CLRS.Chapter34.Turing.CookLevin
