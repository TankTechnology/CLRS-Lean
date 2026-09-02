import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Bounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Core

/-!
# CLRS Section 34.4 - Local transition-circuit gate bounds

Finite label dispatch and the full local transition circuit have emitted-gate
bounds with coefficients depending only on the fixed machine.  The displayed
width expressions remain explicit for later polynomial tableau composition.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Finite-label dispatch -/

/-- Height-independent coefficient for a finite suffix of program labels. -/
def dispatchListGateCoefficient (tm : _root_.Turing.FinTM2) :
    List tm.Λ → Nat
  | [] => 0
  | label :: labels =>
      compileStmtGateCoefficient tm (tm.m label) + 4 +
        dispatchListGateCoefficient tm labels

/-- Height-independent coefficient for complete finite-control dispatch. -/
def dispatchGateCoefficient (tm : _root_.Turing.FinTM2) : Nat :=
  dispatchListGateCoefficient tm (programLabels tm)

private theorem dispatchListGateCost_le
    (tm : _root_.Turing.FinTM2) (H : Nat) (labels : List tm.Λ) :
    dispatchListGateCost tm H labels ≤
      dispatchListGateCoefficient tm labels *
        (cfgBitCount tm (workHeight tm H) + workHeight tm H + 1) := by
  let width := cfgBitCount tm (workHeight tm H) + workHeight tm H + 1
  have hcfg : cfgBitCount tm (workHeight tm H) ≤ width := by omega
  induction labels with
  | nil => simp [dispatchListGateCost, dispatchListGateCoefficient]
  | cons label labels ih =>
      have hstmt := compileStmtGateCost_le tm (workHeight tm H) (tm.m label)
      have hmux : 3 * cfgBitCount tm (workHeight tm H) + 1 ≤ 4 * width := by
        omega
      simp only [dispatchListGateCost, dispatchListGateCoefficient]
      calc
        compileStmtGateCost tm (workHeight tm H) (tm.m label) +
              (3 * cfgBitCount tm (workHeight tm H) + 1) +
              dispatchListGateCost tm H labels ≤
            compileStmtGateCoefficient tm (tm.m label) * width +
              4 * width + dispatchListGateCoefficient tm labels * width :=
          Nat.add_le_add (Nat.add_le_add hstmt hmux) ih
        _ = (compileStmtGateCoefficient tm (tm.m label) + 4 +
              dispatchListGateCoefficient tm labels) * width := by
          ring

/-- Complete finite-label dispatch is bounded by a fixed-machine coefficient
times the affine workspace-width expression. -/
theorem dispatchGateCost_le (tm : _root_.Turing.FinTM2) (H : Nat) :
    dispatchGateCost tm H ≤ dispatchGateCoefficient tm *
      (cfgBitCount tm (workHeight tm H) + workHeight tm H + 1) := by
  exact dispatchListGateCost_le tm H (programLabels tm)

/-- Complete dispatch emits at most the advertised fixed-machine multiple of
the affine workspace-width expression beyond the input builder. -/
theorem dispatchLabels_gate_count_le
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (dispatchLabels tm H base pool source hvalid).builder.gates.length ≤
      base.gates.length + dispatchGateCoefficient tm *
        (cfgBitCount tm (workHeight tm H) + workHeight tm H + 1) := by
  rw [dispatchLabels_gate_delta]
  exact Nat.add_le_add_left (dispatchGateCost_le tm H) _

/-! ## Complete local transition circuit -/

/-- Height-independent coefficient controlling a complete local transition
circuit for one fixed machine. -/
def transitionCircuitGateCoefficient (tm : _root_.Turing.FinTM2) : Nat :=
  dispatchGateCoefficient tm + Fintype.card tm.K * maxPushesPerStep tm + 12

/-- The exact local-transition cost is bounded by a fixed-machine coefficient
times an explicit affine expression in workspace width, public width, and the
two corresponding heights. -/
theorem transitionCircuitGateCost_le (tm : _root_.Turing.FinTM2) (H : Nat) :
    transitionCircuitGateCost tm H ≤ transitionCircuitGateCoefficient tm *
      (cfgBitCount tm (workHeight tm H) + workHeight tm H +
        cfgBitCount tm H + H + 1) := by
  let width := cfgBitCount tm (workHeight tm H) + workHeight tm H +
    cfgBitCount tm H + H + 1
  let dispatchWidth :=
    cfgBitCount tm (workHeight tm H) + workHeight tm H + 1
  have hwidth : 0 < width := by omega
  have hdispatchWidth : dispatchWidth ≤ width := by omega
  have hdispatch : dispatchGateCost tm H ≤ dispatchGateCoefficient tm * width := by
    calc
      dispatchGateCost tm H ≤ dispatchGateCoefficient tm * dispatchWidth :=
        dispatchGateCost_le tm H
      _ ≤ dispatchGateCoefficient tm * width :=
        Nat.mul_le_mul_left _ hdispatchWidth
  let machineCost := Fintype.card tm.K * maxPushesPerStep tm
  have hmachine : machineCost ≤ machineCost * width :=
    Nat.le_mul_of_pos_right machineCost hwidth
  have hcfg : cfgBitCount tm H ≤ width := by omega
  have hcfgSix : 6 * cfgBitCount tm H ≤ 6 * width :=
    Nat.mul_le_mul_left 6 hcfg
  have hconstant : 6 ≤ 6 * width :=
    Nat.le_mul_of_pos_right 6 hwidth
  have hlocal : machineCost + 6 * cfgBitCount tm H + 6 ≤
      (machineCost + 12) * width := by
    calc
      machineCost + 6 * cfgBitCount tm H + 6 ≤
          machineCost * width + 6 * width + 6 * width :=
        Nat.add_le_add (Nat.add_le_add hmachine hcfgSix) hconstant
      _ = (machineCost + 12) * width := by ring
  change 2 + dispatchGateCost tm H + (machineCost + 2) +
      (6 * cfgBitCount tm H + 1) + 1 ≤ _
  change _ ≤ (dispatchGateCoefficient tm + machineCost + 12) * width
  calc
    2 + dispatchGateCost tm H + (machineCost + 2) +
          (6 * cfgBitCount tm H + 1) + 1 ≤
        dispatchGateCoefficient tm * width +
          (machineCost + 12) * width := by
      omega
    _ = (dispatchGateCoefficient tm + machineCost + 12) * width := by
      ring

/-- A complete local transition circuit emits at most the advertised
fixed-machine multiple of the explicit affine width expression. -/
theorem transitionCircuit_gate_count_le
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuit tm H base current next hcurrent hnext).builder.gates.length ≤
      base.gates.length + transitionCircuitGateCoefficient tm *
        (cfgBitCount tm (workHeight tm H) + workHeight tm H +
          cfgBitCount tm H + H + 1) := by
  rw [transitionCircuit_gate_delta]
  exact Nat.add_le_add_left (transitionCircuitGateCost_le tm H) _

end

end CLRS.Chapter34.Turing.CookLevin
