import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Bounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Finishing

/-!
# Chapter 34 Cook--Levin emitted-gate bounds

Focused interface, concrete-machine, and finished-circuit regressions for
milestone 8H.  These bounds count emitted Boolean gates; they deliberately do
not claim a host-language evaluation-time bound for Lean definitions.

The existing regression matrix remains distributed by semantic concern:

- aliased row rejection and canonical validity, including `H = 0` and empty
  reachable support: `Tests/Chapter_34_CookLevin_Internal.lean`;
- temporary push/pop headroom, multi-push paths, halted stuttering, and final
  overflow rejection: `Tests/Chapter_34_CookLevin_TransitionCircuits.lean`;
- unsupported accepting output taking an actual false-wire branch:
  `Tests/Chapter_34_CookLevin_BoundaryCircuits.lean`.

This file adds the missing quantitative and `CircuitBuilder.finish` rows
without duplicating those semantic tests.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

#check validCfgGateCoefficient
#check validCfgGateCost_le
#check validCfgCircuit_gate_count_le
#check dispatchGateCoefficient
#check dispatchGateCost_le
#check dispatchLabels_gate_count_le
#check transitionCircuitGateCoefficient
#check transitionCircuitGateCost_le
#check transitionCircuit_gate_count_le
#check validCfgCircuitFinished
#check validCfgCircuit_finish_wellFormed
#check validCfgCircuit_finish_eval
#check validCfgCircuitFinished_proof_irrel
#check transitionCircuitFinished
#check transitionCircuit_finish_wellFormed
#check transitionCircuit_finish_eval
#check transitionCircuitFinished_proof_irrel

/-! ## Actual fixed-machine bounds at zero and positive heights -/

/-- Empty-support one-stack machine with one immediate-halt label. -/
private abbrev BoundsMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Empty
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := .halt

-- The exact row-validity costs exercise both the height-zero and positive rows.
example : validCfgGateCost BoundsMachine 0 = 35 := by
  simp [validCfgGateCost, BoundsMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

example : validCfgGateCost BoundsMachine 1 = 54 := by
  simp [validCfgGateCost, BoundsMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

-- The fixed coefficient is genuine data, independent of `H`, and nonzero.
example : validCfgGateCoefficient BoundsMachine = 54 := by
  simp [validCfgGateCoefficient, BoundsMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

example : 0 < validCfgGateCoefficient BoundsMachine := by
  rw [show validCfgGateCoefficient BoundsMachine = 54 by
    simp [validCfgGateCoefficient, BoundsMachine, labelCount, stateCount,
      reachableAlphabet, stmtPushSet]]
  decide

example : dispatchGateCoefficient BoundsMachine = 4 := by
  simp [dispatchGateCoefficient, dispatchListGateCoefficient, programLabels,
    BoundsMachine, labelCount, compileStmtGateCoefficient]

-- These exact finite computations are intentionally independent of the bound
-- theorems below: they catch drift in either the cost recurrence or coefficient.
example : dispatchGateCost BoundsMachine 0 = 16 := by
  simp [dispatchGateCost, dispatchListGateCost, programLabels, BoundsMachine,
    labelCount, stateCount, compileStmtGateCost, workHeight, maxPushesPerStep,
    stmtMaxPushes, cfgBitCount, reachableAlphabet, stmtPushSet]

example : dispatchGateCost BoundsMachine 2 = 28 := by
  simp [dispatchGateCost, dispatchListGateCost, programLabels, BoundsMachine,
    labelCount, stateCount, compileStmtGateCost, workHeight, maxPushesPerStep,
    stmtMaxPushes, cfgBitCount, reachableAlphabet, stmtPushSet]

example : transitionCircuitGateCoefficient BoundsMachine = 16 := by
  simp [transitionCircuitGateCoefficient, dispatchGateCoefficient,
    dispatchListGateCoefficient, programLabels, BoundsMachine, labelCount,
    compileStmtGateCoefficient, maxPushesPerStep, stmtMaxPushes]

example : transitionCircuitGateCost BoundsMachine 0 = 52 := by
  simp [transitionCircuitGateCost, dispatchGateCost, dispatchListGateCost,
    programLabels, BoundsMachine, labelCount, compileStmtGateCost, workHeight,
    stateCount, maxPushesPerStep, stmtMaxPushes, cfgBitCount, reachableAlphabet,
    stmtPushSet]

example : transitionCircuitGateCost BoundsMachine 2 = 88 := by
  simp [transitionCircuitGateCost, dispatchGateCost, dispatchListGateCost,
    programLabels, BoundsMachine, labelCount, compileStmtGateCost, workHeight,
    stateCount, maxPushesPerStep, stmtMaxPushes, cfgBitCount, reachableAlphabet,
    stmtPushSet]

-- The displayed right-hand sides are also independently evaluated, so the
-- regression records the concrete slack rather than only a symbolic `≤`.
example : dispatchGateCoefficient BoundsMachine *
    (cfgBitCount BoundsMachine (workHeight BoundsMachine 0) +
      workHeight BoundsMachine 0 + 1) = 24 := by
  simp [dispatchGateCoefficient, dispatchListGateCoefficient, programLabels,
    BoundsMachine, labelCount, stateCount, compileStmtGateCoefficient, workHeight,
    maxPushesPerStep, stmtMaxPushes, cfgBitCount, reachableAlphabet,
    stmtPushSet]

example : dispatchGateCoefficient BoundsMachine *
    (cfgBitCount BoundsMachine (workHeight BoundsMachine 2) +
      workHeight BoundsMachine 2 + 1) = 48 := by
  simp [dispatchGateCoefficient, dispatchListGateCoefficient, programLabels,
    BoundsMachine, labelCount, stateCount, compileStmtGateCoefficient, workHeight,
    maxPushesPerStep, stmtMaxPushes, cfgBitCount, reachableAlphabet,
    stmtPushSet]

example : transitionCircuitGateCoefficient BoundsMachine *
    (cfgBitCount BoundsMachine (workHeight BoundsMachine 0) +
      workHeight BoundsMachine 0 + cfgBitCount BoundsMachine 0 + 0 + 1) = 176 := by
  simp [transitionCircuitGateCoefficient, dispatchGateCoefficient,
    dispatchListGateCoefficient, programLabels, BoundsMachine, labelCount,
    stateCount, compileStmtGateCoefficient, workHeight, maxPushesPerStep, stmtMaxPushes,
    cfgBitCount, reachableAlphabet, stmtPushSet]

example : transitionCircuitGateCoefficient BoundsMachine *
    (cfgBitCount BoundsMachine (workHeight BoundsMachine 2) +
      workHeight BoundsMachine 2 + cfgBitCount BoundsMachine 2 + 2 + 1) = 368 := by
  simp [transitionCircuitGateCoefficient, dispatchGateCoefficient,
    dispatchListGateCoefficient, programLabels, BoundsMachine, labelCount,
    stateCount, compileStmtGateCoefficient, workHeight, maxPushesPerStep, stmtMaxPushes,
    cfgBitCount, reachableAlphabet, stmtPushSet]

-- Concrete exact-cost-to-bound checks at `H = 0` and `H > 0`.
example : validCfgGateCost BoundsMachine 0 ≤
    validCfgGateCoefficient BoundsMachine * (0 + 1) :=
  validCfgGateCost_le BoundsMachine 0

example : validCfgGateCost BoundsMachine 2 ≤
    validCfgGateCoefficient BoundsMachine * (2 + 1) :=
  validCfgGateCost_le BoundsMachine 2

example : dispatchGateCost BoundsMachine 0 ≤
    dispatchGateCoefficient BoundsMachine *
      (cfgBitCount BoundsMachine (workHeight BoundsMachine 0) +
        workHeight BoundsMachine 0 + 1) :=
  dispatchGateCost_le BoundsMachine 0

example : dispatchGateCost BoundsMachine 2 ≤
    dispatchGateCoefficient BoundsMachine *
      (cfgBitCount BoundsMachine (workHeight BoundsMachine 2) +
        workHeight BoundsMachine 2 + 1) :=
  dispatchGateCost_le BoundsMachine 2

example : transitionCircuitGateCost BoundsMachine 0 ≤
    transitionCircuitGateCoefficient BoundsMachine *
      (cfgBitCount BoundsMachine (workHeight BoundsMachine 0) +
        workHeight BoundsMachine 0 + cfgBitCount BoundsMachine 0 + 0 + 1) :=
  transitionCircuitGateCost_le BoundsMachine 0

example : transitionCircuitGateCost BoundsMachine 2 ≤
    transitionCircuitGateCoefficient BoundsMachine *
      (cfgBitCount BoundsMachine (workHeight BoundsMachine 2) +
        workHeight BoundsMachine 2 + cfgBitCount BoundsMachine 2 + 2 + 1) :=
  transitionCircuitGateCost_le BoundsMachine 2

-- The local-transition coefficient cannot collapse to a vacuous zero bound.
example : 0 < transitionCircuitGateCoefficient BoundsMachine := by
  unfold transitionCircuitGateCoefficient
  omega

/-! ## Actual finished circuits -/

private abbrev boundsBase (H : Nat) := freshTransitionBase BoundsMachine H
private abbrev boundsCurrent (H : Nat) :=
  (freshCurrentAllocation BoundsMachine H).wires
private abbrev boundsNext (H : Nat) :=
  (freshNextAllocation BoundsMachine H).wires

/-- Nonhalted source row for a concrete immediate-halt transition. -/
private def boundsSource : BoundsMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => []

/-- Correct halted successor of `boundsSource`. -/
private def boundsHalted : BoundsMachine.Cfg where
  l := none
  var := ()
  stk := fun _ => []

private theorem boundsSourceAlphabet :
    CfgAlphabetBounded BoundsMachine boundsSource := by
  intro k a
  cases k
  exact Empty.elim a

private theorem boundsHaltedAlphabet :
    CfgAlphabetBounded BoundsMachine boundsHalted := by
  intro k a
  cases k
  exact Empty.elim a

private theorem boundsSourceHeight :
    ∀ k, (boundsSource.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

private theorem boundsHaltedHeight :
    ∀ k, (boundsHalted.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

private theorem boundsImmediateHalt :
    boundsHalted = stutterStep BoundsMachine boundsSource := by
  rfl

/-- Two explicit consecutive `writeCfgBits` patches with a fixed source row. -/
private def boundsInputs (next : BoundsMachine.Cfg)
    (hnextAlphabet : CfgAlphabetBounded BoundsMachine next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ 0) : Nat → Bool :=
  freshTransitionInputsAt BoundsMachine 0 (freshCurrentLayout BoundsMachine 0)
    (fun _ => false) boundsSource next boundsSourceAlphabet
    boundsSourceHeight hnextAlphabet hnextHeight

private theorem boundsCurrentDecoded
    (next : BoundsMachine.Cfg)
    (hnextAlphabet : CfgAlphabetBounded BoundsMachine next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ 0) :
    evalBundle (boundsBase 0) (boundsInputs next hnextAlphabet hnextHeight)
      (boundsCurrent 0) (freshCurrentValid BoundsMachine 0) =
        some boundsSource := by
  rw [evalBundle_extends (freshNextAllocation BoundsMachine 0).extension
    (boundsInputs next hnextAlphabet hnextHeight)
    (freshCurrentAllocation BoundsMachine 0).wires
    (freshCurrentAllocation BoundsMachine 0).valid]
  apply evalBundle_encodeCfg
  funext slot
  rw [evalCfgBits, (freshCurrentAllocation BoundsMachine 0).eval_slot]
  exact freshTransitionInputsAt_current_index BoundsMachine 0
    (freshCurrentLayout BoundsMachine 0) (fun _ => false)
    boundsSource next boundsSourceAlphabet boundsSourceHeight
    hnextAlphabet hnextHeight slot

private theorem boundsNextDecoded
    (next : BoundsMachine.Cfg)
    (hnextAlphabet : CfgAlphabetBounded BoundsMachine next)
    (hnextHeight : ∀ k, (next.stk k).length ≤ 0) :
    evalBundle (boundsBase 0) (boundsInputs next hnextAlphabet hnextHeight)
      (boundsNext 0) (freshNextValid BoundsMachine 0) = some next := by
  exact (freshNextAllocation BoundsMachine 0).evalBundle_write_encodeCfg
    ((freshCurrentLayout BoundsMachine 0).writeCfgBits (fun _ => false)
      (encodeRawCfgBits
        (encodeCfg BoundsMachine boundsSourceAlphabet boundsSourceHeight)))
    hnextAlphabet hnextHeight

/-- Concrete two-row assignment for the genuine immediate-halt step. -/
private abbrev boundsStepInputs : Nat → Bool :=
  boundsInputs boundsHalted boundsHaltedAlphabet boundsHaltedHeight

/-- The same source encoded in both rows, giving an intentionally wrong next row. -/
private abbrev boundsWrongInputs : Nat → Bool :=
  boundsInputs boundsSource boundsSourceAlphabet boundsSourceHeight

private theorem boundsCurrentDecodedStep :
    evalBundle (boundsBase 0) boundsStepInputs (boundsCurrent 0)
      (freshCurrentValid BoundsMachine 0) = some boundsSource := by
  exact boundsCurrentDecoded boundsHalted boundsHaltedAlphabet boundsHaltedHeight

private theorem boundsNextDecodedStep :
    evalBundle (boundsBase 0) boundsStepInputs (boundsNext 0)
      (freshNextValid BoundsMachine 0) = some boundsHalted := by
  exact boundsNextDecoded boundsHalted boundsHaltedAlphabet boundsHaltedHeight

private theorem boundsCurrentDecodedWrong :
    evalBundle (boundsBase 0) boundsWrongInputs (boundsCurrent 0)
      (freshCurrentValid BoundsMachine 0) = some boundsSource := by
  exact boundsCurrentDecoded boundsSource boundsSourceAlphabet boundsSourceHeight

private theorem boundsNextDecodedWrong :
    evalBundle (boundsBase 0) boundsWrongInputs (boundsNext 0)
      (freshNextValid BoundsMachine 0) = some boundsSource := by
  exact boundsNextDecoded boundsSource boundsSourceAlphabet boundsSourceHeight

private theorem boundsSource_ne_step :
    boundsSource ≠ stutterStep BoundsMachine boundsSource := by
  intro h
  have hl := congrArg (fun c => c.l) h
  change some () = none at hl
  contradiction

-- A real allocated row-validity builder closes to a well-formed `Circuit`.
example :
    (validCfgCircuitFinished (boundsBase 0) (boundsCurrent 0)
      (freshCurrentValid BoundsMachine 0)).WellFormed :=
  validCfgCircuit_finish_wellFormed (boundsBase 0) (boundsCurrent 0)
    (freshCurrentValid BoundsMachine 0)

-- A real two-row transition builder closes to a well-formed `Circuit`.
example :
    (transitionCircuitFinished BoundsMachine 1 (boundsBase 1)
      (boundsCurrent 1) (boundsNext 1)
      (freshCurrentValid BoundsMachine 1)
      (freshNextValid BoundsMachine 1)).WellFormed :=
  transitionCircuit_finish_wellFormed BoundsMachine 1 (boundsBase 1)
    (boundsCurrent 1) (boundsNext 1)
    (freshCurrentValid BoundsMachine 1)
    (freshNextValid BoundsMachine 1)

-- A canonical allocated row is accepted by the actual finished validity circuit.
example :
    (validCfgCircuitFinished (boundsBase 0) (boundsCurrent 0)
      (freshCurrentValid BoundsMachine 0)).eval boundsStepInputs = true := by
  rw [validCfgCircuit_finish_eval, validCfgCircuit_eval_iff,
    boundsCurrentDecodedStep]
  rfl

-- Two concretely written rows for the immediate halt satisfy the actual
-- finished transition circuit.
example :
    (transitionCircuitFinished BoundsMachine 0 (boundsBase 0)
      (boundsCurrent 0) (boundsNext 0)
      (freshCurrentValid BoundsMachine 0)
      (freshNextValid BoundsMachine 0)).eval boundsStepInputs = true := by
  rw [transitionCircuit_finish_eval]
  exact (transitionCircuit_eval_iff BoundsMachine 0 (boundsBase 0)
    boundsStepInputs (boundsCurrent 0) (boundsNext 0)
    (freshCurrentValid BoundsMachine 0) (freshNextValid BoundsMachine 0)
    boundsCurrentDecodedStep boundsNextDecodedStep).mpr boundsImmediateHalt

-- Reusing the same real source row as the target is rejected by that finished
-- circuit; this observes the `Circuit.eval` result, not merely its wire bridge.
example :
    (transitionCircuitFinished BoundsMachine 0 (boundsBase 0)
      (boundsCurrent 0) (boundsNext 0)
      (freshCurrentValid BoundsMachine 0)
      (freshNextValid BoundsMachine 0)).eval boundsWrongInputs = false := by
  rw [transitionCircuit_finish_eval]
  apply Bool.eq_false_of_not_eq_true
  intro haccepted
  exact boundsSource_ne_step
    ((transitionCircuit_eval_iff BoundsMachine 0 (boundsBase 0)
      boundsWrongInputs (boundsCurrent 0) (boundsNext 0)
      (freshCurrentValid BoundsMachine 0) (freshNextValid BoundsMachine 0)
      boundsCurrentDecodedWrong boundsNextDecodedWrong).mp haccepted)

-- Finishing is only packaging: it preserves the selected wire evaluation.
example (inputs : Nat → Bool) :
    (transitionCircuitFinished BoundsMachine 0 (boundsBase 0)
      (boundsCurrent 0) (boundsNext 0)
      (freshCurrentValid BoundsMachine 0)
      (freshNextValid BoundsMachine 0)).eval inputs =
    (transitionCircuit BoundsMachine 0 (boundsBase 0)
      (boundsCurrent 0) (boundsNext 0)
      (freshCurrentValid BoundsMachine 0)
      (freshNextValid BoundsMachine 0)).builder.evalWire inputs
        (transitionCircuit BoundsMachine 0 (boundsBase 0)
          (boundsCurrent 0) (boundsNext 0)
          (freshCurrentValid BoundsMachine 0)
          (freshNextValid BoundsMachine 0)).wire :=
  transitionCircuit_finish_eval BoundsMachine 0 (boundsBase 0)
    (boundsCurrent 0) (boundsNext 0)
    (freshCurrentValid BoundsMachine 0)
    (freshNextValid BoundsMachine 0) inputs

end

end CLRS.Chapter34.Turing.CookLevin
