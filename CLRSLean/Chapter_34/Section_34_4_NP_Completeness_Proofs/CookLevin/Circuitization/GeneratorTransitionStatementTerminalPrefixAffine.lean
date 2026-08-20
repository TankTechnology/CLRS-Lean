import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalValues
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidenedFallbackAffine

/-!
# Affine source forms for terminal-statement prefixes

The halted, label, and state fields of a normalized terminal statement row
are verifier-fixed affine functions of a transition-row seed.  This module
records their fixed forms and proves exact agreement with the structured
terminal-row values.  Stack blocks are deliberately left to a separate
compiler boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Fixed affine source of the halted coordinate selected by a terminal. -/
def transitionStmtTerminalHaltedForm
    (tm : _root_.Turing.FinTM2) :
    TransitionStmtTerminal tm → AffineUnaryTripleForm
  | .halt => transitionAbsoluteStartForm (TransitionAffineNat.const 1)
  | .goto _ => transitionAbsoluteStartForm (TransitionAffineNat.const 0)

/-- The halted form evaluates to the terminal's Boolean-pool coordinate. -/
theorem transitionStmtTerminalHaltedForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (terminal : TransitionStmtTerminal tm) :
    affineUnaryTripleFormValue
        (transitionStmtTerminalHaltedForm tm terminal)
        (transitionTailAffineSeed seed) =
      terminal.haltedWire tm seed.start (seed.start + 1) := by
  cases terminal <;>
    simp [transitionStmtTerminalHaltedForm,
      TransitionStmtTerminal.haltedWire, arithmeticLabelHaltedWire,
      transitionAbsoluteStartForm_value, labelHalted]

/-- Fixed affine forms of the complete label family. -/
noncomputable def transitionStmtTerminalLabelForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalLayout tm) :
    List AffineUnaryTripleForm :=
  match layout.terminal with
  | .halt =>
      List.ofFn fun target : Fin (labelCount tm + 1) =>
        if target = encodeLabel tm (none : Option tm.Λ) then
          transitionAbsoluteStartForm (TransitionAffineNat.const 1)
        else transitionAbsoluteStartForm (TransitionAffineNat.const 0)
  | .goto jump =>
      List.ofFn fun target : Fin (labelCount tm + 1) =>
        transitionAbsoluteStartForm
          ((labelOffset.add
              (layout.offset.shiftInput (maxPushesPerStep tm))).add
            (TransitionAffineNat.const
              (oneHotMapWireOffset (stmtLabelTable tm jump) target)))

/-- Evaluating the label forms gives exactly the normalized terminal label
coordinates at the runtime statement start. -/
theorem transitionStmtTerminalLabelForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalLayout tm) :
    affineUnaryTripleMap
        (transitionStmtTerminalLabelForms tm labelOffset layout)
        (transitionTailAffineSeed seed) =
      List.ofFn (layout.terminal.labelWires tm seed.start (seed.start + 1)
        ((seed.start + labelOffset.eval seed.height) +
          layout.offset.eval (workHeight tm seed.height))) := by
  rcases layout with ⟨offset, terminal⟩
  cases terminal with
  | halt =>
      unfold affineUnaryTripleMap transitionStmtTerminalLabelForms
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext target
      simp only [TransitionStmtTerminal.labelWires, arithmeticLabelWires]
      by_cases htarget : target = encodeLabel tm (none : Option tm.Λ) <;>
        simp [htarget, transitionAbsoluteStartForm_value,
          TransitionAffineNat.const, TransitionAffineNat.eval]
  | goto jump =>
      unfold affineUnaryTripleMap transitionStmtTerminalLabelForms
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext target
      simp [TransitionStmtTerminal.labelWires,
        transitionAbsoluteStartForm_value, TransitionAffineNat.eval_add,
        TransitionAffineNat.eval_shiftInput, workHeight]
      ring

/-- Fixed affine forms of the complete state family. -/
noncomputable def transitionStmtTerminalStateForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat) :
    TransitionStmtStateLayout tm → List AffineUnaryTripleForm
  | .source =>
      List.ofFn fun target : Fin (stateCount tm) =>
        transitionAbsoluteRowBaseForm
          (TransitionAffineNat.const
            (1 + (labelCount tm + 1) + target.val))
  | .fixed offsets =>
      List.ofFn fun target : Fin (stateCount tm) =>
        transitionAbsoluteStartForm
          (labelOffset.add
            ((offsets target).shiftInput (maxPushesPerStep tm)))

/-- Evaluating the state forms gives exactly the normalized state family. -/
theorem transitionStmtTerminalStateForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtStateLayout tm) :
    affineUnaryTripleMap
        (transitionStmtTerminalStateForms tm labelOffset layout)
        (transitionTailAffineSeed seed) =
      List.ofFn (layout.wires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)) := by
  cases layout with
  | source =>
      unfold affineUnaryTripleMap transitionStmtTerminalStateForms
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext target
      change affineUnaryTripleFormValue
          (transitionAbsoluteRowBaseForm
            (TransitionAffineNat.const
              (1 + (labelCount tm + 1) + target.val)))
          (transitionTailAffineSeed seed) =
        (arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).state target
      rw [transitionAbsoluteRowBaseForm_value]
      simp only [TransitionAffineNat.const, TransitionAffineNat.eval,
        zero_mul, Nat.add_zero]
      rw [arithmeticWidenedCfgWires_state]
  | fixed offsets =>
      unfold affineUnaryTripleMap transitionStmtTerminalStateForms
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext target
      simp [TransitionStmtStateLayout.wires, transitionAbsoluteStartForm_value,
        TransitionAffineNat.eval_add, TransitionAffineNat.eval_shiftInput,
        workHeight]
      ring

/-- Complete fixed form table of one terminal row's halted/label/state
prefix. -/
noncomputable def transitionStmtTerminalPrefixForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    List AffineUnaryTripleForm :=
  transitionStmtTerminalHaltedForm tm layout.terminal.terminal ::
    transitionStmtTerminalLabelForms tm labelOffset layout.terminal ++
    transitionStmtTerminalStateForms tm labelOffset layout.state

/-- The complete fixed form table evaluates literally to the structured
terminal prefix row. -/
theorem transitionStmtTerminalPrefixForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm) :
    affineUnaryTripleMap
        (transitionStmtTerminalPrefixForms tm labelOffset layout)
        (transitionTailAffineSeed seed) =
      layout.prefixValues tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase) := by
  unfold transitionStmtTerminalPrefixForms
    TransitionStmtTerminalRowLayout.prefixValues
  rw [show affineUnaryTripleMap
      (transitionStmtTerminalHaltedForm tm layout.terminal.terminal ::
          transitionStmtTerminalLabelForms tm labelOffset layout.terminal ++
        transitionStmtTerminalStateForms tm labelOffset layout.state)
      (transitionTailAffineSeed seed) =
        affineUnaryTripleFormValue
            (transitionStmtTerminalHaltedForm tm layout.terminal.terminal)
            (transitionTailAffineSeed seed) ::
          affineUnaryTripleMap
              (transitionStmtTerminalLabelForms tm labelOffset layout.terminal)
              (transitionTailAffineSeed seed) ++
            affineUnaryTripleMap
              (transitionStmtTerminalStateForms tm labelOffset layout.state)
              (transitionTailAffineSeed seed) by
        simp [affineUnaryTripleMap]]
  rw [transitionStmtTerminalHaltedForm_value,
    transitionStmtTerminalLabelForms_value,
    transitionStmtTerminalStateForms_value]

end CLRS.Chapter34.Turing.CookLevin
