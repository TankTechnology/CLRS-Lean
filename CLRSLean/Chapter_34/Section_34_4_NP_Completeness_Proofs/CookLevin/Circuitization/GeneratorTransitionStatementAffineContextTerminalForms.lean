import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminal

/-!
# Affine prefix forms of normalized statement terminals

The halted, label, and state coordinates of a normalized branch arm are fixed
affine functions of the enclosing transition seed.  Stack coordinates remain
in the context's compact route and are joined in the following mux-source
layer.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Affine forms of the terminal label family at the final context start. -/
noncomputable def TransitionStmtLinearResult.labelForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    List AffineUnaryTripleForm :=
  match result.terminal with
  | .halt =>
      List.ofFn fun target : Fin (labelCount tm + 1) =>
        if target = encodeLabel tm (none : Option tm.Λ) then
          transitionAbsoluteStartForm (TransitionAffineNat.const 1)
        else transitionAbsoluteStartForm (TransitionAffineNat.const 0)
  | .goto jump =>
      List.ofFn fun target : Fin (labelCount tm + 1) =>
        transitionAffineFormAddConst
          (result.context.startForm tm labelOffset)
          (oneHotMapWireOffset (stmtLabelTable tm jump) target)

/-- Affine forms of the final state family. -/
noncomputable def TransitionStmtLinearResult.stateForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    List AffineUnaryTripleForm :=
  List.ofFn (result.context.stateForm tm labelOffset)

/-- Complete fixed-width prefix of a normalized arm output row. -/
noncomputable def TransitionStmtLinearResult.prefixForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    List AffineUnaryTripleForm :=
  transitionStmtTerminalHaltedForm tm result.terminal ::
    result.labelForms tm labelOffset ++ result.stateForms tm labelOffset

/-- Runtime halted/label/state prefix of the normalized output row. -/
def TransitionStmtLinearResult.prefixValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) : List Nat :=
  let output := result.outputWires tm
    (seed.start + labelOffset.eval seed.height)
    (workHeight tm seed.height) seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
  output.halted :: List.ofFn output.label ++ List.ofFn output.state

/-- Terminal label forms evaluate to the literal normalized label wires. -/
theorem TransitionStmtLinearResult.labelForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    affineUnaryTripleMap (result.labelForms tm labelOffset)
        (transitionTailAffineSeed seed) =
      let output := result.outputWires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
      List.ofFn output.label := by
  rcases result with ⟨context, terminal⟩
  cases terminal with
  | halt =>
      unfold TransitionStmtLinearResult.labelForms affineUnaryTripleMap
        TransitionStmtLinearResult.outputWires
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext target
      simp only [CfgBundle.replaceStatus_label,
        TransitionStmtTerminal.labelWires, arithmeticLabelWires]
      by_cases htarget :
          target = encodeLabel tm (none : Option tm.Λ) <;>
        simp [htarget, transitionAbsoluteStartForm_value,
          TransitionAffineNat.eval, TransitionAffineNat.const]
  | goto jump =>
      unfold TransitionStmtLinearResult.labelForms affineUnaryTripleMap
        TransitionStmtLinearResult.outputWires
      rw [List.map_ofFn]
      apply List.ofFn_inj.mpr
      funext target
      simp only [CfgBundle.replaceStatus_label,
        TransitionStmtTerminal.labelWires]
      change affineUnaryTripleFormValue
          (transitionAffineFormAddConst
            (context.startForm tm labelOffset)
            (oneHotMapWireOffset (stmtLabelTable tm jump) target))
          (transitionTailAffineSeed seed) = _
      rw [transitionAffineFormAddConst_value,
        context.startForm_value]

/-- State forms evaluate to the literal normalized state wires. -/
theorem TransitionStmtLinearResult.stateForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    affineUnaryTripleMap (result.stateForms tm labelOffset)
        (transitionTailAffineSeed seed) =
      let output := result.outputWires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
      List.ofFn output.state := by
  rcases result with ⟨context, terminal⟩
  unfold TransitionStmtLinearResult.stateForms affineUnaryTripleMap
    TransitionStmtLinearResult.outputWires
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext target
  rw [CfgBundle.replaceStatus_state]
  exact context.stateForm_eq_wires tm seed labelOffset target

/-- The complete fixed prefix form table evaluates byte-for-byte to the
normalized arm's halted/label/state prefix. -/
theorem TransitionStmtLinearResult.prefixForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    affineUnaryTripleMap (result.prefixForms tm labelOffset)
        (transitionTailAffineSeed seed) =
      result.prefixValues tm seed labelOffset := by
  unfold TransitionStmtLinearResult.prefixForms
    TransitionStmtLinearResult.prefixValues
  rw [show affineUnaryTripleMap
      (transitionStmtTerminalHaltedForm tm result.terminal ::
          result.labelForms tm labelOffset ++
            result.stateForms tm labelOffset)
      (transitionTailAffineSeed seed) =
        affineUnaryTripleFormValue
            (transitionStmtTerminalHaltedForm tm result.terminal)
            (transitionTailAffineSeed seed) ::
          affineUnaryTripleMap (result.labelForms tm labelOffset)
              (transitionTailAffineSeed seed) ++
            affineUnaryTripleMap (result.stateForms tm labelOffset)
              (transitionTailAffineSeed seed) by
        simp [affineUnaryTripleMap]]
  rw [transitionStmtTerminalHaltedForm_value,
    result.labelForms_value, result.stateForms_value]
  simp [TransitionStmtLinearResult.outputWires, CfgBundle.halted,
    CfgSlot.halted, CfgBundle.replaceStatus]

/-- Direct semantic bridge: the fixed prefix forms are the halted, label, and
state coordinates of the original branch-free arm output. -/
theorem transitionStmtLinearResult_prefixForms_value_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (result : TransitionStmtLinearResult tm)
    (hresult : transitionStmtLinearResult tm context q hsupport =
      some result) :
    affineUnaryTripleMap (result.prefixForms tm labelOffset)
        (transitionTailAffineSeed seed) =
      let output := transitionStmtOutputWires tm
        (workHeight tm seed.height) seed.start (seed.start + 1)
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        (context.rowWires tm seed labelOffset) q hsupport
      output.halted :: List.ofFn output.label ++ List.ofFn output.state := by
  rw [result.prefixForms_value]
  have houtput := transitionStmtLinearResult_outputWires tm
    (workHeight tm seed.height) hwork
    (seed.start + labelOffset.eval seed.height) seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    context q hsupport result hresult
  unfold TransitionStmtLinearResult.prefixValues
  unfold TransitionStmtAffineContext.rowWires
  rw [houtput]

end CLRS.Chapter34.Turing.CookLevin
