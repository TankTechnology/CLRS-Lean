import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalForms
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionCfgStructuredValues

/-!
# Complete routed rows of normalized statement terminals

The fixed affine prefix is joined with the existing compact affine route of
each stack.  This produces the complete canonical true/false arm row required
by a whole-row branch mux without rebuilding stack operations.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Complete routed stack blocks in the machine's canonical stack order. -/
noncomputable def TransitionStmtLinearResult.stackRouteBlocks
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) : List (List Nat) :=
  (arithmeticRuntimeStackSourceIndices tm).map fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    (result.context.stackRoute tm labelOffset k).eval seed
      (TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k))
      |>.flatten

/-- Prefix plus stack routes, flattened in canonical configuration order. -/
noncomputable def TransitionStmtLinearResult.completeRouteValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) : List Nat :=
  result.prefixValues tm seed labelOffset ++
    (result.stackRouteBlocks tm seed labelOffset).flatten

/-- The normalized fixed prefix is the generic configuration prefix. -/
theorem TransitionStmtLinearResult.prefixValues_eq_cfgPrefix
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm) :
    result.prefixValues tm seed labelOffset =
      transitionCfgPrefixWireValues tm (workHeight tm seed.height)
        (result.outputWires tm
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)) := by
  unfold TransitionStmtLinearResult.prefixValues
    transitionCfgPrefixWireValues transitionEqPrefixSlots
  rw [List.map_append, List.map_cons, List.map_ofFn, List.map_ofFn]
  rfl

/-- Every compact stack route evaluates to the corresponding stack block of
the normalized arm output. -/
theorem TransitionStmtLinearResult.stackRouteBlocks_eq_cfgStacks
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm)
    (hcapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        result.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    result.stackRouteBlocks tm seed labelOffset =
      transitionCfgStackWireBlocks tm (workHeight tm seed.height)
        (result.outputWires tm
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)) := by
  unfold TransitionStmtLinearResult.stackRouteBlocks
    transitionCfgStackWireBlocks
  apply List.map_congr_left
  intro position hposition
  let k := (arithmeticStackEquiv tm).symm position
  have hroute := result.context.stackRoute_eval tm seed labelOffset k
    (hcapacity k)
  change
    ((result.context.stackRoute tm labelOffset k).eval seed
      (TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k))).flatten =
      transitionStackWireValues
        ((result.outputWires tm
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase)).stack k)
  rw [hroute]
  simp [TransitionStmtLinearResult.outputWires]

/-- The complete routed arm is literally the canonical configuration row. -/
theorem TransitionStmtLinearResult.completeRouteValues_eq_canonical
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (result : TransitionStmtLinearResult tm)
    (hcapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        result.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    result.completeRouteValues tm seed labelOffset =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (result.outputWires tm
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)) := by
  rw [← transitionCfgStructuredWireValues_eq_canonical]
  unfold TransitionStmtLinearResult.completeRouteValues
    transitionCfgStructuredWireValues
  rw [result.prefixValues_eq_cfgPrefix,
    result.stackRouteBlocks_eq_cfgStacks tm seed labelOffset hcapacity]

/-- Direct branch-arm bridge: the complete prefix/stack route is exactly the
canonical output row of the original branch-free statement. -/
theorem transitionStmtLinearResult_completeRouteValues_eq_output
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (result : TransitionStmtLinearResult tm)
    (hresult : transitionStmtLinearResult tm context q hsupport =
      some result)
    (hcapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        result.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    result.completeRouteValues tm seed labelOffset =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          ((seed.start + labelOffset.eval seed.height) +
            context.gateOffset.eval (workHeight tm seed.height))
          (context.rowWires tm seed labelOffset) q hsupport) := by
  rw [result.completeRouteValues_eq_canonical tm seed labelOffset hcapacity]
  have houtput := transitionStmtLinearResult_outputWires tm
    (workHeight tm seed.height) hwork
    (seed.start + labelOffset.eval seed.height) seed.start (seed.start + 1)
    (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
    context q hsupport result hresult
  unfold TransitionStmtAffineContext.rowWires at houtput ⊢
  rw [houtput]

end CLRS.Chapter34.Turing.CookLevin
