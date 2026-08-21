import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextPrefixTerminalBranchPadding

/-!
# Complete scripts for affine prefixes ending in a terminal branch

The direct branch theorem is lifted through every linear TM2 statement
constructor.  This closes arbitrary `load`/`push`/`peek`/`pop` prefixes before
a branch with branch-free arms.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Evaluated prefix phases followed by the complete final branch. -/
def TransitionStmtPrefixTerminalBranchPlan.completePhases
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    List AffineStmtPhase :=
  plan.prefixForms.map
      (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
    plan.branchPlan.completePhases tm seed labelOffset plan.branchContext
      plan.test plan.whenTrue plan.whenFalse plan.branchSupport

private theorem optionToList_map {A B : Type} (f : A → B)
    (value : Option A) :
    value.toList.map f = (value.map f).toList := by
  cases value <;> rfl

/-- A successful prefix-terminal-branch plan evaluates phase-for-phase to the
original recursive statement script. -/
theorem transitionStmtPrefixTerminalBranchPlan_completePhases_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtPrefixTerminalBranchPadding tm seed context q hsupport →
      ∀ (plan : TransitionStmtPrefixTerminalBranchPlan tm),
        transitionStmtPrefixTerminalBranchPlan tm labelOffset context q
            hsupport = some plan →
        plan.completePhases tm seed labelOffset =
          transitionStmtScript tm (workHeight tm seed.height) seed.start
            (seed.start + 1)
            ((seed.start + labelOffset.eval seed.height) +
              context.gateOffset.eval (workHeight tm seed.height))
            (context.rowWires tm seed labelOffset) q hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hpadding
      exact False.elim hpadding
  | goto jump =>
      intro hsupport hpadding
      exact False.elim hpadding
  | load update continuation ih =>
      intro hsupport hpadding plan hplan
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtPrefixTerminalBranchPlan] at hplan
      cases hrest : transitionStmtPrefixTerminalBranchPlan tm labelOffset
          (context.afterLoad tm update) continuation hcontinuation with
      | none => simp [hrest] at hplan
      | some rest =>
          rw [hrest] at hplan
          simp only [Option.map_some, Option.some.injEq] at hplan
          subst plan
          have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm
            seed labelOffset context (.load update continuation) hsupport
              hcurrent
          have htail := ih (context.afterLoad tm update) hcontinuation
            htailPadding rest hrest
          have hsource := context.afterLoad_wires tm
            (seed.start + labelOffset.eval seed.height)
            (workHeight tm seed.height) seed.start (seed.start + 1)
            (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
            update
          unfold TransitionStmtAffineContext.rowWires at htail
          rw [hsource] at htail
          have hstart :
              (seed.start + labelOffset.eval seed.height) +
                  (context.afterLoad tm update).gateOffset.eval
                    (workHeight tm seed.height) =
                ((seed.start + labelOffset.eval seed.height) +
                    context.gateOffset.eval (workHeight tm seed.height)) +
                  stateCount tm + stateCount tm := by
            rw [TransitionStmtAffineContext.afterLoad_gateOffset_eval]
            omega
          rw [hstart] at htail
          simp only [TransitionStmtPrefixTerminalBranchPlan.completePhases,
            List.map_append, List.append_assoc]
          rw [show (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.load update continuation) hsupport).toList.map
                (fun phase => phase.eval (transitionTailAffineSeed seed)) =
              (transitionStmtHeadPhase tm (workHeight tm seed.height)
                ((seed.start + labelOffset.eval seed.height) +
                  context.gateOffset.eval (workHeight tm seed.height))
                seed.start (seed.start + 1)
                (context.rowWires tm seed labelOffset)
                (.load update continuation) hsupport).toList by
            simpa [optionToList_map] using congrArg Option.toList hhead]
          rw [← TransitionStmtPrefixTerminalBranchPlan.completePhases,
            htail]
          rfl
  | push k emit continuation ih =>
      intro hsupport hpadding plan hplan
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      simp only [transitionStmtPrefixTerminalBranchPlan] at hplan
      change Option.map _
          (transitionStmtPrefixTerminalBranchPlan tm labelOffset
            (context.afterPush tm k table) continuation hcontinuation) =
        some plan at hplan
      cases hrest : transitionStmtPrefixTerminalBranchPlan tm labelOffset
          (context.afterPush tm k table) continuation hcontinuation with
      | none => simp [hrest] at hplan
      | some rest =>
          rw [hrest] at hplan
          simp only [Option.map_some, Option.some.injEq] at hplan
          subst plan
          have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm
            seed labelOffset context (.push k emit continuation) hsupport
              hcurrent
          have htail := ih (context.afterPush tm k table) hcontinuation
            htailPadding rest hrest
          have hsource := context.afterPush_wires tm
            (seed.start + labelOffset.eval seed.height)
            (workHeight tm seed.height) seed.start (seed.start + 1)
            (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
            k table
          unfold TransitionStmtAffineContext.rowWires at htail
          rw [hsource] at htail
          have hstart :
              (seed.start + labelOffset.eval seed.height) +
                  (context.afterPush tm k table).gateOffset.eval
                    (workHeight tm seed.height) =
                ((seed.start + labelOffset.eval seed.height) +
                    context.gateOffset.eval (workHeight tm seed.height)) +
                  stateCount tm + (reachableAlphabet tm k).card := by
            rw [TransitionStmtAffineContext.afterPush_gateOffset_eval]
            omega
          rw [hstart] at htail
          simp only [TransitionStmtPrefixTerminalBranchPlan.completePhases,
            List.map_append, List.append_assoc]
          rw [show (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.push k emit continuation) hsupport).toList.map
                (fun phase => phase.eval (transitionTailAffineSeed seed)) =
              (transitionStmtHeadPhase tm (workHeight tm seed.height)
                ((seed.start + labelOffset.eval seed.height) +
                  context.gateOffset.eval (workHeight tm seed.height))
                seed.start (seed.start + 1)
                (context.rowWires tm seed labelOffset)
                (.push k emit continuation) hsupport).toList by
            simpa [optionToList_map] using congrArg Option.toList hhead]
          rw [← TransitionStmtPrefixTerminalBranchPlan.completePhases,
            htail]
          rfl
  | peek k update continuation ih =>
      intro hsupport hpadding plan hplan
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtPrefixTerminalBranchPlan] at hplan
      change Option.map _
          (transitionStmtPrefixTerminalBranchPlan tm labelOffset
            (context.afterPeek tm k update) continuation hcontinuation) =
        some plan at hplan
      cases hrest : transitionStmtPrefixTerminalBranchPlan tm labelOffset
          (context.afterPeek tm k update) continuation hcontinuation with
      | none => simp [hrest] at hplan
      | some rest =>
          rw [hrest] at hplan
          simp only [Option.map_some, Option.some.injEq] at hplan
          subst plan
          have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm
            seed labelOffset context (.peek k update continuation) hsupport
              hcurrent
          have htail := ih (context.afterPeek tm k update) hcontinuation
            htailPadding rest hrest
          unfold TransitionStmtAffineContext.rowWires at htail
          rw [context.afterPeek_wires tm
            (seed.start + labelOffset.eval seed.height)
            (workHeight tm seed.height) seed.start (seed.start + 1)
            (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
            k update] at htail
          have hstart :
              (seed.start + labelOffset.eval seed.height) +
                  (context.afterPeek tm k update).gateOffset.eval
                    (workHeight tm seed.height) =
                ((seed.start + labelOffset.eval seed.height) +
                    context.gateOffset.eval (workHeight tm seed.height)) +
                  2 * stateCount tm * ((reachableAlphabet tm k).card + 1) +
                    stateCount tm := by
            rw [TransitionStmtAffineContext.afterPeek_gateOffset_eval]
            omega
          rw [hstart] at htail
          simp only [TransitionStmtPrefixTerminalBranchPlan.completePhases,
            List.map_append, List.append_assoc]
          rw [show (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.peek k update continuation) hsupport).toList.map
                (fun phase => phase.eval (transitionTailAffineSeed seed)) =
              (transitionStmtHeadPhase tm (workHeight tm seed.height)
                ((seed.start + labelOffset.eval seed.height) +
                  context.gateOffset.eval (workHeight tm seed.height))
                seed.start (seed.start + 1)
                (context.rowWires tm seed labelOffset)
                (.peek k update continuation) hsupport).toList by
            simpa [optionToList_map] using congrArg Option.toList hhead]
          rw [← TransitionStmtPrefixTerminalBranchPlan.completePhases,
            htail]
          rfl
  | pop k update continuation ih =>
      intro hsupport hpadding plan hplan
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtPrefixTerminalBranchPlan] at hplan
      change Option.map _
          (transitionStmtPrefixTerminalBranchPlan tm labelOffset
            (context.afterPop tm k update) continuation hcontinuation) =
        some plan at hplan
      cases hrest : transitionStmtPrefixTerminalBranchPlan tm labelOffset
          (context.afterPop tm k update) continuation hcontinuation with
      | none => simp [hrest] at hplan
      | some rest =>
          rw [hrest] at hplan
          simp only [Option.map_some, Option.some.injEq] at hplan
          subst plan
          have hblock := transitionStmtContextPopPhaseForms_eval tm seed
            labelOffset context k update (hcurrent k)
          have htail := ih (context.afterPop tm k update) hcontinuation
            htailPadding rest hrest
          unfold TransitionStmtAffineContext.rowWires at htail
          rw [context.afterPop_wires tm
            (seed.start + labelOffset.eval seed.height)
            (workHeight tm seed.height) seed.start (seed.start + 1)
            (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
            k update] at htail
          have hstart :
              (seed.start + labelOffset.eval seed.height) +
                  (context.afterPop tm k update).gateOffset.eval
                    (workHeight tm seed.height) =
                ((seed.start + labelOffset.eval seed.height) +
                    context.gateOffset.eval (workHeight tm seed.height)) + 1 +
                  (2 * stateCount tm *
                    ((reachableAlphabet tm k).card + 1) + stateCount tm) := by
            rw [TransitionStmtAffineContext.afterPop_gateOffset_eval]
            omega
          rw [hstart] at htail
          simp only [TransitionStmtPrefixTerminalBranchPlan.completePhases,
            List.map_append, List.append_assoc]
          rw [hblock]
          rw [← TransitionStmtPrefixTerminalBranchPlan.completePhases,
            htail]
          have hpopCost :
              popStackWireGateCost (workHeight tm seed.height) = 1 := by
            cases hworkspace : workHeight tm seed.height with
            | zero => omega
            | succ workspace => rfl
          simp only [transitionStmtContextPopPhaseBlock,
            transitionStmtScript]
          rw [hpopCost]
          rfl
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hpadding plan hplan
      rcases hpadding with ⟨hcurrent, htruePadding, hfalsePadding⟩
      simp only [transitionStmtPrefixTerminalBranchPlan] at hplan
      cases hbranch : transitionStmtTerminalBranchPlan tm labelOffset context
          test whenTrue whenFalse hsupport with
      | none => simp [hbranch] at hplan
      | some branchPlan =>
          rw [hbranch] at hplan
          simp only [Option.map_some, Option.some.injEq] at hplan
          subst plan
          simpa [TransitionStmtPrefixTerminalBranchPlan.completePhases] using
            transitionStmtTerminalBranchPlan_completePhases_eq_script tm seed
              hwork labelOffset context test whenTrue whenFalse hsupport
              branchPlan hbranch hcurrent htruePadding hfalsePadding

end CLRS.Chapter34.Turing.CookLevin
