import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearForms

/-!
# Semantics of recursive branch-free affine statement forms

This module identifies the generated affine phase list with the existing
builder-free `transitionStmtScript`.  The padding predicate mirrors the
recursive contexts and will later be discharged uniformly from the verifier's
machine-static action padding.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Every recursive context in a branch-free spine has enough public stack
front to expose its possible `peek` and `pop` operands. -/
def transitionStmtLinearContextPadding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) → Prop
  | context, halt, _ => ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height
  | context, goto _, _ => ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k, stmtPushSet tm continuation k ⊆
          reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      (∀ k, 2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtLinearContextPadding tm seed
        (context.afterLoad tm update) continuation hcontinuation
  | context, push k emit continuation, hsupport =>
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let table : Fin (stateCount tm) →
          Fin (reachableAlphabet tm k).card := fun code =>
        encodeSupportedSymbol
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport k
            simp [stmtPushSet]⟩
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtLinearContextPadding tm seed
        (context.afterPush tm k table) continuation hcontinuation
  | context, peek k update continuation, hsupport =>
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtLinearContextPadding tm seed
        (context.afterPeek tm k update) continuation hcontinuation
  | context, pop k update continuation, hsupport =>
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (∀ j, 2 * (transitionStmtStackActionsFor tm j
        context.stackActions).length + 1 ≤ seed.height) ∧
      transitionStmtLinearContextPadding tm seed
        (context.afterPop tm k update) continuation hcontinuation
  | _, branch _ _ _, _ => False

private theorem optionToList_map {A B : Type} (f : A → B)
    (value : Option A) :
    value.toList.map f = (value.map f).toList := by
  cases value <;> rfl

/-- Evaluation of a successfully generated branch-free form list is exactly
the established semantic statement script from the context row. -/
theorem transitionStmtLinearContextPhaseForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hpadding : transitionStmtLinearContextPadding tm seed context q hsupport)
    (forms : List TransitionAffineStmtPhaseForm)
    (hforms : transitionStmtLinearContextPhaseForms tm labelOffset context q
      hsupport = some forms) :
    forms.map (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtScript tm (workHeight tm seed.height) seed.start
        (seed.start + 1)
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        (context.rowWires tm seed labelOffset) q hsupport := by
  induction q generalizing context forms with
  | halt =>
      simp [transitionStmtLinearContextPhaseForms] at hforms
      subst forms
      rfl
  | goto jump =>
      simp only [transitionStmtLinearContextPhaseForms,
        Option.some.injEq] at hforms
      subst forms
      have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
        labelOffset context (.goto jump) hsupport hpadding
      simpa [transitionStmtContextHeadPhaseForm, transitionStmtHeadPhase,
        transitionStmtScript, optionToList_map] using
        congrArg Option.toList hhead
  | load update continuation ih =>
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ k, stmtPushSet tm continuation k ⊆
          reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearContextPhaseForms] at hforms
      cases hrest : transitionStmtLinearContextPhaseForms tm labelOffset
          (context.afterLoad tm update) continuation hcontinuation with
      | none => simp [hrest] at hforms
      | some rest =>
          rw [hrest] at hforms
          simp only [Option.map_some, Option.some.injEq] at hforms
          subst forms
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
          rw [List.map_append]
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
          rw [htail]
          rfl
  | push k emit continuation ih =>
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm k := fun code =>
        ⟨emit ((stateEquivFin tm).symm code), by
          apply hsupport k
          simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      simp only [transitionStmtLinearContextPhaseForms] at hforms
      change Option.map
          ((transitionStmtContextHeadPhaseForm tm labelOffset context
            (.push k emit continuation) hsupport).toList ++ ·)
          (transitionStmtLinearContextPhaseForms tm labelOffset
            (context.afterPush tm k table) continuation hcontinuation) =
        some forms at hforms
      cases hrest : transitionStmtLinearContextPhaseForms tm labelOffset
          (context.afterPush tm k table) continuation hcontinuation with
      | none => simp [hrest] at hforms
      | some rest =>
          rw [hrest] at hforms
          simp only [Option.map_some, Option.some.injEq] at hforms
          subst forms
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
          rw [List.map_append]
          have hheadList := congrArg Option.toList hhead
          rw [show (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.push k emit continuation) hsupport).toList.map
                (fun phase => phase.eval (transitionTailAffineSeed seed)) =
              (transitionStmtHeadPhase tm (workHeight tm seed.height)
                ((seed.start + labelOffset.eval seed.height) +
                  context.gateOffset.eval (workHeight tm seed.height))
                seed.start (seed.start + 1)
                (context.rowWires tm seed labelOffset)
                (.push k emit continuation) hsupport).toList by
            simpa [optionToList_map] using hheadList]
          rw [htail]
          rfl
  | peek k update continuation ih =>
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearContextPhaseForms] at hforms
      change Option.map
          ((transitionStmtContextHeadPhaseForm tm labelOffset context
            (.peek k update continuation) hsupport).toList ++ ·)
          (transitionStmtLinearContextPhaseForms tm labelOffset
            (context.afterPeek tm k update) continuation hcontinuation) =
        some forms at hforms
      cases hrest : transitionStmtLinearContextPhaseForms tm labelOffset
          (context.afterPeek tm k update) continuation hcontinuation with
      | none => simp [hrest] at hforms
      | some rest =>
          rw [hrest] at hforms
          simp only [Option.map_some, Option.some.injEq] at hforms
          subst forms
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
          rw [List.map_append]
          have hheadList := congrArg Option.toList hhead
          rw [show (transitionStmtContextHeadPhaseForm tm labelOffset context
                (.peek k update continuation) hsupport).toList.map
                (fun phase => phase.eval (transitionTailAffineSeed seed)) =
              (transitionStmtHeadPhase tm (workHeight tm seed.height)
                ((seed.start + labelOffset.eval seed.height) +
                  context.gateOffset.eval (workHeight tm seed.height))
                seed.start (seed.start + 1)
                (context.rowWires tm seed labelOffset)
                (.peek k update continuation) hsupport).toList by
            simpa [optionToList_map] using hheadList]
          rw [htail]
          rfl
  | pop k update continuation ih =>
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      simp only [transitionStmtLinearContextPhaseForms] at hforms
      change Option.map
          (transitionStmtContextPopPhaseForms tm labelOffset context k
            update ++ ·)
          (transitionStmtLinearContextPhaseForms tm labelOffset
            (context.afterPop tm k update) continuation hcontinuation) =
        some forms at hforms
      cases hrest : transitionStmtLinearContextPhaseForms tm labelOffset
          (context.afterPop tm k update) continuation hcontinuation with
      | none => simp [hrest] at hforms
      | some rest =>
          rw [hrest] at hforms
          simp only [Option.map_some, Option.some.injEq] at hforms
          subst forms
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
          rw [List.map_append, hblock, htail]
          have hwork : 0 < workHeight tm seed.height := by
            have hk := hcurrent k
            unfold workHeight
            omega
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
      exact False.elim hpadding

end CLRS.Chapter34.Turing.CookLevin
