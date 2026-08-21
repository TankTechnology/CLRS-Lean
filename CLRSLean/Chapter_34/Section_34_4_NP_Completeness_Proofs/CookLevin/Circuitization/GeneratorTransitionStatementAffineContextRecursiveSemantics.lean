import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursivePadding

/-!
# Exact phase semantics for arbitrary nested statements

This is the recursive statement-generator closure theorem.  The generated
phase list follows every primitive continuation, recursively compiles both
arms of every branch, and finally emits the parent whole-row mux.  Its main
theorem identifies that list with the pre-existing semantic
`transitionStmtScript` for statements of unrestricted branch depth.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

private theorem recursive_optionToList_map {A B : Type} (f : A → B)
    (value : Option A) :
    value.toList.map f = (value.map f).toList := by
  cases value <;> rfl

/-- Runtime phase list generated recursively from fixed affine forms and
canonical mux invocation views. -/
noncomputable def transitionStmtRecursivePhases
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    (context : TransitionStmtAffineContext tm) →
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) →
    (∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) →
      List AffineStmtPhase
  | _, halt, _ => []
  | context, goto jump, hsupport =>
      (transitionStmtContextHeadPhaseForm tm labelOffset context
        (.goto jump) hsupport).toList.map
          (fun phase => phase.eval (transitionTailAffineSeed seed))
  | context, load update continuation, hsupport =>
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtContextHeadPhaseForm tm labelOffset context
          (.load update continuation) hsupport).toList.map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
        transitionStmtRecursivePhases tm seed labelOffset
          (context.afterLoad tm update) continuation hcontinuation
  | context, push k emit continuation, hsupport =>
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
      (transitionStmtContextHeadPhaseForm tm labelOffset context
          (.push k emit continuation) hsupport).toList.map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
        transitionStmtRecursivePhases tm seed labelOffset
          (context.afterPush tm k table) continuation hcontinuation
  | context, peek k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtContextHeadPhaseForm tm labelOffset context
          (.peek k update continuation) hsupport).toList.map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
        transitionStmtRecursivePhases tm seed labelOffset
          (context.afterPeek tm k update) continuation hcontinuation
  | context, pop k update continuation, hsupport =>
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      (transitionStmtContextPopPhaseForms tm labelOffset context k update).map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
        transitionStmtRecursivePhases tm seed labelOffset
          (context.afterPop tm k update) continuation hcontinuation
  | context, branch test whenTrue whenFalse, hsupport =>
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      let view := transitionStmtRecursiveBranchMuxInvocationView tm seed
        labelOffset context test whenTrue whenFalse hsupport
      (transitionStmtContextHeadPhaseForm tm labelOffset context
          (.branch test whenTrue whenFalse) hsupport).toList.map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
        transitionStmtRecursivePhases tm seed labelOffset
          (transitionStmtBranchTrueContext tm context test) whenTrue
          htrueSupport ++
        transitionStmtRecursivePhases tm seed labelOffset
          (transitionStmtBranchFalseContext tm context test whenTrue)
          whenFalse hfalseSupport ++
        [.mux view.selector view.frames]

/-- Recursive affine generation is phase-for-phase the established semantic
statement script, with no restriction on branch depth. -/
theorem transitionStmtRecursivePhases_eq_script
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtRecursiveContextPadding tm seed context q hsupport →
      transitionStmtRecursivePhases tm seed labelOffset context q hsupport =
        transitionStmtScript tm (workHeight tm seed.height) seed.start
          (seed.start + 1)
          ((seed.start + labelOffset.eval seed.height) +
            context.gateOffset.eval (workHeight tm seed.height))
          (context.rowWires tm seed labelOffset) q hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hpadding
      rfl
  | goto jump =>
      intro hsupport hpadding
      have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
        labelOffset context (.goto jump) hsupport hpadding
      unfold transitionStmtRecursivePhases
      rw [recursive_optionToList_map, hhead]
      rfl
  | load update continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ k, stmtPushSet tm continuation k ⊆
          reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
        labelOffset context (.load update continuation) hsupport hcurrent
      have htail := ih (context.afterLoad tm update) hcontinuation
        htailPadding
      unfold TransitionStmtAffineContext.rowWires at htail
      rw [context.afterLoad_wires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        update] at htail
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
      have hheadList :
          (transitionStmtContextHeadPhaseForm tm labelOffset context
              (.load update continuation) hsupport).toList.map
              (fun phase => phase.eval (transitionTailAffineSeed seed)) =
            (transitionStmtHeadPhase tm (workHeight tm seed.height)
              ((seed.start + labelOffset.eval seed.height) +
                context.gateOffset.eval (workHeight tm seed.height))
              seed.start (seed.start + 1)
              (context.rowWires tm seed labelOffset)
              (.load update continuation) hsupport).toList := by
        simpa [recursive_optionToList_map] using congrArg Option.toList hhead
      simp only [transitionStmtRecursivePhases]
      rw [hheadList, htail]
      rfl
  | push k emit continuation ih =>
      intro hsupport hpadding
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
      have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
        labelOffset context (.push k emit continuation) hsupport hcurrent
      have htail := ih (context.afterPush tm k table) hcontinuation
        htailPadding
      unfold TransitionStmtAffineContext.rowWires at htail
      rw [context.afterPush_wires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        k table] at htail
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
      have hheadList :
          (transitionStmtContextHeadPhaseForm tm labelOffset context
              (.push k emit continuation) hsupport).toList.map
              (fun phase => phase.eval (transitionTailAffineSeed seed)) =
            (transitionStmtHeadPhase tm (workHeight tm seed.height)
              ((seed.start + labelOffset.eval seed.height) +
                context.gateOffset.eval (workHeight tm seed.height))
              seed.start (seed.start + 1)
              (context.rowWires tm seed labelOffset)
              (.push k emit continuation) hsupport).toList := by
        simpa [recursive_optionToList_map] using congrArg Option.toList hhead
      simp only [transitionStmtRecursivePhases]
      change _ ++ transitionStmtRecursivePhases tm seed labelOffset
          (context.afterPush tm k table) continuation hcontinuation = _
      rw [hheadList, htail]
      rfl
  | peek k update continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
        labelOffset context (.peek k update continuation) hsupport hcurrent
      have htail := ih (context.afterPeek tm k update) hcontinuation
        htailPadding
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
      have hheadList :
          (transitionStmtContextHeadPhaseForm tm labelOffset context
              (.peek k update continuation) hsupport).toList.map
              (fun phase => phase.eval (transitionTailAffineSeed seed)) =
            (transitionStmtHeadPhase tm (workHeight tm seed.height)
              ((seed.start + labelOffset.eval seed.height) +
                context.gateOffset.eval (workHeight tm seed.height))
              seed.start (seed.start + 1)
              (context.rowWires tm seed labelOffset)
              (.peek k update continuation) hsupport).toList := by
        simpa [recursive_optionToList_map] using congrArg Option.toList hhead
      simp only [transitionStmtRecursivePhases]
      rw [hheadList, htail]
      rfl
  | pop k update continuation ih =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htailPadding⟩
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      have hblock := transitionStmtContextPopPhaseForms_eval tm seed
        labelOffset context k update (hcurrent k)
      have htail := ih (context.afterPop tm k update) hcontinuation
        htailPadding
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
      simp only [transitionStmtRecursivePhases]
      rw [hblock, htail]
      have hpopCost :
          popStackWireGateCost (workHeight tm seed.height) = 1 := by
        cases hworkspace : workHeight tm seed.height with
        | zero => omega
        | succ workspace => rfl
      simp only [transitionStmtContextPopPhaseBlock, transitionStmtScript]
      rw [hpopCost]
      rfl
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hpadding
      rcases hpadding with ⟨hcurrent, htruePadding, hfalsePadding⟩
      let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
        whenFalse hsupport
      let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
        whenFalse hsupport
      let trueContext := transitionStmtBranchTrueContext tm context test
      let falseContext :=
        transitionStmtBranchFalseContext tm context test whenTrue
      have hhead := transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
        labelOffset context (.branch test whenTrue whenFalse) hsupport
        hcurrent
      have htrue := ihTrue trueContext htrueSupport htruePadding
      have hfalse := ihFalse falseContext hfalseSupport hfalsePadding
      have htrueStart :
          (seed.start + labelOffset.eval seed.height) +
              trueContext.gateOffset.eval (workHeight tm seed.height) =
            ((seed.start + labelOffset.eval seed.height) +
                context.gateOffset.eval (workHeight tm seed.height)) +
              ((oneHotTruePreimage
                (stmtPredicateTable tm test)).card + 1) := by
        simp [trueContext, transitionStmtBranchTrueContext,
          transitionStmtBranchPredicateCost,
          TransitionStmtAffineContext.advance,
          TransitionAffineNat.eval_add]
        omega
      have hfalseStart :
          (seed.start + labelOffset.eval seed.height) +
              falseContext.gateOffset.eval (workHeight tm seed.height) =
            ((seed.start + labelOffset.eval seed.height) +
                context.gateOffset.eval (workHeight tm seed.height)) +
              ((oneHotTruePreimage
                (stmtPredicateTable tm test)).card + 1) +
              compileStmtGateCost tm (workHeight tm seed.height) whenTrue := by
        simp [falseContext, transitionStmtBranchFalseContext,
          transitionStmtBranchPredicateCost,
          TransitionStmtAffineContext.advance,
          TransitionAffineNat.eval_add,
          compileStmtGateAffine_eval tm whenTrue
            (workHeight tm seed.height) hwork]
        omega
      rw [htrueStart] at htrue
      rw [hfalseStart] at hfalse
      have htrueRow : trueContext.rowWires tm seed labelOffset =
          context.rowWires tm seed labelOffset := by rfl
      have hfalseRow : falseContext.rowWires tm seed labelOffset =
          context.rowWires tm seed labelOffset := by rfl
      rw [htrueRow] at htrue
      rw [hfalseRow] at hfalse
      have hheadList :
          (transitionStmtContextHeadPhaseForm tm labelOffset context
              (.branch test whenTrue whenFalse) hsupport).toList.map
              (fun phase => phase.eval (transitionTailAffineSeed seed)) =
            (transitionStmtHeadPhase tm (workHeight tm seed.height)
              ((seed.start + labelOffset.eval seed.height) +
                context.gateOffset.eval (workHeight tm seed.height))
              seed.start (seed.start + 1)
              (context.rowWires tm seed labelOffset)
              (.branch test whenTrue whenFalse) hsupport).toList := by
        simpa [recursive_optionToList_map] using congrArg Option.toList hhead
      have htrueCapacity :=
        transitionStmtRecursiveContextPadding_linearResult_capacity tm seed
          trueContext whenTrue htrueSupport htruePadding
      have hfalseCapacity :=
        transitionStmtRecursiveContextPadding_linearResult_capacity tm seed
          falseContext whenFalse hfalseSupport hfalsePadding
      have hframes :=
        transitionStmtRecursiveBranchMuxInvocationView_frames tm seed hwork
          labelOffset context test whenTrue whenFalse hsupport
          htrueCapacity hfalseCapacity
      have hselector := transitionStmtBranchSelectorForm_value tm seed
        labelOffset context test
      have hviewSelector :
          (transitionStmtRecursiveBranchMuxInvocationView tm seed labelOffset
            context test whenTrue whenFalse hsupport).selector =
            transitionStmtBranchSemanticSelector tm seed labelOffset context
              test := by
        simpa [transitionStmtRecursiveBranchMuxInvocationView,
          transitionStmtBranchSemanticSelector] using hselector
      simp only [transitionStmtRecursivePhases]
      change _ ++ transitionStmtRecursivePhases tm seed labelOffset
          trueContext whenTrue htrueSupport ++
        transitionStmtRecursivePhases tm seed labelOffset falseContext
          whenFalse hfalseSupport ++ [_] = _
      rw [hheadList, htrue, hfalse, hviewSelector, hframes]
      simp only [transitionStmtScript]
      unfold transitionStmtBranchSemanticSelector
        transitionStmtBranchSemanticMuxStart
        transitionStmtBranchSemanticTrueWires
        transitionStmtBranchSemanticFalseWires
      rfl

end CLRS.Chapter34.Turing.CookLevin
