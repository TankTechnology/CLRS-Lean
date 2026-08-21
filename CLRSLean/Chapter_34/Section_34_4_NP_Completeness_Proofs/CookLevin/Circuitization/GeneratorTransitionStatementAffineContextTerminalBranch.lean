import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalRoute

/-!
# Affine branch plans with branch-free arms

This is the first complete branch layer of the raw transition-script compiler.
It emits the predicate and both recursively compiled fixed-width arm scripts;
the final height-dependent whole-row mux is deliberately kept as the next
runtime phase and consumes the complete routed arm rows proved previously.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Exact affine cost of the predicate phase at the head of a branch. -/
def transitionStmtBranchPredicateCost
    (tm : _root_.Turing.FinTM2) (test : tm.σ → Bool) :
    TransitionAffineNat :=
  TransitionAffineNat.const
    ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1)

/-- Static branch plan whose two arms terminate in `halt` or `goto`. -/
structure TransitionStmtTerminalBranchPlan (tm : _root_.Turing.FinTM2) where
  trueForms : List TransitionAffineStmtPhaseForm
  falseForms : List TransitionAffineStmtPhaseForm
  trueResult : TransitionStmtLinearResult tm
  falseResult : TransitionStmtLinearResult tm

/-- Predicate followed by the two fixed-width arm scripts. -/
def TransitionStmtTerminalBranchPlan.fixedPhaseForms
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm) :
    List TransitionAffineStmtPhaseForm :=
  (transitionStmtContextHeadPhaseForm tm labelOffset context
      (.branch test whenTrue whenFalse) hsupport).toList ++
    plan.trueForms ++ plan.falseForms

/-- Compile both branch-free arms at their exact post-predicate and
post-true-arm affine contexts. -/
noncomputable def transitionStmtTerminalBranchPlan
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    Option (TransitionStmtTerminalBranchPlan tm) :=
  let htrueSupport :
      ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
    intro k symbol hsymbol
    apply hsupport k
    simp only [stmtPushSet]
    exact Finset.mem_union_left _ hsymbol
  let hfalseSupport :
      ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
    intro k symbol hsymbol
    apply hsupport k
    simp only [stmtPushSet]
    exact Finset.mem_union_right _ hsymbol
  let predicateCost := transitionStmtBranchPredicateCost tm test
  let trueContext := context.advance predicateCost
  let falseContext := context.advance
    (predicateCost.add (compileStmtGateAffine tm whenTrue))
  match transitionStmtLinearContextPhaseForms tm labelOffset trueContext
      whenTrue htrueSupport,
    transitionStmtLinearResult tm trueContext whenTrue htrueSupport,
    transitionStmtLinearContextPhaseForms tm labelOffset falseContext
      whenFalse hfalseSupport,
    transitionStmtLinearResult tm falseContext whenFalse hfalseSupport with
  | some trueForms, some trueResult, some falseForms, some falseResult =>
      some { trueForms, falseForms, trueResult, falseResult }
  | _, _, _, _ => none

/-- A terminal branch plan exists exactly when both arms are branch-free. -/
theorem transitionStmtTerminalBranchPlan_isSome_iff
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    (transitionStmtTerminalBranchPlan tm labelOffset context test whenTrue
      whenFalse hsupport).isSome ↔
      (transitionStmtTerminalLayout tm whenTrue).isSome ∧
        (transitionStmtTerminalLayout tm whenFalse).isSome := by
  let htrueSupport :
      ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
    intro k symbol hsymbol
    apply hsupport k
    simp only [stmtPushSet]
    exact Finset.mem_union_left _ hsymbol
  let hfalseSupport :
      ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
    intro k symbol hsymbol
    apply hsupport k
    simp only [stmtPushSet]
    exact Finset.mem_union_right _ hsymbol
  let predicateCost := transitionStmtBranchPredicateCost tm test
  let trueContext := context.advance predicateCost
  let falseContext := context.advance
    (predicateCost.add (compileStmtGateAffine tm whenTrue))
  rw [show transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport =
    match transitionStmtLinearContextPhaseForms tm labelOffset trueContext
        whenTrue htrueSupport,
      transitionStmtLinearResult tm trueContext whenTrue htrueSupport,
      transitionStmtLinearContextPhaseForms tm labelOffset falseContext
        whenFalse hfalseSupport,
      transitionStmtLinearResult tm falseContext whenFalse hfalseSupport with
    | some trueForms, some trueResult, some falseForms, some falseResult =>
        some { trueForms, falseForms, trueResult, falseResult }
    | _, _, _, _ => none by rfl]
  generalize htf : transitionStmtLinearContextPhaseForms tm labelOffset
    trueContext whenTrue htrueSupport = trueForms
  generalize htr : transitionStmtLinearResult tm trueContext whenTrue
    htrueSupport = trueResult
  generalize hff : transitionStmtLinearContextPhaseForms tm labelOffset
    falseContext whenFalse hfalseSupport = falseForms
  generalize hfr : transitionStmtLinearResult tm falseContext whenFalse
    hfalseSupport = falseResult
  have htfIff := transitionStmtLinearContextPhaseForms_isSome_iff_terminal tm
    labelOffset trueContext whenTrue htrueSupport
  have htrIff := transitionStmtLinearResult_isSome_iff_terminal tm trueContext
    whenTrue htrueSupport
  have hffIff := transitionStmtLinearContextPhaseForms_isSome_iff_terminal tm
    labelOffset falseContext whenFalse hfalseSupport
  have hfrIff := transitionStmtLinearResult_isSome_iff_terminal tm falseContext
    whenFalse hfalseSupport
  rw [htf] at htfIff
  rw [htr] at htrIff
  rw [hff] at hffIff
  rw [hfr] at hfrIff
  cases trueForms <;> cases trueResult <;> cases falseForms <;>
    cases falseResult <;> simp_all

private theorem optionToList_map {A B : Type} (f : A → B)
    (value : Option A) :
    value.toList.map f = (value.map f).toList := by
  cases value <;> rfl

/-- The fixed portion of a terminal branch plan evaluates exactly to the
predicate phase followed by the two semantic arm scripts. -/
theorem transitionStmtTerminalBranchPlan_fixedPhaseForms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (hcurrent : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height)
    (htruePadding : transitionStmtLinearContextPadding tm seed
      (context.advance (transitionStmtBranchPredicateCost tm test))
      whenTrue (by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_left _ hsymbol))
    (hfalsePadding : transitionStmtLinearContextPadding tm seed
      (context.advance
        ((transitionStmtBranchPredicateCost tm test).add
          (compileStmtGateAffine tm whenTrue)))
      whenFalse (by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol)) :
    (plan.fixedPhaseForms tm labelOffset context test whenTrue whenFalse
        hsupport).map
        (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      let currentStart :=
        (seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height)
      let current := context.rowWires tm seed labelOffset
      let predicateCost :=
        (oneHotTruePreimage (stmtPredicateTable tm test)).card + 1
      let htrueSupport :
          ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_left _ hsymbol
      let hfalseSupport :
          ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      (transitionStmtHeadPhase tm (workHeight tm seed.height) currentStart
          seed.start (seed.start + 1) current
          (.branch test whenTrue whenFalse) hsupport).toList ++
        transitionStmtScript tm (workHeight tm seed.height)
          seed.start (seed.start + 1) (currentStart + predicateCost)
          current whenTrue htrueSupport ++
        transitionStmtScript tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          (currentStart + predicateCost +
            compileStmtGateCost tm (workHeight tm seed.height) whenTrue)
          current whenFalse hfalseSupport := by
  let htrueSupport :
      ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
    intro k symbol hsymbol
    apply hsupport k
    simp only [stmtPushSet]
    exact Finset.mem_union_left _ hsymbol
  let hfalseSupport :
      ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
    intro k symbol hsymbol
    apply hsupport k
    simp only [stmtPushSet]
    exact Finset.mem_union_right _ hsymbol
  let predicateCost := transitionStmtBranchPredicateCost tm test
  let trueContext := context.advance predicateCost
  let falseContext := context.advance
    (predicateCost.add (compileStmtGateAffine tm whenTrue))
  change (match transitionStmtLinearContextPhaseForms tm labelOffset
      trueContext whenTrue htrueSupport,
    transitionStmtLinearResult tm trueContext whenTrue htrueSupport,
    transitionStmtLinearContextPhaseForms tm labelOffset falseContext
      whenFalse hfalseSupport,
    transitionStmtLinearResult tm falseContext whenFalse hfalseSupport with
  | some trueForms, some trueResult, some falseForms, some falseResult =>
      some ({ trueForms, falseForms, trueResult, falseResult } :
        TransitionStmtTerminalBranchPlan tm)
  | _, _, _, _ => none) = some plan at hplan
  cases htrueForms : transitionStmtLinearContextPhaseForms tm labelOffset
      trueContext whenTrue htrueSupport with
  | none => simp [htrueForms] at hplan
  | some trueForms =>
      cases htrueResult : transitionStmtLinearResult tm trueContext whenTrue
          htrueSupport with
      | none => simp [htrueForms, htrueResult] at hplan
      | some trueResult =>
          cases hfalseForms : transitionStmtLinearContextPhaseForms tm
              labelOffset falseContext whenFalse hfalseSupport with
          | none => simp [htrueForms, htrueResult, hfalseForms] at hplan
          | some falseForms =>
              cases hfalseResult : transitionStmtLinearResult tm falseContext
                  whenFalse hfalseSupport with
              | none =>
                  simp [htrueForms, htrueResult, hfalseForms, hfalseResult]
                    at hplan
              | some falseResult =>
                  simp [htrueForms, htrueResult, hfalseForms, hfalseResult]
                    at hplan
                  subst plan
                  have hhead :=
                    transitionStmtContextHeadPhaseForm_eval_of_padding tm seed
                      labelOffset context (.branch test whenTrue whenFalse)
                      hsupport hcurrent
                  have htrue := transitionStmtLinearContextPhaseForms_eval tm
                    seed labelOffset trueContext whenTrue htrueSupport
                    htruePadding trueForms htrueForms
                  have hfalse := transitionStmtLinearContextPhaseForms_eval tm
                    seed labelOffset falseContext whenFalse hfalseSupport
                    hfalsePadding falseForms hfalseForms
                  have htrueStart :
                      (seed.start + labelOffset.eval seed.height) +
                          trueContext.gateOffset.eval
                            (workHeight tm seed.height) =
                        ((seed.start + labelOffset.eval seed.height) +
                            context.gateOffset.eval
                              (workHeight tm seed.height)) +
                          ((oneHotTruePreimage
                            (stmtPredicateTable tm test)).card + 1) := by
                    simp [trueContext, predicateCost,
                      transitionStmtBranchPredicateCost,
                      TransitionStmtAffineContext.advance,
                      TransitionAffineNat.eval_add]
                    omega
                  have hfalseStart :
                      (seed.start + labelOffset.eval seed.height) +
                          falseContext.gateOffset.eval
                            (workHeight tm seed.height) =
                        ((seed.start + labelOffset.eval seed.height) +
                            context.gateOffset.eval
                              (workHeight tm seed.height)) +
                          ((oneHotTruePreimage
                            (stmtPredicateTable tm test)).card + 1) +
                          compileStmtGateCost tm
                            (workHeight tm seed.height) whenTrue := by
                    simp [falseContext, predicateCost,
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
                  simp only [TransitionStmtTerminalBranchPlan.fixedPhaseForms,
                    List.map_append]
                  rw [show
                    (transitionStmtContextHeadPhaseForm tm labelOffset context
                      (.branch test whenTrue whenFalse) hsupport).toList.map
                        (fun phase => phase.eval
                          (transitionTailAffineSeed seed)) =
                      (transitionStmtHeadPhase tm
                        (workHeight tm seed.height)
                        ((seed.start + labelOffset.eval seed.height) +
                          context.gateOffset.eval
                            (workHeight tm seed.height))
                        seed.start (seed.start + 1)
                        (context.rowWires tm seed labelOffset)
                        (.branch test whenTrue whenFalse) hsupport).toList by
                      simpa [optionToList_map] using congrArg Option.toList
                        hhead]
                  rw [htrue, hfalse]

end CLRS.Chapter34.Turing.CookLevin
