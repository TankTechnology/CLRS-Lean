import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranch

/-!
# Mux inputs of affine branches with terminal arms

The branch plan now exposes the exact selector, mux start, and both complete
arm rows.  These are precisely the four semantic views consumed by the
existing variable-width whole-row mux assembler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Support inherited by the true arm. -/
theorem transitionStmtBranchTrueSupport
    (tm : _root_.Turing.FinTM2) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    ∀ k, stmtPushSet tm whenTrue k ⊆ reachableAlphabet tm k := by
  intro k symbol hsymbol
  apply hsupport k
  simp only [stmtPushSet]
  exact Finset.mem_union_left _ hsymbol

/-- Support inherited by the false arm. -/
theorem transitionStmtBranchFalseSupport
    (tm : _root_.Turing.FinTM2) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k) :
    ∀ k, stmtPushSet tm whenFalse k ⊆ reachableAlphabet tm k := by
  intro k symbol hsymbol
  apply hsupport k
  simp only [stmtPushSet]
  exact Finset.mem_union_right _ hsymbol

/-- Context at the first true-arm gate. -/
def transitionStmtBranchTrueContext
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool) : TransitionStmtAffineContext tm :=
  context.advance (transitionStmtBranchPredicateCost tm test)

/-- Context at the first false-arm gate. -/
def transitionStmtBranchFalseContext
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool)
    (whenTrue : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    TransitionStmtAffineContext tm :=
  context.advance ((transitionStmtBranchPredicateCost tm test).add
    (compileStmtGateAffine tm whenTrue))

/-- Affine wire form of the predicate result used as mux selector. -/
def transitionStmtBranchSelectorForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool) :
    AffineUnaryTripleForm :=
  transitionAffineFormAddConst (context.startForm tm labelOffset)
    (oneHotTruePreimage (stmtPredicateTable tm test)).card

/-- Context at the first gate of the final whole-row mux. -/
def transitionStmtBranchMuxContext
    (tm : _root_.Turing.FinTM2) (context : TransitionStmtAffineContext tm)
    (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    TransitionStmtAffineContext tm :=
  context.advance
    ((transitionStmtBranchPredicateCost tm test).add
      ((compileStmtGateAffine tm whenTrue).add
        (compileStmtGateAffine tm whenFalse)))

/-- Affine form of the final mux start. -/
def transitionStmtBranchMuxStartForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    AffineUnaryTripleForm :=
  (transitionStmtBranchMuxContext tm context test whenTrue whenFalse).startForm
    tm labelOffset

private theorem disjunctionGateTrace_wire_eq_start_add_length
    (start : Nat) : ∀ wires : List CircuitBuilder.Wire,
    (CircuitBuilder.disjunctionGateTrace start wires).wire =
      start + wires.length := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [CircuitBuilder.disjunctionGateTrace,
        CircuitBuilder.disjunctionGateTrace_length]

/-- The selector form is the literal predicate output wire. -/
theorem transitionStmtBranchSelectorForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool) :
    affineUnaryTripleFormValue
        (transitionStmtBranchSelectorForm tm labelOffset context test)
        (transitionTailAffineSeed seed) =
      (CircuitBuilder.disjunctionGateTrace
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        (oneHotPredicateWires
          (context.rowWires tm seed labelOffset).state
          (stmtPredicateTable tm test))).wire := by
  rw [transitionStmtBranchSelectorForm,
    transitionAffineFormAddConst_value, context.startForm_value,
    disjunctionGateTrace_wire_eq_start_add_length]
  simp

/-- The mux-start form evaluates to the exact semantic start after the
predicate and both arm scripts. -/
theorem transitionStmtBranchMuxStartForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ) :
    affineUnaryTripleFormValue
        (transitionStmtBranchMuxStartForm tm labelOffset context test
          whenTrue whenFalse)
        (transitionTailAffineSeed seed) =
      ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height)) +
        ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1) +
        compileStmtGateCost tm (workHeight tm seed.height) whenTrue +
        compileStmtGateCost tm (workHeight tm seed.height) whenFalse := by
  rw [transitionStmtBranchMuxStartForm,
    TransitionStmtAffineContext.startForm_value]
  simp [transitionStmtBranchMuxContext,
    transitionStmtBranchPredicateCost,
    TransitionStmtAffineContext.advance, TransitionAffineNat.eval_add,
    compileStmtGateAffine_eval tm whenTrue (workHeight tm seed.height) hwork,
    compileStmtGateAffine_eval tm whenFalse (workHeight tm seed.height) hwork]
  omega

/-- A successful plan retains the exact normalized terminal result of each
arm at its proper affine context. -/
theorem transitionStmtTerminalBranchPlan_results
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan) :
    transitionStmtLinearResult tm
        (transitionStmtBranchTrueContext tm context test) whenTrue
        (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
          hsupport) = some plan.trueResult ∧
      transitionStmtLinearResult tm
        (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
        (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
          hsupport) = some plan.falseResult := by
  let htrueSupport := transitionStmtBranchTrueSupport tm test whenTrue
    whenFalse hsupport
  let hfalseSupport := transitionStmtBranchFalseSupport tm test whenTrue
    whenFalse hsupport
  let trueContext := transitionStmtBranchTrueContext tm context test
  let falseContext := transitionStmtBranchFalseContext tm context test whenTrue
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
                  exact ⟨rfl, rfl⟩

/-- Complete routed true-arm input. -/
def TransitionStmtTerminalBranchPlan.trueRouteValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtTerminalBranchPlan tm) : List Nat :=
  plan.trueResult.completeRouteValues tm seed labelOffset

/-- Complete routed false-arm input. -/
def TransitionStmtTerminalBranchPlan.falseRouteValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtTerminalBranchPlan tm) : List Nat :=
  plan.falseResult.completeRouteValues tm seed labelOffset

/-- The routed true input is exactly the semantic true-arm output row. -/
theorem transitionStmtTerminalBranchPlan_trueRouteValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (hcapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    plan.trueRouteValues tm seed labelOffset =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          (((seed.start + labelOffset.eval seed.height) +
              context.gateOffset.eval (workHeight tm seed.height)) +
            ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1))
          (context.rowWires tm seed labelOffset) whenTrue
          (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
            hsupport)) := by
  have hresults := transitionStmtTerminalBranchPlan_results tm labelOffset
    context test whenTrue whenFalse hsupport plan hplan
  have hroute := transitionStmtLinearResult_completeRouteValues_eq_output tm
    seed hwork labelOffset
    (transitionStmtBranchTrueContext tm context test) whenTrue
    (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport)
    plan.trueResult hresults.1 hcapacity
  simp only [transitionStmtBranchTrueContext,
    TransitionStmtAffineContext.rowWires,
    TransitionStmtAffineContext.advance_wires] at hroute
  unfold TransitionStmtTerminalBranchPlan.trueRouteValues
  simpa [transitionStmtBranchTrueContext,
    transitionStmtBranchPredicateCost,
    TransitionStmtAffineContext.advance, TransitionAffineNat.eval_add,
    TransitionStmtAffineContext.rowWires, Nat.add_assoc] using hroute

/-- The routed false input is exactly the semantic false-arm output row. -/
theorem transitionStmtTerminalBranchPlan_falseRouteValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm)
    (hplan : transitionStmtTerminalBranchPlan tm labelOffset context test
      whenTrue whenFalse hsupport = some plan)
    (hcapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.falseResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    plan.falseRouteValues tm seed labelOffset =
      transitionCfgWireValues tm (workHeight tm seed.height)
        (transitionStmtOutputWires tm (workHeight tm seed.height)
          seed.start (seed.start + 1)
          ((((seed.start + labelOffset.eval seed.height) +
              context.gateOffset.eval (workHeight tm seed.height)) +
            ((oneHotTruePreimage (stmtPredicateTable tm test)).card + 1)) +
            compileStmtGateCost tm (workHeight tm seed.height) whenTrue)
          (context.rowWires tm seed labelOffset) whenFalse
          (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
            hsupport)) := by
  have hresults := transitionStmtTerminalBranchPlan_results tm labelOffset
    context test whenTrue whenFalse hsupport plan hplan
  have hroute := transitionStmtLinearResult_completeRouteValues_eq_output tm
    seed hwork labelOffset
    (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
    (transitionStmtBranchFalseSupport tm test whenTrue whenFalse hsupport)
    plan.falseResult hresults.2 hcapacity
  simp only [transitionStmtBranchFalseContext,
    TransitionStmtAffineContext.rowWires,
    TransitionStmtAffineContext.advance_wires] at hroute
  unfold TransitionStmtTerminalBranchPlan.falseRouteValues
  simpa [transitionStmtBranchFalseContext,
    transitionStmtBranchPredicateCost,
    TransitionStmtAffineContext.advance, TransitionAffineNat.eval_add,
    TransitionStmtAffineContext.rowWires,
    compileStmtGateAffine_eval tm whenTrue (workHeight tm seed.height) hwork,
    Nat.add_assoc] using hroute

end CLRS.Chapter34.Turing.CookLevin
