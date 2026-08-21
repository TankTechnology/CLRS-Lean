import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalCapacity

/-!
# Complete semantic script of a terminal-arm branch

The fixed predicate/arm phases and the variable-width mux invocation are
joined here for the first time.  The resulting list is proved equal to the
original recursive statement compiler, phase for phase.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Evaluated fixed phases followed by the reconstructed whole-row mux. -/
def TransitionStmtTerminalBranchPlan.completePhases
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k,
      stmtPushSet tm (.branch test whenTrue whenFalse) k ⊆
        reachableAlphabet tm k)
    (plan : TransitionStmtTerminalBranchPlan tm) : List AffineStmtPhase :=
  (plan.fixedPhaseForms tm labelOffset context test whenTrue whenFalse
      hsupport).map
      (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
    [.mux
      (plan.muxInvocationView tm seed labelOffset context test whenTrue
        whenFalse).selector
      (plan.muxInvocationView tm seed labelOffset context test whenTrue
        whenFalse).frames]

/-- A complete generated terminal-arm branch is literally the established
semantic `transitionStmtScript`. -/
theorem transitionStmtTerminalBranchPlan_completePhases_eq_script
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
    (hcurrent : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height)
    (htruePadding : transitionStmtLinearContextPadding tm seed
      (transitionStmtBranchTrueContext tm context test) whenTrue
      (transitionStmtBranchTrueSupport tm test whenTrue whenFalse hsupport))
    (hfalsePadding : transitionStmtLinearContextPadding tm seed
      (transitionStmtBranchFalseContext tm context test whenTrue) whenFalse
      (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
        hsupport)) :
    plan.completePhases tm seed labelOffset context test whenTrue whenFalse
        hsupport =
      transitionStmtScript tm (workHeight tm seed.height) seed.start
        (seed.start + 1)
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        (context.rowWires tm seed labelOffset)
        (.branch test whenTrue whenFalse) hsupport := by
  have hfixed :=
    transitionStmtTerminalBranchPlan_fixedPhaseForms_eval tm seed hwork
      labelOffset context test whenTrue whenFalse hsupport plan hplan hcurrent
      htruePadding hfalsePadding
  have hcapacities :=
    transitionStmtTerminalBranchPlan_capacities_of_padding tm seed labelOffset
      context test whenTrue whenFalse hsupport plan hplan htruePadding
      hfalsePadding
  have hframes :=
    transitionStmtTerminalBranchPlan_muxInvocationView_frames tm seed hwork
      labelOffset context test whenTrue whenFalse hsupport plan hplan
      hcapacities.1 hcapacities.2
  have hselector := transitionStmtBranchSelectorForm_value tm seed
    labelOffset context test
  have hviewSelector :
      (plan.muxInvocationView tm seed labelOffset context test whenTrue
        whenFalse).selector =
        transitionStmtBranchSemanticSelector tm seed labelOffset context
          test := by
    simpa [TransitionStmtTerminalBranchPlan.muxInvocationView,
      transitionStmtBranchSemanticSelector] using hselector
  unfold TransitionStmtTerminalBranchPlan.completePhases
  rw [hfixed, hviewSelector, hframes]
  simp only [transitionStmtScript]
  unfold transitionStmtBranchSemanticSelector
    transitionStmtBranchSemanticMuxStart
    transitionStmtBranchSemanticTrueWires
    transitionStmtBranchSemanticFalseWires
  rfl

end CLRS.Chapter34.Turing.CookLevin
