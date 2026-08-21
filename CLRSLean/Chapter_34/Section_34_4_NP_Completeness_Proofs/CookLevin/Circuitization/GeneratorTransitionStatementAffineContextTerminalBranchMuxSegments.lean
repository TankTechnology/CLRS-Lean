import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextTerminalBranchMuxFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxInvocationSegments

/-!
# Controller segments for terminal branch muxes

This file lowers the canonical branch invocation view to the already verified
generic mux-progression controller.  Singleton segments are sufficient for
correctness; later compression may merge adjacent coordinates without
changing this semantic boundary.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Generic-controller segments for one terminal branch mux. -/
def TransitionStmtTerminalBranchPlan.muxInvocationSegments
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (test : tm.σ → Bool)
    (whenTrue whenFalse : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (plan : TransitionStmtTerminalBranchPlan tm) :
    List AffineMuxInvocationProgression :=
  affineMuxInvocationSingletonSegments
    (plan.muxInvocationView tm seed labelOffset context test whenTrue
      whenFalse).selector
    (plan.muxInvocationView tm seed labelOffset context test whenTrue
      whenFalse).frames

/-- The generic controller expands the segment source exactly to the mux
invocation view, including the shared header and every coordinate delimiter. -/
theorem transitionStmtTerminalBranchPlan_muxInvocationSegments_frames
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
    (htrueCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height)
    (hfalseCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.falseResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    affineMuxInvocationProgressionFamilyFrames
        (plan.muxInvocationSegments tm seed labelOffset context test whenTrue
          whenFalse) =
      (plan.muxInvocationView tm seed labelOffset context test whenTrue
        whenFalse).encode := by
  have hframes :=
    transitionStmtTerminalBranchPlan_muxInvocationView_frames tm seed hwork
      labelOffset context test whenTrue whenFalse hsupport plan hplan
      htrueCapacity hfalseCapacity
  have hselector := transitionStmtBranchSelectorForm_value tm seed
    labelOffset context test
  have hviewSelector :
      (plan.muxInvocationView tm seed labelOffset context test whenTrue
        whenFalse).selector =
        transitionStmtBranchSemanticSelector tm seed labelOffset context
          test := by
    simpa [TransitionStmtTerminalBranchPlan.muxInvocationView,
      transitionStmtBranchSemanticSelector] using hselector
  unfold TransitionStmtTerminalBranchPlan.muxInvocationSegments
    TransitionDispatchMuxInvocationView.encode
  rw [hviewSelector, hframes]
  apply affineMuxInvocationSingletonSegments_frames
  · exact affineMuxFinCanonicalFrames_selector _ _ _ _ _
  · exact affineMuxFinCanonicalFrames_falseArm _ _ _ _ _

/-- Consequently the controller-expanded stream is the literal canonical
whole-row mux payload of `transitionStmtScript`. -/
theorem transitionStmtTerminalBranchPlan_muxInvocationSegments_encode
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
    (htrueCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.trueResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height)
    (hfalseCapacity : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        plan.falseResult.context.stackActions).length + 1 ≤
        workHeight tm seed.height) :
    affineMuxInvocationProgressionFamilyFrames
        (plan.muxInvocationSegments tm seed labelOffset context test whenTrue
          whenFalse) =
      encodeAffineMuxFinFrames
        (transitionStmtBranchSemanticSelector tm seed labelOffset context test)
        (affineMuxFinCanonicalFrames
          (transitionStmtBranchSemanticMuxStart tm seed labelOffset context
            test whenTrue whenFalse)
          (transitionStmtBranchSemanticSelector tm seed labelOffset context
            test)
          (cfgBitCount tm (workHeight tm seed.height))
          (fun coordinate =>
            transitionStmtBranchSemanticTrueWires tm seed labelOffset context
              test whenTrue whenFalse hsupport
              ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
                coordinate))
          (fun coordinate =>
            transitionStmtBranchSemanticFalseWires tm seed labelOffset context
              test whenTrue whenFalse hsupport
              ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm
                coordinate))) := by
  rw [transitionStmtTerminalBranchPlan_muxInvocationSegments_frames tm seed
    hwork labelOffset context test whenTrue whenFalse hsupport plan hplan
    htrueCapacity hfalseCapacity]
  exact transitionStmtTerminalBranchPlan_muxInvocationView_encode tm seed
    hwork labelOffset context test whenTrue whenFalse hsupport plan hplan
    htrueCapacity hfalseCapacity

end CLRS.Chapter34.Turing.CookLevin
