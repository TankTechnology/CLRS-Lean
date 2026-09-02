import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextShallowPlan

/-!
# Controller-source decomposition of prefix terminal branches

The fixed affine phase compiler and the variable-width mux progression
controller have different source formats.  This module gives their exact
concatenation boundary and proves that the joined output is the official
statement-controller encoding of the complete generated branch script.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Final mux segments carried by a prefix-terminal-branch plan. -/
def TransitionStmtPrefixTerminalBranchPlan.muxInvocationSegments
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    List AffineMuxInvocationProgression :=
  plan.branchPlan.muxInvocationSegments tm seed labelOffset
    plan.branchContext plan.test plan.whenTrue plan.whenFalse

/-- Controller output for the fixed predicate/arm phase prefix. -/
def TransitionStmtPrefixTerminalBranchPlan.fixedControllerFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    List UnaryFrameSym :=
  encodeAffineStmtControllerScript
    ((plan.fixedPhaseForms tm labelOffset).map fun phase =>
      phase.eval (transitionTailAffineSeed seed))

/-- Tagged final mux phase emitted by the generic progression controller. -/
def TransitionStmtPrefixTerminalBranchPlan.muxControllerFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    List UnaryFrameSym :=
  let view := plan.branchPlan.muxInvocationView tm seed labelOffset
    plan.branchContext plan.test plan.whenTrue plan.whenFalse
  affineStmtPhaseTagCode (.mux view.selector view.frames) ++
    affineMuxInvocationProgressionFamilyFrames
      (plan.muxInvocationSegments tm seed labelOffset)

/-- Complete two-controller output stream for one shallow branch plan. -/
def TransitionStmtPrefixTerminalBranchPlan.controllerFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    List UnaryFrameSym :=
  plan.fixedControllerFrames tm seed labelOffset ++
    plan.muxControllerFrames tm seed labelOffset

private theorem completePhases_eq_fixed_append_mux
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    plan.completePhases tm seed labelOffset =
      (plan.fixedPhaseForms tm labelOffset).map
          (fun phase => phase.eval (transitionTailAffineSeed seed)) ++
        [.mux
          (plan.branchPlan.muxInvocationView tm seed labelOffset
            plan.branchContext plan.test plan.whenTrue
            plan.whenFalse).selector
          (plan.branchPlan.muxInvocationView tm seed labelOffset
            plan.branchContext plan.test plan.whenTrue
            plan.whenFalse).frames] := by
  unfold TransitionStmtPrefixTerminalBranchPlan.completePhases
    TransitionStmtPrefixTerminalBranchPlan.fixedPhaseForms
    TransitionStmtTerminalBranchPlan.completePhases
  simp [List.map_append, List.append_assoc]

/-- Joining the two verified controller outputs gives exactly the official
encoding of the complete semantic phase list.  This theorem is structural:
it needs no padding or semantic hypotheses. -/
theorem TransitionStmtPrefixTerminalBranchPlan.controllerFrames_eq_complete
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (plan : TransitionStmtPrefixTerminalBranchPlan tm) :
    plan.controllerFrames tm seed labelOffset =
      encodeAffineStmtControllerScript
        (plan.completePhases tm seed labelOffset) := by
  rw [completePhases_eq_fixed_append_mux]
  unfold TransitionStmtPrefixTerminalBranchPlan.controllerFrames
    TransitionStmtPrefixTerminalBranchPlan.fixedControllerFrames
    TransitionStmtPrefixTerminalBranchPlan.muxControllerFrames
    TransitionStmtPrefixTerminalBranchPlan.muxInvocationSegments
    encodeAffineStmtControllerScript
  simp only [List.flatMap_append, List.flatMap_singleton]
  rw [transitionStmtTerminalBranchPlan_muxInvocationSegments_frames_structural]
  rfl

end CLRS.Chapter34.Turing.CookLevin
