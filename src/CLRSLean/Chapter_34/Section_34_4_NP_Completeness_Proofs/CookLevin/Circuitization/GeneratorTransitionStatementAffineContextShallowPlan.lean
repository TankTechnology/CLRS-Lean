import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextPrefixTerminalBranchBudget

/-!
# Unified shallow statement plans

Branch-free statements and arbitrary linear prefixes ending in a branch with
branch-free arms now share one public compiler interface.  This is the first
statement-plan layer that can be consumed uniformly by transition-row
assembly.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A complete branch-free script or a complete one-branch-layer script. -/
inductive TransitionStmtShallowPlan (tm : _root_.Turing.FinTM2)
  | linear (forms : List TransitionAffineStmtPhaseForm)
  | branch (plan : TransitionStmtPrefixTerminalBranchPlan tm)

/-- Prefer the simpler branch-free compiler, then fall back to the verified
prefix-terminal-branch compiler. -/
noncomputable def transitionStmtShallowPlan
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    Option (TransitionStmtShallowPlan tm) :=
  match transitionStmtLinearContextPhaseForms tm labelOffset context q
      hsupport with
  | some forms => some (.linear forms)
  | none =>
      (transitionStmtPrefixTerminalBranchPlan tm labelOffset context q
        hsupport).map .branch

/-- The unified compiler recognizes exactly branch-free spines and spines
ending in one terminal-arm branch. -/
theorem transitionStmtShallowPlan_isSome_iff
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k) :
    (transitionStmtShallowPlan tm labelOffset context q hsupport).isSome ↔
      (transitionStmtTerminalLayout tm q).isSome ∨
        transitionStmtEndsInTerminalBranch tm q := by
  cases hlinear : transitionStmtLinearContextPhaseForms tm labelOffset
      context q hsupport with
  | none =>
      have hlinearIff :=
        transitionStmtLinearContextPhaseForms_isSome_iff_terminal tm
          labelOffset context q hsupport
      rw [hlinear] at hlinearIff
      have hnotTerminal : ¬ (transitionStmtTerminalLayout tm q).isSome := by
        simpa using hlinearIff
      simp [transitionStmtShallowPlan, hlinear, hnotTerminal,
        transitionStmtPrefixTerminalBranchPlan_isSome_iff]
  | some forms =>
      have hlinearIff :=
        transitionStmtLinearContextPhaseForms_isSome_iff_terminal tm
          labelOffset context q hsupport
      rw [hlinear] at hlinearIff
      have hterminal : (transitionStmtTerminalLayout tm q).isSome := by
        simpa using hlinearIff
      simp [transitionStmtShallowPlan, hlinear, hterminal]

/-- Evaluate either unified plan to its complete semantic phase list. -/
def TransitionStmtShallowPlan.completePhases
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    TransitionStmtShallowPlan tm → List AffineStmtPhase
  | .linear forms =>
      forms.map (fun phase => phase.eval (transitionTailAffineSeed seed))
  | .branch plan => plan.completePhases tm seed labelOffset

/-- At a verifier label, every successful unified plan is exactly the
established semantic statement script, with all padding discharged. -/
theorem transitionStmtShallowInitial_completePhases_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (plan : TransitionStmtShallowPlan W.machine.tm)
    (hplan : transitionStmtShallowPlan W.machine.tm labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label) =
        some plan) :
    plan.completePhases W.machine.tm seed labelOffset =
      transitionStmtScript W.machine.tm
        (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
        (seed.start + labelOffset.eval seed.height)
        (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
          seed.rowBase)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label) := by
  change (match transitionStmtLinearContextPhaseForms W.machine.tm
      labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    with
    | some forms => some (.linear forms)
    | none =>
        (transitionStmtPrefixTerminalBranchPlan W.machine.tm labelOffset
          (TransitionStmtAffineContext.initial W.machine.tm)
          (W.machine.tm.m label)
          (stmtPushSet_program_subset W.machine.tm label)).map .branch) =
      some plan at hplan
  cases hlinear : transitionStmtLinearContextPhaseForms W.machine.tm
      labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
      with
  | some forms =>
      rw [hlinear] at hplan
      simp only [Option.some.injEq] at hplan
      subst plan
      have hterminalIff :=
        transitionStmtLinearContextPhaseForms_isSome_iff_terminal W.machine.tm
          labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
          (W.machine.tm.m label)
          (stmtPushSet_program_subset W.machine.tm label)
      rw [hlinear] at hterminalIff
      have hterminal :
          (transitionStmtTerminalLayout W.machine.tm
            (W.machine.tm.m label)).isSome := by
        simpa using hterminalIff
      exact transitionStmtLinearInitialPhaseForms_eval W input seed hseed
        labelOffset label hterminal forms hlinear
  | none =>
      rw [hlinear] at hplan
      cases hbranch : transitionStmtPrefixTerminalBranchPlan W.machine.tm
          labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
          (W.machine.tm.m label)
          (stmtPushSet_program_subset W.machine.tm label) with
      | none => simp [hbranch] at hplan
      | some branchPlan =>
          rw [hbranch] at hplan
          simp only [Option.map_some, Option.some.injEq] at hplan
          subst plan
          have hendsIff :=
            transitionStmtPrefixTerminalBranchPlan_isSome_iff W.machine.tm
              labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
              (W.machine.tm.m label)
              (stmtPushSet_program_subset W.machine.tm label)
          rw [hbranch] at hendsIff
          have hends : transitionStmtEndsInTerminalBranch W.machine.tm
              (W.machine.tm.m label) := by
            simpa using hendsIff
          exact
            transitionStmtPrefixTerminalBranchInitial_completePhases_eq_script
              W input seed hseed labelOffset label hends branchPlan hbranch

end CLRS.Chapter34.Turing.CookLevin
