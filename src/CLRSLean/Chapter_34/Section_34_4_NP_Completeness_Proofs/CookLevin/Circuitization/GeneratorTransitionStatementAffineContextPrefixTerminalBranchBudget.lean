import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextPrefixTerminalBranchComplete

/-!
# Static padding for prefixes ending in a terminal branch

The verifier's machine-wide per-step action budget now discharges every
capacity premise of the complete prefix/branch theorem.  The final theorem is
stated directly at an initial program-label context.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A single bound on the recorded prefix plus the remaining statement tree
supplies all prefix and arm padding obligations. -/
theorem transitionStmtPrefixTerminalBranchPadding_of_budget
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (budget : Nat) (hheight : 2 * budget + 1 ≤ seed.height) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      transitionStmtEndsInTerminalBranch tm q →
      (∀ k,
        (transitionStmtStackActionsFor tm k
          context.stackActions).length +
            stmtMaxStackActions tm k q ≤ budget) →
      transitionStmtPrefixTerminalBranchPadding tm seed context q
        hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hends
      exact False.elim hends
  | goto jump =>
      intro hsupport hends
      exact False.elim hends
  | load update continuation ih =>
      intro hsupport hends hbudget
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      constructor
      · intro k
        have hk := hbudget k
        simp [stmtMaxStackActions] at hk
        omega
      · apply ih (context.afterLoad tm update) hcontinuation hends
        intro k
        simpa [TransitionStmtAffineContext.afterLoad,
          TransitionStmtAffineContext.advance,
          TransitionStmtAffineContext.replaceStateByMap,
          stmtMaxStackActions] using hbudget k
  | push selected emit continuation ih =>
      intro hsupport hends hbudget
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        intro j symbol hsymbol
        apply hsupport j
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm selected :=
        fun code =>
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport selected
            simp [stmtPushSet]⟩
      let table := fun code => encodeSupportedSymbol (symbolAt code)
      constructor
      · intro k
        have hk := hbudget k
        have hzero : 0 ≤ stmtMaxStackActions tm k
            (.push selected emit continuation) := Nat.zero_le _
        omega
      · apply ih (context.afterPush tm selected table) hcontinuation hends
        intro target
        have hk := hbudget target
        rw [show (context.afterPush tm selected table).stackActions =
            context.stackActions ++
              [{ k := selected
                 kind := .push fun symbol =>
                   context.gateOffset.add
                     (TransitionAffineNat.const
                       (oneHotMapWireOffset table symbol)) }] by rfl]
        rw [transitionStmtStackActionsFor_append_singleton_length]
        change ((transitionStmtStackActionsFor tm target
            context.stackActions).length +
              (if selected = target then 1 else 0)) +
                stmtMaxStackActions tm target continuation ≤ budget
        change (transitionStmtStackActionsFor tm target
            context.stackActions).length +
              ((if selected = target then 1 else 0) +
                stmtMaxStackActions tm target continuation) ≤ budget at hk
        omega
  | peek selected update continuation ih =>
      intro hsupport hends hbudget
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      constructor
      · intro k
        have hk := hbudget k
        simp [stmtMaxStackActions] at hk
        omega
      · apply ih (context.afterPeek tm selected update) hcontinuation hends
        intro k
        simpa [TransitionStmtAffineContext.afterPeek,
          TransitionStmtAffineContext.advance,
          TransitionStmtAffineContext.replaceStateByPairMap,
          stmtMaxStackActions] using hbudget k
  | pop selected update continuation ih =>
      intro hsupport hends hbudget
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      constructor
      · intro k
        have hk := hbudget k
        have hzero : 0 ≤ stmtMaxStackActions tm k
            (.pop selected update continuation) := Nat.zero_le _
        omega
      · apply ih (context.afterPop tm selected update) hcontinuation hends
        intro target
        have hk := hbudget target
        rw [show (context.afterPop tm selected update).stackActions =
            context.stackActions ++
              [{ k := selected, kind := .pop context.gateOffset }] by rfl]
        rw [transitionStmtStackActionsFor_append_singleton_length]
        change ((transitionStmtStackActionsFor tm target
            context.stackActions).length +
              (if selected = target then 1 else 0)) +
                stmtMaxStackActions tm target continuation ≤ budget
        change (transitionStmtStackActionsFor tm target
            context.stackActions).length +
              ((if selected = target then 1 else 0) +
                stmtMaxStackActions tm target continuation) ≤ budget at hk
        omega
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport hends hbudget
      rcases hends with ⟨htrueTerminal, hfalseTerminal⟩
      constructor
      · intro k
        have hk := hbudget k
        simp only [stmtMaxStackActions] at hk
        omega
      · constructor
        · apply transitionStmtLinearContextPadding_of_budget tm seed budget
            hheight
            (transitionStmtBranchTrueContext tm context test) whenTrue
            (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
              hsupport) htrueTerminal
          intro k
          have hk := hbudget k
          simp only [stmtMaxStackActions] at hk
          simpa [transitionStmtBranchTrueContext,
            TransitionStmtAffineContext.advance] using
            (show (transitionStmtStackActionsFor tm k
                context.stackActions).length +
                  stmtMaxStackActions tm k whenTrue ≤ budget by omega)
        · apply transitionStmtLinearContextPadding_of_budget tm seed budget
            hheight
            (transitionStmtBranchFalseContext tm context test whenTrue)
            whenFalse
            (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
              hsupport) hfalseTerminal
          intro k
          have hk := hbudget k
          simp only [stmtMaxStackActions] at hk
          simpa [transitionStmtBranchFalseContext,
            TransitionStmtAffineContext.advance] using
            (show (transitionStmtStackActionsFor tm k
                context.stackActions).length +
                  stmtMaxStackActions tm k whenFalse ≤ budget by omega)

/-- Initial machine context inherits the uniform per-step action budget. -/
theorem transitionStmtPrefixTerminalBranchPadding_initial
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (label : tm.Λ)
    (hheight : 2 * maxStackActionsPerStep tm + 1 ≤ seed.height)
    (hends : transitionStmtEndsInTerminalBranch tm (tm.m label)) :
    transitionStmtPrefixTerminalBranchPadding tm seed
      (TransitionStmtAffineContext.initial tm) (tm.m label)
      (stmtPushSet_program_subset tm label) := by
  apply transitionStmtPrefixTerminalBranchPadding_of_budget tm seed
    (maxStackActionsPerStep tm) hheight
      (TransitionStmtAffineContext.initial tm) (tm.m label)
      (stmtPushSet_program_subset tm label) hends
  intro k
  simpa [TransitionStmtAffineContext.initial,
    transitionStmtStackActionsFor] using
    stmtMaxStackActions_le_maxStackActionsPerStep tm label k

/-- Every verifier transition seed supplies the complete shallow-branch
padding invariant. -/
theorem transitionStmtPrefixTerminalBranchPadding_initial_verifier
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (label : W.machine.tm.Λ)
    (hends : transitionStmtEndsInTerminalBranch W.machine.tm
      (W.machine.tm.m label)) :
    transitionStmtPrefixTerminalBranchPadding W.machine.tm seed
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) := by
  apply transitionStmtPrefixTerminalBranchPadding_initial W.machine.tm seed
    label
  · rw [hseed]
    exact verifierHeight_actionPadding_le W input.length
  · exact hends

/-- At a verifier label, no local capacity assumptions remain: the generated
complete plan equals the semantic statement script directly. -/
theorem transitionStmtPrefixTerminalBranchInitial_completePhases_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (hends : transitionStmtEndsInTerminalBranch W.machine.tm
      (W.machine.tm.m label))
    (plan : TransitionStmtPrefixTerminalBranchPlan W.machine.tm)
    (hplan : transitionStmtPrefixTerminalBranchPlan W.machine.tm labelOffset
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
  have hpadding := transitionStmtPrefixTerminalBranchPadding_initial_verifier
    W input seed hseed label hends
  have hheight := verifierHeight_actionPadding_le W input.length
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    rw [hseed]
    unfold workHeight
    omega
  have heval :=
    transitionStmtPrefixTerminalBranchPlan_completePhases_eq_script
      W.machine.tm seed hwork labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
      hpadding plan hplan
  rw [TransitionStmtAffineContext.initial_rowWires] at heval
  simpa [TransitionStmtAffineContext.initial] using heval

end CLRS.Chapter34.Turing.CookLevin
