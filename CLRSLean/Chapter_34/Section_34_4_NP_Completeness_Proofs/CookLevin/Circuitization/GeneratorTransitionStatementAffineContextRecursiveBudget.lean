import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextRecursiveSemantics

/-!
# Uniform verifier budget for arbitrary nested statements

The machine-wide maximum stack-action count bounds every root-to-leaf path,
including both sides of recursively nested branches.  This module discharges
the recursive padding invariant from that one static budget and exposes the
unconditional verifier-label statement-generation theorem.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- A single root-to-leaf action budget supplies recursive padding at every
statement node. -/
theorem transitionStmtRecursiveContextPadding_of_budget
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (budget : Nat) (hheight : 2 * budget + 1 ≤ seed.height) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      (∀ k,
        (transitionStmtStackActionsFor tm k
          context.stackActions).length +
            stmtMaxStackActions tm k q ≤ budget) →
      transitionStmtRecursiveContextPadding tm seed context q hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hbudget k
      have hk := hbudget k
      simp [stmtMaxStackActions] at hk
      omega
  | goto jump =>
      intro hsupport hbudget k
      have hk := hbudget k
      simp [stmtMaxStackActions] at hk
      omega
  | load update continuation ih =>
      intro hsupport hbudget
      let hcontinuation : ∀ k,
          stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      constructor
      · intro k
        have hk := hbudget k
        simp [stmtMaxStackActions] at hk
        omega
      · apply ih (context.afterLoad tm update) hcontinuation
        intro k
        simpa [TransitionStmtAffineContext.afterLoad,
          TransitionStmtAffineContext.advance,
          TransitionStmtAffineContext.replaceStateByMap,
          stmtMaxStackActions] using hbudget k
  | push selected emit continuation ih =>
      intro hsupport hbudget
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
      · apply ih (context.afterPush tm selected table) hcontinuation
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
      intro hsupport hbudget
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      constructor
      · intro k
        have hk := hbudget k
        simp [stmtMaxStackActions] at hk
        omega
      · apply ih (context.afterPeek tm selected update) hcontinuation
        intro k
        simpa [TransitionStmtAffineContext.afterPeek,
          TransitionStmtAffineContext.advance,
          TransitionStmtAffineContext.replaceStateByPairMap,
          stmtMaxStackActions] using hbudget k
  | pop selected update continuation ih =>
      intro hsupport hbudget
      let hcontinuation : ∀ j,
          stmtPushSet tm continuation j ⊆ reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      constructor
      · intro k
        have hk := hbudget k
        have hzero : 0 ≤ stmtMaxStackActions tm k
            (.pop selected update continuation) := Nat.zero_le _
        omega
      · apply ih (context.afterPop tm selected update) hcontinuation
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
      intro hsupport hbudget
      constructor
      · intro k
        have hk := hbudget k
        simp only [stmtMaxStackActions] at hk
        omega
      · constructor
        · apply ihTrue (transitionStmtBranchTrueContext tm context test)
            (transitionStmtBranchTrueSupport tm test whenTrue whenFalse
              hsupport)
          intro k
          have hk := hbudget k
          simp only [stmtMaxStackActions] at hk
          simpa [transitionStmtBranchTrueContext,
            TransitionStmtAffineContext.advance] using
            (show (transitionStmtStackActionsFor tm k
                context.stackActions).length +
                  stmtMaxStackActions tm k whenTrue ≤ budget by omega)
        · apply ihFalse
            (transitionStmtBranchFalseContext tm context test whenTrue)
            (transitionStmtBranchFalseSupport tm test whenTrue whenFalse
              hsupport)
          intro k
          have hk := hbudget k
          simp only [stmtMaxStackActions] at hk
          simpa [transitionStmtBranchFalseContext,
            TransitionStmtAffineContext.advance] using
            (show (transitionStmtStackActionsFor tm k
                context.stackActions).length +
                  stmtMaxStackActions tm k whenFalse ≤ budget by omega)

/-- Initial program-label contexts inherit the machine-wide action budget. -/
theorem transitionStmtRecursiveContextPadding_initial
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (label : tm.Λ)
    (hheight : 2 * maxStackActionsPerStep tm + 1 ≤ seed.height) :
    transitionStmtRecursiveContextPadding tm seed
      (TransitionStmtAffineContext.initial tm) (tm.m label)
      (stmtPushSet_program_subset tm label) := by
  apply transitionStmtRecursiveContextPadding_of_budget tm seed
    (maxStackActionsPerStep tm) hheight
      (TransitionStmtAffineContext.initial tm) (tm.m label)
      (stmtPushSet_program_subset tm label)
  intro k
  simpa [TransitionStmtAffineContext.initial,
    transitionStmtStackActionsFor] using
    stmtMaxStackActions_le_maxStackActionsPerStep tm label k

/-- Every verifier transition seed supplies recursive padding for every
program label, without a branch-depth restriction. -/
theorem transitionStmtRecursiveContextPadding_initial_verifier
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (label : W.machine.tm.Λ) :
    transitionStmtRecursiveContextPadding W.machine.tm seed
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) := by
  apply transitionStmtRecursiveContextPadding_initial W.machine.tm seed label
  rw [hseed]
  exact verifierHeight_actionPadding_le W input.length

/-- Unconditional verifier-label closure: recursive affine phases equal the
full semantic statement script for every fixed program statement. -/
theorem transitionStmtRecursiveInitial_phases_eq_script
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ) :
    transitionStmtRecursivePhases W.machine.tm seed labelOffset
        (TransitionStmtAffineContext.initial W.machine.tm)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label) =
      transitionStmtScript W.machine.tm
        (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
        (seed.start + labelOffset.eval seed.height)
        (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
          seed.rowBase)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label) := by
  have hpadding := transitionStmtRecursiveContextPadding_initial_verifier
    W input seed hseed label
  have hheight := verifierHeight_actionPadding_le W input.length
  have hwork : 0 < workHeight W.machine.tm seed.height := by
    rw [hseed]
    unfold workHeight
    omega
  have heval := transitionStmtRecursivePhases_eq_script W.machine.tm seed
    hwork labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    hpadding
  rw [TransitionStmtAffineContext.initial_rowWires] at heval
  simpa [TransitionStmtAffineContext.initial] using heval

end CLRS.Chapter34.Turing.CookLevin
