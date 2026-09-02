import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContextLinearSemantics

/-!
# Static padding for recursive affine statement contexts

The semantic recursion previously exposed a padding predicate at every
continuation.  This file discharges all of those obligations from one static
action budget.  The verifier height already reserves twice the uniform
per-step action count plus one public coordinate.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

/-- Appending one heterogeneous action changes a selected route length by one
exactly when that action targets the selected stack. -/
theorem transitionStmtStackActionsFor_append_singleton_length
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (actions : List (TransitionStmtStackAction tm))
    (action : TransitionStmtStackAction tm) :
    (transitionStmtStackActionsFor tm target
      (actions ++ [action])).length =
      (transitionStmtStackActionsFor tm target actions).length +
        (if action.k = target then 1 else 0) := by
  unfold transitionStmtStackActionsFor
  rw [List.filterMap_append, List.length_append]
  rcases action with ⟨selected, kind⟩
  by_cases hselected : selected = target
  · subst selected
    simp [TransitionStmtStackAction.selectFor]
  · simp [TransitionStmtStackAction.selectFor, hselected]

/-- One budget bounding the already-recorded prefix plus the remaining
statement actions discharges the complete recursive padding predicate. -/
theorem transitionStmtLinearContextPadding_of_budget
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (budget : Nat) (hheight : 2 * budget + 1 ≤ seed.height) :
    ∀ (context : TransitionStmtAffineContext tm)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k),
      (transitionStmtTerminalLayout tm q).isSome →
      (∀ k,
        (transitionStmtStackActionsFor tm k
          context.stackActions).length +
            stmtMaxStackActions tm k q ≤ budget) →
      transitionStmtLinearContextPadding tm seed context q hsupport := by
  intro context q
  induction q generalizing context with
  | halt =>
      intro hsupport hterminal hbudget
      intro k
      have hk := hbudget k
      simp [stmtMaxStackActions] at hk
      omega
  | goto jump =>
      intro hsupport hterminal hbudget
      intro k
      have hk := hbudget k
      simp [stmtMaxStackActions] at hk
      omega
  | load update continuation ih =>
      intro hsupport hterminal hbudget
      let hcontinuation : ∀ k, stmtPushSet tm continuation k ⊆
          reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      have hterminalContinuation :
          (transitionStmtTerminalLayout tm continuation).isSome := by
        simpa [transitionStmtTerminalLayout] using hterminal
      constructor
      · intro k
        have hk := hbudget k
        simp [stmtMaxStackActions] at hk
        omega
      · apply ih (context.afterLoad tm update) hcontinuation
          hterminalContinuation
        intro k
        simpa [TransitionStmtAffineContext.afterLoad,
          TransitionStmtAffineContext.advance,
          TransitionStmtAffineContext.replaceStateByMap,
          stmtMaxStackActions] using hbudget k
  | push selected emit continuation ih =>
      intro hsupport hterminal hbudget
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
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
      have hterminalContinuation :
          (transitionStmtTerminalLayout tm continuation).isSome := by
        simpa [transitionStmtTerminalLayout] using hterminal
      constructor
      · intro k
        have hk := hbudget k
        have hzero : 0 ≤ stmtMaxStackActions tm k
            (.push selected emit continuation) := Nat.zero_le _
        omega
      · apply ih (context.afterPush tm selected table) hcontinuation
          hterminalContinuation
        intro target
        have hk := hbudget target
        rw [show (context.afterPush tm selected table).stackActions =
            context.stackActions ++
              [{ k := selected
                 kind := .push fun symbol =>
                   context.gateOffset.add
                     (TransitionAffineNat.const
                       (oneHotMapWireOffset table symbol)) }] by
          rfl]
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
      intro hsupport hterminal hbudget
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      have hterminalContinuation :
          (transitionStmtTerminalLayout tm continuation).isSome := by
        simpa [transitionStmtTerminalLayout] using hterminal
      constructor
      · intro k
        have hk := hbudget k
        simp [stmtMaxStackActions] at hk
        omega
      · apply ih (context.afterPeek tm selected update) hcontinuation
          hterminalContinuation
        intro k
        simpa [TransitionStmtAffineContext.afterPeek,
          TransitionStmtAffineContext.advance,
          TransitionStmtAffineContext.replaceStateByPairMap,
          stmtMaxStackActions] using hbudget k
  | pop selected update continuation ih =>
      intro hsupport hterminal hbudget
      let hcontinuation : ∀ j, stmtPushSet tm continuation j ⊆
          reachableAlphabet tm j := by
        simpa [stmtPushSet] using hsupport
      have hterminalContinuation :
          (transitionStmtTerminalLayout tm continuation).isSome := by
        simpa [transitionStmtTerminalLayout] using hterminal
      constructor
      · intro k
        have hk := hbudget k
        have hzero : 0 ≤ stmtMaxStackActions tm k
            (.pop selected update continuation) := Nat.zero_le _
        omega
      · apply ih (context.afterPop tm selected update) hcontinuation
          hterminalContinuation
        intro target
        have hk := hbudget target
        rw [show (context.afterPop tm selected update).stackActions =
            context.stackActions ++
              [{ k := selected, kind := .pop context.gateOffset }] by
          rfl]
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
      intro hsupport hterminal hbudget
      simp [transitionStmtTerminalLayout] at hterminal

/-- In the initial context, a machine-wide per-step action budget suffices for
every branch-free program statement. -/
theorem transitionStmtLinearContextPadding_initial
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (label : tm.Λ)
    (hheight : 2 * maxStackActionsPerStep tm + 1 ≤ seed.height)
    (hterminal : (transitionStmtTerminalLayout tm (tm.m label)).isSome) :
    transitionStmtLinearContextPadding tm seed
      (TransitionStmtAffineContext.initial tm) (tm.m label)
      (stmtPushSet_program_subset tm label) := by
  apply transitionStmtLinearContextPadding_of_budget tm seed
    (maxStackActionsPerStep tm) hheight
      (TransitionStmtAffineContext.initial tm) (tm.m label)
      (stmtPushSet_program_subset tm label) hterminal
  intro k
  simpa [TransitionStmtAffineContext.initial, transitionStmtStackActionsFor]
    using stmtMaxStackActions_le_maxStackActionsPerStep tm label k

@[simp] theorem TransitionStmtAffineContext.initial_rowWires
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat) :
    (TransitionStmtAffineContext.initial tm).rowWires tm seed labelOffset =
      arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, coordinate⟩) <;>
    rfl

/-- Every verifier transition seed supplies the static padding required by a
branch-free program statement. -/
theorem transitionStmtLinearContextPadding_initial_verifier
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (label : W.machine.tm.Λ)
    (hterminal :
      (transitionStmtTerminalLayout W.machine.tm
        (W.machine.tm.m label)).isSome) :
    transitionStmtLinearContextPadding W.machine.tm seed
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label)
      (stmtPushSet_program_subset W.machine.tm label) := by
  apply transitionStmtLinearContextPadding_initial W.machine.tm seed label
  · rw [hseed]
    exact verifierHeight_actionPadding_le W input.length
  · exact hterminal

/-- Consequently, a successfully generated initial branch-free form list
evaluates to the full semantic script without any local operand hypotheses. -/
theorem transitionStmtLinearInitialPhaseForms_eval
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed.height = (verifierHeight W).eval input.length)
    (labelOffset : TransitionAffineNat) (label : W.machine.tm.Λ)
    (hterminal :
      (transitionStmtTerminalLayout W.machine.tm
        (W.machine.tm.m label)).isSome)
    (forms : List TransitionAffineStmtPhaseForm)
    (hforms : transitionStmtLinearContextPhaseForms W.machine.tm labelOffset
      (TransitionStmtAffineContext.initial W.machine.tm)
      (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label) =
        some forms) :
    forms.map (fun phase => phase.eval (transitionTailAffineSeed seed)) =
      transitionStmtScript W.machine.tm
        (workHeight W.machine.tm seed.height) seed.start (seed.start + 1)
        (seed.start + labelOffset.eval seed.height)
        (arithmeticWidenedCfgWires W.machine.tm seed.height seed.start
          seed.rowBase)
        (W.machine.tm.m label)
        (stmtPushSet_program_subset W.machine.tm label) := by
  have hpadding := transitionStmtLinearContextPadding_initial_verifier W
    input seed hseed label hterminal
  have heval := transitionStmtLinearContextPhaseForms_eval W.machine.tm seed
    labelOffset (TransitionStmtAffineContext.initial W.machine.tm)
    (W.machine.tm.m label) (stmtPushSet_program_subset W.machine.tm label)
    hpadding forms hforms
  rw [TransitionStmtAffineContext.initial_rowWires] at heval
  simpa [TransitionStmtAffineContext.initial] using heval

end CLRS.Chapter34.Turing.CookLevin
