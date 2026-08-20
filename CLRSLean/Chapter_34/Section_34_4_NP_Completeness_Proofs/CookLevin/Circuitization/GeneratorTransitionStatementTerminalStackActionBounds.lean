import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalRow
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouting

/-!
# Push bounds for terminal statement stack routes

The terminal statement normal form records a fixed heterogeneous stack-action
table.  This module counts the pushes aimed at one selected stack, proves that
filtering the table by stack preserves that count, and identifies the result
with the existing semantic bound `stmtMaxPushes`.  Consequently every terminal
row produced from a machine label fits in the one-step workspace.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Contribution of one global stack action to the push count of `target`. -/
def TransitionStmtStackAction.pushCountFor
    (tm : _root_.Turing.FinTM2) (target : tm.K) :
    TransitionStmtStackAction tm → Nat
  | ⟨selected, .push _⟩ => if selected = target then 1 else 0
  | ⟨_, .pop _⟩ => 0

/-- Number of pushes aimed at one stack in a heterogeneous action table. -/
def transitionStmtStackActionPushCountFor
    (tm : _root_.Turing.FinTM2) (target : tm.K) :
    List (TransitionStmtStackAction tm) → Nat
  | [] => 0
  | action :: rest =>
      action.pushCountFor tm target +
        transitionStmtStackActionPushCountFor tm target rest

/-- Push contribution of an action whose selected stack is already fixed. -/
def TransitionStmtSelectedStackAction.pushCount
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    TransitionStmtSelectedStackAction tm k → Nat
  | .push _ => 1
  | .pop _ => 0

/-- Push count in a per-stack filtered action table. -/
def transitionStmtSelectedStackActionPushCount
    (tm : _root_.Turing.FinTM2) (k : tm.K) :
    List (TransitionStmtSelectedStackAction tm k) → Nat
  | [] => 0
  | action :: rest =>
      action.pushCount tm k +
        transitionStmtSelectedStackActionPushCount tm k rest

/-- Contribution of one heterogeneous action to the total number of actions
aimed at `target`. -/
def TransitionStmtStackAction.actionCountFor
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (action : TransitionStmtStackAction tm) : Nat :=
  if action.k = target then 1 else 0

/-- Total number of push or pop actions aimed at one stack. -/
def transitionStmtStackActionCountFor
    (tm : _root_.Turing.FinTM2) (target : tm.K) :
    List (TransitionStmtStackAction tm) → Nat
  | [] => 0
  | action :: rest =>
      action.actionCountFor tm target +
        transitionStmtStackActionCountFor tm target rest

/-- Filtering the heterogeneous action table for one stack preserves exactly
the number of commands aimed at that stack. -/
theorem transitionStmtStackActionsFor_length_eq
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (actions : List (TransitionStmtStackAction tm)) :
    (transitionStmtStackActionsFor tm target actions).length =
      transitionStmtStackActionCountFor tm target actions := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      change (List.filterMap
          (TransitionStmtStackAction.selectFor tm target) rest).length =
        transitionStmtStackActionCountFor tm target rest at ih
      simp only [TransitionStmtStackAction.selectFor] at ih
      rcases action with ⟨selected, kind⟩
      by_cases hselected : selected = target
      · subst selected
        cases kind <;>
          simp [transitionStmtStackActionsFor,
            TransitionStmtStackAction.selectFor,
            TransitionStmtStackAction.actionCountFor,
            transitionStmtStackActionCountFor, ih] <;> omega
      · cases kind <;>
          simp [transitionStmtStackActionsFor,
            TransitionStmtStackAction.selectFor,
            TransitionStmtStackAction.actionCountFor,
            transitionStmtStackActionCountFor, hselected, ih] <;> omega

/-- Counting one global action agrees with first selecting it for the target
stack and then counting the selected action. -/
theorem TransitionStmtStackAction.pushCountFor_eq_selectFor
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (action : TransitionStmtStackAction tm) :
    action.pushCountFor tm target =
      match action.selectFor tm target with
      | none => 0
      | some selected => selected.pushCount tm target := by
  rcases action with ⟨selected, kind⟩
  by_cases hselected : selected = target
  · subst selected
    cases kind <;>
      simp [TransitionStmtStackAction.pushCountFor,
        TransitionStmtStackAction.selectFor,
        TransitionStmtSelectedStackAction.pushCount]
  · cases kind <;>
      simp [TransitionStmtStackAction.pushCountFor,
        TransitionStmtStackAction.selectFor, hselected]

/-- Filtering a heterogeneous action table for one stack preserves exactly
the pushes aimed at that stack. -/
theorem transitionStmtStackActionsFor_pushCount_eq
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (actions : List (TransitionStmtStackAction tm)) :
    transitionStmtSelectedStackActionPushCount tm target
        (transitionStmtStackActionsFor tm target actions) =
      transitionStmtStackActionPushCountFor tm target actions := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      change transitionStmtSelectedStackActionPushCount tm target
          (List.filterMap (TransitionStmtStackAction.selectFor tm target)
            (action :: rest)) = _
      change transitionStmtSelectedStackActionPushCount tm target
          (List.filterMap (TransitionStmtStackAction.selectFor tm target)
            rest) = _ at ih
      rw [List.filterMap_cons]
      rw [show transitionStmtStackActionPushCountFor tm target
          (action :: rest) =
            action.pushCountFor tm target +
              transitionStmtStackActionPushCountFor tm target rest by rfl]
      rw [action.pushCountFor_eq_selectFor tm target]
      cases hselected : action.selectFor tm target with
      | none => simp [ih]
      | some selected =>
          simp [transitionStmtSelectedStackActionPushCount, ih]

private theorem transitionStmtTerminalStackActionsFrom_pushCount_eq
    (tm : _root_.Turing.FinTM2) (target : tm.K) :
    ∀ (gateOffset : TransitionAffineNat)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k,
        stmtPushSet tm q k ⊆ reachableAlphabet tm k)
      (actions : List (TransitionStmtStackAction tm)),
      transitionStmtTerminalStackActionsFrom tm gateOffset q hsupport =
          some actions →
        transitionStmtStackActionPushCountFor tm target actions =
          stmtMaxPushes tm target q := by
  intro gateOffset q
  induction q generalizing gateOffset with
  | halt =>
      intro hsupport actions hactions
      simp [transitionStmtTerminalStackActionsFrom] at hactions
      subst actions
      rfl
  | goto jump =>
      intro hsupport actions hactions
      simp [transitionStmtTerminalStackActionsFrom] at hactions
      subst actions
      rfl
  | load update continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      exact ih
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + stateCount tm)))
        hcontinuation actions hactions
  | push selected emit continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm selected :=
        fun code =>
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport selected
            simp [stmtPushSet]⟩
      let action : TransitionStmtStackAction tm :=
        { k := selected
          kind := .push fun symbol =>
            gateOffset.add (TransitionAffineNat.const
              (oneHotMapWireOffset
                (fun code => encodeSupportedSymbol (symbolAt code)) symbol)) }
      change (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + (reachableAlphabet tm selected).card)))
        continuation hcontinuation).map (action :: ·) = some actions at hactions
      cases hrest : transitionStmtTerminalStackActionsFrom tm
          (gateOffset.add (TransitionAffineNat.const
            (stateCount tm + (reachableAlphabet tm selected).card)))
          continuation hcontinuation with
      | none => simp [hrest] at hactions
      | some rest =>
          rw [hrest] at hactions
          simp only [Option.map_some, Option.some.injEq] at hactions
          subst actions
          rw [show transitionStmtStackActionPushCountFor tm target
              (action :: rest) =
                (if selected = target then 1 else 0) +
                  transitionStmtStackActionPushCountFor tm target rest by
            simp [transitionStmtStackActionPushCountFor,
              TransitionStmtStackAction.pushCountFor, action]]
          rw [ih _ hcontinuation rest hrest]
          rfl
  | peek selected update continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      exact ih
        (gateOffset.add (TransitionAffineNat.const
          (2 * stateCount tm *
            ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
        hcontinuation actions hactions
  | pop selected update continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let action : TransitionStmtStackAction tm :=
        { k := selected
          kind := .pop gateOffset }
      change (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (1 + 2 * stateCount tm *
            ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
        continuation hcontinuation).map (action :: ·) = some actions at hactions
      cases hrest : transitionStmtTerminalStackActionsFrom tm
          (gateOffset.add (TransitionAffineNat.const
            (1 + 2 * stateCount tm *
              ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
          continuation hcontinuation with
      | none => simp [hrest] at hactions
      | some rest =>
          rw [hrest] at hactions
          simp only [Option.map_some, Option.some.injEq] at hactions
          subst actions
          rw [show transitionStmtStackActionPushCountFor tm target
              (action :: rest) =
                transitionStmtStackActionPushCountFor tm target rest by
            simp [transitionStmtStackActionPushCountFor,
              TransitionStmtStackAction.pushCountFor, action]]
          exact ih _ hcontinuation rest hrest
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport actions hactions
      simp [transitionStmtTerminalStackActionsFrom] at hactions

/-- The action table extracted from a terminal statement spine contains
exactly the pushes counted by the semantic statement bound. -/
theorem transitionStmtTerminalStackActions_pushCount_eq_stmtMaxPushes
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (actions : List (TransitionStmtStackAction tm))
    (hactions : transitionStmtTerminalStackActions tm q hsupport =
      some actions) :
    transitionStmtStackActionPushCountFor tm target actions =
      stmtMaxPushes tm target q := by
  exact transitionStmtTerminalStackActionsFrom_pushCount_eq tm target
    (TransitionAffineNat.const 0) q hsupport actions hactions

private theorem transitionStmtTerminalStackActionsFrom_actionCount_eq
    (tm : _root_.Turing.FinTM2) (target : tm.K) :
    ∀ (gateOffset : TransitionAffineNat)
      (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
      (hsupport : ∀ k,
        stmtPushSet tm q k ⊆ reachableAlphabet tm k)
      (actions : List (TransitionStmtStackAction tm)),
      transitionStmtTerminalStackActionsFrom tm gateOffset q hsupport =
          some actions →
        transitionStmtStackActionCountFor tm target actions =
          stmtMaxStackActions tm target q := by
  intro gateOffset q
  induction q generalizing gateOffset with
  | halt =>
      intro hsupport actions hactions
      simp [transitionStmtTerminalStackActionsFrom] at hactions
      subst actions
      rfl
  | goto jump =>
      intro hsupport actions hactions
      simp [transitionStmtTerminalStackActionsFrom] at hactions
      subst actions
      rfl
  | load update continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      exact ih
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + stateCount tm)))
        hcontinuation actions hactions
  | push selected emit continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        intro k symbol hsymbol
        apply hsupport k
        simp only [stmtPushSet]
        exact Finset.mem_union_right _ hsymbol
      let symbolAt : Fin (stateCount tm) → SupportedSymbol tm selected :=
        fun code =>
          ⟨emit ((stateEquivFin tm).symm code), by
            apply hsupport selected
            simp [stmtPushSet]⟩
      let action : TransitionStmtStackAction tm :=
        { k := selected
          kind := .push fun symbol =>
            gateOffset.add (TransitionAffineNat.const
              (oneHotMapWireOffset
                (fun code => encodeSupportedSymbol (symbolAt code)) symbol)) }
      change (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (stateCount tm + (reachableAlphabet tm selected).card)))
        continuation hcontinuation).map (action :: ·) = some actions at hactions
      cases hrest : transitionStmtTerminalStackActionsFrom tm
          (gateOffset.add (TransitionAffineNat.const
            (stateCount tm + (reachableAlphabet tm selected).card)))
          continuation hcontinuation with
      | none => simp [hrest] at hactions
      | some rest =>
          rw [hrest] at hactions
          simp only [Option.map_some, Option.some.injEq] at hactions
          subst actions
          rw [show transitionStmtStackActionCountFor tm target
              (action :: rest) =
                (if selected = target then 1 else 0) +
                  transitionStmtStackActionCountFor tm target rest by
            simp [transitionStmtStackActionCountFor,
              TransitionStmtStackAction.actionCountFor, action]]
          rw [ih _ hcontinuation rest hrest]
          rfl
  | peek selected update continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      exact ih
        (gateOffset.add (TransitionAffineNat.const
          (2 * stateCount tm *
            ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
        hcontinuation actions hactions
  | pop selected update continuation ih =>
      intro hsupport actions hactions
      have hcontinuation :
          ∀ k, stmtPushSet tm continuation k ⊆ reachableAlphabet tm k := by
        simpa [stmtPushSet] using hsupport
      let action : TransitionStmtStackAction tm :=
        { k := selected
          kind := .pop gateOffset }
      change (transitionStmtTerminalStackActionsFrom tm
        (gateOffset.add (TransitionAffineNat.const
          (1 + 2 * stateCount tm *
            ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
        continuation hcontinuation).map (action :: ·) = some actions at hactions
      cases hrest : transitionStmtTerminalStackActionsFrom tm
          (gateOffset.add (TransitionAffineNat.const
            (1 + 2 * stateCount tm *
              ((reachableAlphabet tm selected).card + 1) + stateCount tm)))
          continuation hcontinuation with
      | none => simp [hrest] at hactions
      | some rest =>
          rw [hrest] at hactions
          simp only [Option.map_some, Option.some.injEq] at hactions
          subst actions
          rw [show transitionStmtStackActionCountFor tm target
              (action :: rest) =
                (if selected = target then 1 else 0) +
                  transitionStmtStackActionCountFor tm target rest by
            simp [transitionStmtStackActionCountFor,
              TransitionStmtStackAction.actionCountFor, action]]
          rw [ih _ hcontinuation rest hrest]
          rfl
  | branch test whenTrue whenFalse ihTrue ihFalse =>
      intro hsupport actions hactions
      simp [transitionStmtTerminalStackActionsFrom] at hactions

/-- The terminal action table contains exactly as many commands for the
selected stack as the structural statement-path action measure. -/
theorem transitionStmtTerminalStackActions_length_eq_stmtMaxStackActions
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (actions : List (TransitionStmtStackAction tm))
    (hactions : transitionStmtTerminalStackActions tm q hsupport =
      some actions) :
    (transitionStmtStackActionsFor tm target actions).length =
      stmtMaxStackActions tm target q := by
  rw [transitionStmtStackActionsFor_length_eq]
  exact transitionStmtTerminalStackActionsFrom_actionCount_eq tm target
    (TransitionAffineNat.const 0) q hsupport actions hactions

/-- A complete terminal row extracted from a machine label never contains
more selected-stack pushes than the uniform one-step machine bound. -/
theorem TransitionStmtTerminalRowLayout.selectedPushCount_le_maxPushesPerStep
    (tm : _root_.Turing.FinTM2) (label : tm.Λ)
    (hsupport : ∀ k,
      stmtPushSet tm (tm.m label) k ⊆ reachableAlphabet tm k)
    (layout : TransitionStmtTerminalRowLayout tm)
    (hlayout : transitionStmtTerminalRowLayout tm (tm.m label) hsupport =
      some layout) (target : tm.K) :
    transitionStmtSelectedStackActionPushCount tm target
        (transitionStmtStackActionsFor tm target layout.stackActions) ≤
      maxPushesPerStep tm := by
  unfold transitionStmtTerminalRowLayout at hlayout
  cases hterminal : transitionStmtTerminalLayout tm (tm.m label) with
  | none => simp [hterminal] at hlayout
  | some terminal =>
      cases hstate : transitionStmtTerminalStateLayout tm (tm.m label) with
      | none => simp [hterminal, hstate] at hlayout
      | some state =>
          cases hstack : transitionStmtTerminalStackActions tm (tm.m label)
              hsupport with
          | none => simp [hterminal, hstate, hstack] at hlayout
          | some actions =>
              simp [hterminal, hstate, hstack] at hlayout
              subst layout
              rw [transitionStmtStackActionsFor_pushCount_eq]
              rw [transitionStmtTerminalStackActions_pushCount_eq_stmtMaxPushes
                tm target (tm.m label) hsupport actions hstack]
              exact stmtMaxPushes_le_maxPushesPerStep tm label target

/-- A complete terminal row contains at most the uniform machine-static
number of selected-stack push/pop commands. -/
theorem TransitionStmtTerminalRowLayout.selectedActionCount_le_maxStackActionsPerStep
    (tm : _root_.Turing.FinTM2) (label : tm.Λ)
    (hsupport : ∀ k,
      stmtPushSet tm (tm.m label) k ⊆ reachableAlphabet tm k)
    (layout : TransitionStmtTerminalRowLayout tm)
    (hlayout : transitionStmtTerminalRowLayout tm (tm.m label) hsupport =
      some layout) (target : tm.K) :
    (transitionStmtStackActionsFor tm target layout.stackActions).length ≤
      maxStackActionsPerStep tm := by
  unfold transitionStmtTerminalRowLayout at hlayout
  cases hterminal : transitionStmtTerminalLayout tm (tm.m label) with
  | none => simp [hterminal] at hlayout
  | some terminal =>
      cases hstate : transitionStmtTerminalStateLayout tm (tm.m label) with
      | none => simp [hterminal, hstate] at hlayout
      | some state =>
          cases hstack : transitionStmtTerminalStackActions tm (tm.m label)
              hsupport with
          | none => simp [hterminal, hstate, hstack] at hlayout
          | some actions =>
              simp [hterminal, hstate, hstack] at hlayout
              subst layout
              rw [transitionStmtTerminalStackActions_length_eq_stmtMaxStackActions
                tm target (tm.m label) hsupport actions hstack]
              exact stmtMaxStackActions_le_maxStackActionsPerStep
                tm label target

/-- The widened one-step workspace has room for every push in a terminal row,
independently of the public tableau height. -/
theorem TransitionStmtTerminalRowLayout.selectedPushCount_le_workHeight
    (tm : _root_.Turing.FinTM2) (label : tm.Λ)
    (hsupport : ∀ k,
      stmtPushSet tm (tm.m label) k ⊆ reachableAlphabet tm k)
    (layout : TransitionStmtTerminalRowLayout tm)
    (hlayout : transitionStmtTerminalRowLayout tm (tm.m label) hsupport =
      some layout) (target : tm.K) (height : Nat) :
    transitionStmtSelectedStackActionPushCount tm target
        (transitionStmtStackActionsFor tm target layout.stackActions) ≤
      workHeight tm height := by
  exact le_trans
    (layout.selectedPushCount_le_maxPushesPerStep tm label hsupport hlayout
      target)
    (by simp [workHeight])

end CLRS.Chapter34.Turing.CookLevin
