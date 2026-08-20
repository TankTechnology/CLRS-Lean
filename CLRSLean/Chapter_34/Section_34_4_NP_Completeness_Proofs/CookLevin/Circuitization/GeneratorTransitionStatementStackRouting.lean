import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalStack

/-!
# Per-stack routing of terminal statement actions

The terminal statement normal form stores one heterogeneous action list for
all verifier stacks.  A concrete source compiler, however, emits the stacks in
a fixed order and can process each stack independently.  This file filters the
global table to one selected stack and proves that executing the filtered table
is exactly the corresponding projection of the original whole-configuration
execution.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- An action after its selected stack has been fixed. -/
abbrev TransitionStmtSelectedStackAction
    (tm : _root_.Turing.FinTM2) (k : tm.K) :=
  TransitionStmtStackActionKind tm k

/-- Evaluate an action directly on its selected stack. -/
def TransitionStmtSelectedStackAction.eval
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : StackWires tm height k) :
    TransitionStmtSelectedStackAction tm k → StackWires tm height k
  | .push symbolOffsets =>
      arithmeticPushStackWires tm k falseWire
        (fun target => originStart + (symbolOffsets target).eval height)
        height source
  | .pop heightWireOffset =>
      arithmeticPopStackWires tm k falseWire trueWire
        (originStart + heightWireOffset.eval height) height source

/-- Retain an action exactly when it targets the requested stack. -/
noncomputable def TransitionStmtStackAction.selectFor
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (action : TransitionStmtStackAction tm) :
    Option (TransitionStmtSelectedStackAction tm target) :=
  if h : action.k = target then some (h ▸ action.kind) else none

/-- The verifier-fixed action subsequence for one selected stack. -/
noncomputable def transitionStmtStackActionsFor
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (actions : List (TransitionStmtStackAction tm)) :
    List (TransitionStmtSelectedStackAction tm target) :=
  actions.filterMap (TransitionStmtStackAction.selectFor tm target)

/-- Sequential execution of one selected stack's filtered action table. -/
def transitionStmtSelectedStackActions_eval
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : StackWires tm height k)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    StackWires tm height k :=
  actions.foldl
    (fun current action =>
      action.eval tm k originStart height falseWire trueWire current)
    source

/-- Projecting one global action either applies its selected-stack action or
leaves the requested stack unchanged. -/
theorem TransitionStmtStackAction.eval_stack_eq_selectFor
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (action : TransitionStmtStackAction tm) :
    (action.eval tm originStart height falseWire trueWire source).stack target =
      match action.selectFor tm target with
      | none => source.stack target
      | some selected =>
          selected.eval tm target originStart height falseWire trueWire
            (source.stack target) := by
  rcases action with ⟨selected, kind⟩
  by_cases hselected : selected = target
  · subst target
    cases kind <;>
      simp [TransitionStmtStackAction.selectFor,
        TransitionStmtStackAction.eval,
        TransitionStmtSelectedStackAction.eval,
        arithmeticPushCfgWires, arithmeticPopCfgWires]
  · cases kind <;>
      simp [TransitionStmtStackAction.selectFor, hselected,
        TransitionStmtStackAction.eval,
        arithmeticPushCfgWires, arithmeticPopCfgWires,
        CfgBundle.replaceStack_stack_other, Ne.symm hselected]

/-- The global action fold decomposes exactly into independent per-stack
folds.  No permutation or approximation is hidden in the decomposition. -/
theorem transitionStmtStackActions_eval_stack_eq_selected
    (tm : _root_.Turing.FinTM2) (target : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (actions : List (TransitionStmtStackAction tm)) :
    (transitionStmtStackActions_eval tm originStart height falseWire trueWire
        source actions).stack target =
      transitionStmtSelectedStackActions_eval tm target originStart height
        falseWire trueWire (source.stack target)
        (transitionStmtStackActionsFor tm target actions) := by
  induction actions generalizing source with
  | nil => rfl
  | cons action rest ih =>
      change
        (transitionStmtStackActions_eval tm originStart height falseWire
          trueWire
          (action.eval tm originStart height falseWire trueWire source)
          rest).stack target = _
      rw [ih]
      rw [action.eval_stack_eq_selectFor tm target originStart height
        falseWire trueWire source]
      unfold transitionStmtStackActionsFor
      simp only [List.filterMap_cons]
      cases hselected : action.selectFor tm target with
      | none =>
          simp [transitionStmtSelectedStackActions_eval]
      | some selected =>
          simp [transitionStmtSelectedStackActions_eval]

end CLRS.Chapter34.Turing.CookLevin
