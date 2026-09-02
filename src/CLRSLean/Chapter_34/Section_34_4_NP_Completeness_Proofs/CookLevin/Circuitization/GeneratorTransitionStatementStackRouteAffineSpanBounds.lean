import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanTerminal

/-!
# Endpoint bounds for compact affine stack routes

The segment compiler needs more than total route capacity: left deletions must
remain in the long public segment and right deletions must remain in the fixed
overflow padding.  This module records the sharper invariant.  Pops are the
only actions that move the left endpoint, while pushes are the only actions
that move the right endpoint.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

@[simp] theorem TransitionRouteSpan.sourceDrop_dropTail
    (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropTail amount).sourceDrop = span.sourceDrop := by
  unfold TransitionRouteSpan.dropTail
  split_ifs <;> rfl

@[simp] theorem TransitionRouteSpan.sourceRdrop_dropHead
    (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropHead amount).sourceRdrop = span.sourceRdrop := by
  unfold TransitionRouteSpan.dropHead
  split_ifs <;> rfl

@[simp] theorem TransitionRouteSpan.sourceDrop_prepend
    (span : TransitionRouteSpan α) (value : α) :
    (span.prepend value).sourceDrop = span.sourceDrop := by
  rfl

@[simp] theorem TransitionRouteSpan.sourceRdrop_prepend
    (span : TransitionRouteSpan α) (value : α) :
    (span.prepend value).sourceRdrop = span.sourceRdrop := by
  rfl

@[simp] theorem TransitionRouteSpan.sourceDrop_append
    (span : TransitionRouteSpan α) (value : α) :
    (span.append value).sourceDrop = span.sourceDrop := by
  rfl

@[simp] theorem TransitionRouteSpan.sourceRdrop_append
    (span : TransitionRouteSpan α) (value : α) :
    (span.append value).sourceRdrop = span.sourceRdrop := by
  rfl

theorem TransitionRouteSpan.sourceDrop_dropHead_le
    (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropHead amount).sourceDrop ≤ span.sourceDrop + amount := by
  unfold TransitionRouteSpan.dropHead
  split_ifs <;> simp

theorem TransitionRouteSpan.sourceRdrop_dropTail_le
    (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropTail amount).sourceRdrop ≤ span.sourceRdrop + amount := by
  unfold TransitionRouteSpan.dropTail
  split_ifs <;> simp

/-- One selected action moves the height left endpoint by at most two and the
cell left endpoint by at most one. -/
theorem TransitionStmtSelectedStackAction.evalAffineSpan_sourceDrop_le
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (action : TransitionStmtSelectedStackAction tm k) :
    (action.evalAffineSpan tm k labelOffset route).heightSpan.sourceDrop ≤
        route.heightSpan.sourceDrop + 2 ∧
      (action.evalAffineSpan tm k labelOffset route).cellSpan.sourceDrop ≤
        route.cellSpan.sourceDrop + 1 := by
  cases action with
  | push symbolOffsets =>
      simp [TransitionStmtSelectedStackAction.evalAffineSpan,
        TransitionStackAffineRouteSpanBlock.push]
  | pop heightWireOffset =>
      constructor
      · simpa [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.pop] using
          route.heightSpan.sourceDrop_dropHead_le 2
      · simpa [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.pop] using
          route.cellSpan.sourceDrop_dropHead_le 1

/-- One selected action moves either right endpoint only when it is a push. -/
theorem TransitionStmtSelectedStackAction.evalAffineSpan_sourceRdrop_le
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (action : TransitionStmtSelectedStackAction tm k) :
    (action.evalAffineSpan tm k labelOffset route).heightSpan.sourceRdrop ≤
        route.heightSpan.sourceRdrop + action.pushCount tm k ∧
      (action.evalAffineSpan tm k labelOffset route).cellSpan.sourceRdrop ≤
        route.cellSpan.sourceRdrop + action.pushCount tm k := by
  cases action with
  | push symbolOffsets =>
      constructor
      · simpa [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.push,
          TransitionStmtSelectedStackAction.pushCount] using
          route.heightSpan.sourceRdrop_dropTail_le 1
      · simpa [TransitionStmtSelectedStackAction.evalAffineSpan,
          TransitionStackAffineRouteSpanBlock.push,
          TransitionStmtSelectedStackAction.pushCount] using
          route.cellSpan.sourceRdrop_dropTail_le 1
  | pop heightWireOffset =>
      simp [TransitionStmtSelectedStackAction.evalAffineSpan,
        TransitionStackAffineRouteSpanBlock.pop,
        TransitionStmtSelectedStackAction.pushCount]

/-- Left-endpoint bounds for an arbitrary affine-span fold from an existing
route. -/
theorem transitionStmtSelectedStackAffineActionSpans_sourceDrop_le_from
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).heightSpan.sourceDrop ≤
        route.heightSpan.sourceDrop + 2 * actions.length ∧
      (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).cellSpan.sourceDrop ≤
        route.cellSpan.sourceDrop + actions.length := by
  induction actions generalizing route with
  | nil => simp [transitionStmtSelectedStackAffineActionSpans]
  | cons action rest ih =>
      let next := action.evalAffineSpan tm k labelOffset route
      have hrest := ih next
      have hstep := action.evalAffineSpan_sourceDrop_le tm k labelOffset route
      change
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset next
          rest).heightSpan.sourceDrop ≤
            route.heightSpan.sourceDrop + 2 * (action :: rest).length ∧
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset next
          rest).cellSpan.sourceDrop ≤
            route.cellSpan.sourceDrop + (action :: rest).length
      dsimp [next] at hrest ⊢
      omega

/-- Right-endpoint bounds for an arbitrary affine-span fold from an existing
route. -/
theorem transitionStmtSelectedStackAffineActionSpans_sourceRdrop_le_from
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).heightSpan.sourceRdrop ≤
        route.heightSpan.sourceRdrop +
          transitionStmtSelectedStackActionPushCount tm k actions ∧
      (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).cellSpan.sourceRdrop ≤
        route.cellSpan.sourceRdrop +
          transitionStmtSelectedStackActionPushCount tm k actions := by
  induction actions generalizing route with
  | nil => simp [transitionStmtSelectedStackAffineActionSpans,
      transitionStmtSelectedStackActionPushCount]
  | cons action rest ih =>
      let next := action.evalAffineSpan tm k labelOffset route
      have hrest := ih next
      have hstep := action.evalAffineSpan_sourceRdrop_le tm k labelOffset route
      change
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset next
          rest).heightSpan.sourceRdrop ≤
            route.heightSpan.sourceRdrop +
              transitionStmtSelectedStackActionPushCount tm k
                (action :: rest) ∧
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset next
          rest).cellSpan.sourceRdrop ≤
            route.cellSpan.sourceRdrop +
              transitionStmtSelectedStackActionPushCount tm k
                (action :: rest)
      rw [show transitionStmtSelectedStackActionPushCount tm k
          (action :: rest) = action.pushCount tm k +
            transitionStmtSelectedStackActionPushCount tm k rest by rfl]
      dsimp [next] at hrest ⊢
      omega

/-- Final left endpoints starting from the identity span. -/
theorem transitionStmtSelectedStackAffineActionSpans_sourceDrop_le
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity
        actions).heightSpan.sourceDrop ≤ 2 * actions.length ∧
      (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity
        actions).cellSpan.sourceDrop ≤ actions.length := by
  simpa [TransitionStackAffineRouteSpanBlock.identity,
    TransitionRouteSpan.identity] using
    transitionStmtSelectedStackAffineActionSpans_sourceDrop_le_from tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions

/-- Final right endpoints starting from the identity span. -/
theorem transitionStmtSelectedStackAffineActionSpans_sourceRdrop_le
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity
        actions).heightSpan.sourceRdrop ≤
          transitionStmtSelectedStackActionPushCount tm k actions ∧
      (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity
        actions).cellSpan.sourceRdrop ≤
          transitionStmtSelectedStackActionPushCount tm k actions := by
  simpa [TransitionStackAffineRouteSpanBlock.identity,
    TransitionRouteSpan.identity] using
    transitionStmtSelectedStackAffineActionSpans_sourceRdrop_le_from tm k
      labelOffset TransitionStackAffineRouteSpanBlock.identity actions

/-- Real terminal routes keep left deletion inside the verifier's static
two-cells-per-action padding. -/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanRoute_sourceDrop_le
    (tm : _root_.Turing.FinTM2) (label : tm.Λ)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm)
    (hlayout : transitionStmtTerminalRowLayout tm (tm.m label)
      (stmtPushSet_program_subset tm label) = some layout) (k : tm.K) :
    (layout.stackAffineSpanRoute tm k labelOffset).heightSpan.sourceDrop ≤
        2 * maxStackActionsPerStep tm ∧
      (layout.stackAffineSpanRoute tm k labelOffset).cellSpan.sourceDrop ≤
        maxStackActionsPerStep tm := by
  have hend := transitionStmtSelectedStackAffineActionSpans_sourceDrop_le tm k
    labelOffset (transitionStmtStackActionsFor tm k layout.stackActions)
  have hcount := layout.selectedActionCount_le_maxStackActionsPerStep tm label
    (stmtPushSet_program_subset tm label) hlayout k
  unfold TransitionStmtTerminalRowLayout.stackAffineSpanRoute
  omega

/-- Real terminal routes keep right deletion entirely inside the fixed
push-overflow padding. -/
theorem TransitionStmtTerminalRowLayout.stackAffineSpanRoute_sourceRdrop_le
    (tm : _root_.Turing.FinTM2) (label : tm.Λ)
    (labelOffset : TransitionAffineNat)
    (layout : TransitionStmtTerminalRowLayout tm)
    (hlayout : transitionStmtTerminalRowLayout tm (tm.m label)
      (stmtPushSet_program_subset tm label) = some layout) (k : tm.K) :
    (layout.stackAffineSpanRoute tm k labelOffset).heightSpan.sourceRdrop ≤
        maxPushesPerStep tm ∧
      (layout.stackAffineSpanRoute tm k labelOffset).cellSpan.sourceRdrop ≤
        maxPushesPerStep tm := by
  have hend := transitionStmtSelectedStackAffineActionSpans_sourceRdrop_le tm k
    labelOffset (transitionStmtStackActionsFor tm k layout.stackActions)
  have hpush := layout.selectedPushCount_le_maxPushesPerStep tm label
    (stmtPushSet_program_subset tm label) hlayout k
  unfold TransitionStmtTerminalRowLayout.stackAffineSpanRoute
  omega

end CLRS.Chapter34.Turing.CookLevin
