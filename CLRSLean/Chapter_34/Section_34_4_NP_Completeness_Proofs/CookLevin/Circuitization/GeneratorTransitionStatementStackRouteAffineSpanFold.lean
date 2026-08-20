import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAffineSpanActions
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValueShape

/-!
# Complete selected-action folds on compact affine route spans

Each stack action removes at most two coordinates from the surviving interval
of the original widened stack.  This module turns that observation into a
route budget invariant, proves it is preserved by both primitive actions, and
uses it to lift the one-step affine-span theorems to an arbitrary fixed action
sequence.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Number of original-source coordinates removed from the two ends. -/
def TransitionRouteSpan.removalCount (span : TransitionRouteSpan α) : Nat :=
  span.sourceDrop + span.sourceRdrop

@[simp] theorem TransitionRouteSpan.removalCount_identity :
    (TransitionRouteSpan.identity : TransitionRouteSpan α).removalCount = 0 := by
  rfl

@[simp] theorem TransitionRouteSpan.removalCount_prepend
    (span : TransitionRouteSpan α) (value : α) :
    (span.prepend value).removalCount = span.removalCount := by
  rfl

@[simp] theorem TransitionRouteSpan.removalCount_append
    (span : TransitionRouteSpan α) (value : α) :
    (span.append value).removalCount = span.removalCount := by
  rfl

@[simp] theorem TransitionRouteSpan.removalCount_map
    (span : TransitionRouteSpan α) (f : α → β) :
    (span.map f).removalCount = span.removalCount := by
  rfl

/-- Dropping a prefix transfers at most the requested amount to the source
interval. -/
theorem TransitionRouteSpan.removalCount_dropHead_le
    (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropHead amount).removalCount ≤ span.removalCount + amount := by
  unfold TransitionRouteSpan.dropHead TransitionRouteSpan.removalCount
  split_ifs <;> simp
  all_goals omega

/-- Dropping a suffix transfers at most the requested amount to the source
interval. -/
theorem TransitionRouteSpan.removalCount_dropTail_le
    (span : TransitionRouteSpan α) (amount : Nat) :
    (span.dropTail amount).removalCount ≤ span.removalCount + amount := by
  unfold TransitionRouteSpan.dropTail TransitionRouteSpan.removalCount
  split_ifs <;> simp
  all_goals omega

/-- Exact length of the surviving source interval. -/
theorem TransitionRouteSpan.middle_length
    (span : TransitionRouteSpan α) (source : List α) :
    (span.middle source).length = source.length - span.removalCount := by
  unfold TransitionRouteSpan.middle List.rdrop
  simp [TransitionRouteSpan.removalCount, Nat.sub_sub]
  omega

/-- Enough total source space implies a lower bound on the surviving middle.
-/
theorem TransitionRouteSpan.le_middle_length_of_budget
    (span : TransitionRouteSpan α) (source : List α) (needed : Nat)
    (hbudget : span.removalCount + needed ≤ source.length) :
    needed ≤ (span.middle source).length := by
  rw [span.middle_length]
  omega

/-- A compact route has enough untouched original coordinates for a specified
number of remaining stack actions.  The factor two uniformly covers both
height deletion by pop and the cheaper cell-row transformations. -/
def TransitionStackAffineRouteSpanBlock.HasRouteBudget
    (route : TransitionStackAffineRouteSpanBlock)
    (source : TransitionStackValueBlock) (remaining : Nat) : Prop :=
  route.heightSpan.removalCount + 2 * remaining + 1 ≤
      source.heightValues.length ∧
    route.cellSpan.removalCount + 2 * remaining + 1 ≤
      source.cellRows.length

/-- The identity route inherits any action budget supported by the source
lengths. -/
theorem TransitionStackAffineRouteSpanBlock.HasRouteBudget.identity
    (source : TransitionStackValueBlock) (remaining : Nat)
    (hheight : 2 * remaining + 1 ≤ source.heightValues.length)
    (hcells : 2 * remaining + 1 ≤ source.cellRows.length) :
    TransitionStackAffineRouteSpanBlock.HasRouteBudget
      TransitionStackAffineRouteSpanBlock.identity source remaining := by
  exact ⟨by simpa [TransitionStackAffineRouteSpanBlock.identity,
    TransitionStackAffineRouteSpanBlock.HasRouteBudget] using hheight,
    by simpa [TransitionStackAffineRouteSpanBlock.identity,
      TransitionStackAffineRouteSpanBlock.HasRouteBudget] using hcells⟩

/-- Consuming a push preserves the budget for the remaining suffix. -/
theorem TransitionStackAffineRouteSpanBlock.HasRouteBudget.push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock) (remaining : Nat)
    (hbudget : route.HasRouteBudget source (remaining + 1)) :
    (route.push tm k falseForm symbolForms).HasRouteBudget source remaining := by
  rcases hbudget with ⟨hheight, hcells⟩
  constructor
  · refine le_trans ?_ hheight
    have hdrop := route.heightSpan.removalCount_dropTail_le 1
    simp only [TransitionStackAffineRouteSpanBlock.push,
      TransitionRouteSpan.removalCount_prepend]
    omega
  · refine le_trans ?_ hcells
    have hdrop := route.cellSpan.removalCount_dropTail_le 1
    simp only [TransitionStackAffineRouteSpanBlock.push,
      TransitionRouteSpan.removalCount_prepend]
    omega

/-- Consuming a pop preserves the budget for the remaining suffix. -/
theorem TransitionStackAffineRouteSpanBlock.HasRouteBudget.pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseForm trueForm freshForm : AffineUnaryTripleForm)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock) (remaining : Nat)
    (hbudget : route.HasRouteBudget source (remaining + 1)) :
    (route.pop tm k falseForm trueForm freshForm).HasRouteBudget source
      remaining := by
  rcases hbudget with ⟨hheight, hcells⟩
  constructor
  · refine le_trans ?_ hheight
    have hdrop := route.heightSpan.removalCount_dropHead_le 2
    simp only [TransitionStackAffineRouteSpanBlock.pop,
      TransitionRouteSpan.removalCount_append,
      TransitionRouteSpan.removalCount_prepend]
    omega
  · refine le_trans ?_ hcells
    have hdrop := route.cellSpan.removalCount_dropHead_le 1
    simp only [TransitionStackAffineRouteSpanBlock.pop,
      TransitionRouteSpan.removalCount_append]
    omega

/-- Fixed symbolic action on a compact affine span. -/
def TransitionStmtSelectedStackAction.evalAffineSpan
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock) :
    TransitionStmtSelectedStackAction tm k →
      TransitionStackAffineRouteSpanBlock
  | .push symbolOffsets =>
      route.push tm k
        (transitionAbsoluteStartForm (TransitionAffineNat.const 0))
        (fun target => transitionAbsoluteStartForm
          (labelOffset.add
            ((symbolOffsets target).shiftInput (maxPushesPerStep tm))))
  | .pop heightWireOffset =>
      route.pop tm k
        (transitionAbsoluteStartForm (TransitionAffineNat.const 0))
        (transitionAbsoluteStartForm (TransitionAffineNat.const 1))
        (transitionAbsoluteStartForm
          (labelOffset.add
            (heightWireOffset.shiftInput (maxPushesPerStep tm))))

/-- One symbolic span action consumes its fixed two-coordinate budget. -/
theorem TransitionStmtSelectedStackAction.evalAffineSpan_hasRouteBudget
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock)
    (action : TransitionStmtSelectedStackAction tm k) (remaining : Nat)
    (hbudget : route.HasRouteBudget source (remaining + 1)) :
    (action.evalAffineSpan tm k labelOffset route).HasRouteBudget source
      remaining := by
  cases action with
  | push symbolOffsets =>
      exact hbudget.push tm k _ _ source route remaining
  | pop heightWireOffset =>
      exact hbudget.pop tm k _ _ _ source route remaining

/-- Evaluating one affine span action gives the established list-valued stack
semantics.  The remaining-action budget supplies all prefix/suffix safety
conditions required by the primitive span theorems. -/
theorem TransitionStmtSelectedStackAction.evalAffineSpan_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock)
    (action : TransitionStmtSelectedStackAction tm k) (remaining : Nat)
    (hwork : 0 < workHeight tm seed.height)
    (hshape : (route.eval seed source).HasShape tm k
      (workHeight tm seed.height))
    (hbudget : route.HasRouteBudget source (remaining + 1)) :
    (action.evalAffineSpan tm k labelOffset route).eval seed source =
      action.evalValues tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (route.eval seed source) := by
  have hheightHeadInside (f : AffineUnaryTripleForm → Nat) :
      2 ≤ (route.heightSpan.map f).headValues.length +
        ((route.heightSpan.map f).middle source.heightValues).length := by
    have hmiddle :
        2 ≤ ((route.heightSpan.map f).middle source.heightValues).length := by
      apply (route.heightSpan.map f).le_middle_length_of_budget
        source.heightValues 2
      simpa only [TransitionRouteSpan.removalCount_map] using
        (le_trans (by omega) hbudget.1)
    omega
  have hheightTailInside (f : AffineUnaryTripleForm → Nat) :
      1 ≤ (route.heightSpan.map f).tailValues.length +
        ((route.heightSpan.map f).middle source.heightValues).length := by
    have hmiddle :
        2 ≤ ((route.heightSpan.map f).middle source.heightValues).length := by
      apply (route.heightSpan.map f).le_middle_length_of_budget
        source.heightValues 2
      simpa only [TransitionRouteSpan.removalCount_map] using
        (le_trans (by omega) hbudget.1)
    omega
  have hcellHeadInside (f : List AffineUnaryTripleForm → List Nat) :
      1 ≤ (route.cellSpan.map f).headValues.length +
        ((route.cellSpan.map f).middle source.cellRows).length := by
    have hmiddle :
        2 ≤ ((route.cellSpan.map f).middle source.cellRows).length := by
      apply (route.cellSpan.map f).le_middle_length_of_budget
        source.cellRows 2
      simpa only [TransitionRouteSpan.removalCount_map] using
        (le_trans (by omega) hbudget.2)
    omega
  have hcellTailInside (f : List AffineUnaryTripleForm → List Nat) :
      1 ≤ (route.cellSpan.map f).tailValues.length +
        ((route.cellSpan.map f).middle source.cellRows).length := by
    have hmiddle :
        2 ≤ ((route.cellSpan.map f).middle source.cellRows).length := by
      apply (route.cellSpan.map f).le_middle_length_of_budget
        source.cellRows 2
      simpa only [TransitionRouteSpan.removalCount_map] using
        (le_trans (by omega) hbudget.2)
    omega
  rcases hshape with ⟨hheightLength, hcellLength, hrows⟩
  cases action with
  | push symbolOffsets =>
      simp only [TransitionStmtSelectedStackAction.evalAffineSpan,
        TransitionStmtSelectedStackAction.evalValues]
      rw [route.eval_push tm seed k (workHeight tm seed.height) hwork _ _
        source hheightLength hcellLength
        (hheightTailInside _) (hcellTailInside _)]
      have hfalse :
          affineUnaryTripleFormValue
              (transitionAbsoluteStartForm (TransitionAffineNat.const 0))
              (transitionTailAffineSeed seed) = seed.start := by
        rw [transitionAbsoluteStartForm_value]
        simp
      rw [hfalse]
      congr 1
      funext target
      rw [transitionAbsoluteStartForm_value,
        TransitionAffineNat.eval_add,
        TransitionAffineNat.eval_shiftInput]
      simp [workHeight, Nat.add_assoc]
  | pop heightWireOffset =>
      simp only [TransitionStmtSelectedStackAction.evalAffineSpan,
        TransitionStmtSelectedStackAction.evalValues]
      rw [route.eval_pop tm seed k (workHeight tm seed.height) hwork _ _ _
        source (hheightHeadInside _) (hcellHeadInside _)]
      rw [transitionAbsoluteStartForm_value,
        transitionAbsoluteStartForm_value,
        transitionAbsoluteStartForm_value,
        TransitionAffineNat.eval_add,
        TransitionAffineNat.eval_shiftInput]
      simp [workHeight, Nat.add_assoc]

/-- Complete symbolic affine-span normalization of a selected action list. -/
def transitionStmtSelectedStackAffineActionSpans
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteSpanBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    TransitionStackAffineRouteSpanBlock :=
  actions.foldl
    (fun current action => action.evalAffineSpan tm k labelOffset current)
    route

/-- Complete affine-span normalization commutes with the selected-action
value fold from any shaped, sufficiently budgeted starting route. -/
theorem transitionStmtSelectedStackAffineActionSpans_values_from
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (hwork : 0 < workHeight tm seed.height)
    (hshape : (route.eval seed source).HasShape tm k
      (workHeight tm seed.height))
    (hbudget : route.HasRouteBudget source actions.length) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset route
        actions).eval seed source =
      transitionStmtSelectedStackActionValues_eval tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (route.eval seed source) actions := by
  induction actions generalizing route with
  | nil => rfl
  | cons action rest ih =>
      have hstep := action.evalAffineSpan_eval tm seed k labelOffset source
        route rest.length hwork hshape (by simpa using hbudget)
      have hnextBudget := action.evalAffineSpan_hasRouteBudget tm k labelOffset
        source route rest.length (by simpa using hbudget)
      have hnextShape :
          ((action.evalAffineSpan tm k labelOffset route).eval seed source).HasShape
            tm k (workHeight tm seed.height) := by
        rw [hstep]
        exact action.evalValues_hasShape tm k
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (route.eval seed source) hshape
      change
        (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
          (action.evalAffineSpan tm k labelOffset route) rest).eval seed source =
        transitionStmtSelectedStackActionValues_eval tm k
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (action.evalValues tm k
            (seed.start + labelOffset.eval seed.height)
            (workHeight tm seed.height) seed.start (seed.start + 1)
            (route.eval seed source)) rest
      rw [ih (action.evalAffineSpan tm k labelOffset route) hnextShape
        hnextBudget]
      rw [hstep]

/-- Starting from the identity span, complete affine normalization evaluates
to the exact sequential stack semantics whenever the fixed workspace reserves
two coordinates per selected action plus one sentinel coordinate. -/
theorem transitionStmtSelectedStackAffineActionSpans_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (source : TransitionStackValueBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k))
    (hshape : source.HasShape tm k (workHeight tm seed.height))
    (hcapacity : 2 * actions.length + 1 ≤ workHeight tm seed.height) :
    (transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity actions).eval seed source =
      transitionStmtSelectedStackActionValues_eval tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        source actions := by
  have hwork : 0 < workHeight tm seed.height := by omega
  have hbudget : TransitionStackAffineRouteSpanBlock.HasRouteBudget
      TransitionStackAffineRouteSpanBlock.identity source actions.length := by
    apply TransitionStackAffineRouteSpanBlock.HasRouteBudget.identity
    · rw [hshape.1]
      omega
    · rw [hshape.2.1]
      exact hcapacity
  simpa only [TransitionStackAffineRouteSpanBlock.eval_identity] using
    (transitionStmtSelectedStackAffineActionSpans_values_from tm seed k
      labelOffset source TransitionStackAffineRouteSpanBlock.identity actions
      hwork (by simpa using hshape) hbudget)

end CLRS.Chapter34.Turing.CookLevin
