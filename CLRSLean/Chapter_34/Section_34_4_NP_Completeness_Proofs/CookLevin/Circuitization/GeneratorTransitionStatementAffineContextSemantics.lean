import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementAffineContext

/-!
# Semantics of affine statement-prefix contexts

The symbolic context is useful to the generator only if it denotes the same
continuation configuration as the ordinary statement compiler.  This module
interprets a context as typed `CfgWires` and proves that its compact affine
stack routes evaluate exactly to those typed stacks.  The theorem is stated
with the precise per-stack capacity hypothesis so later verifier-row code can
discharge it from the uniform action-padding bound.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Typed continuation configuration denoted by a recorded prefix.  Stack
actions are executed first; replacing state afterwards is extensionally
equivalent to their operational interleaving because stack actions preserve
all state coordinates. -/
def TransitionStmtAffineContext.wires
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (context : TransitionStmtAffineContext tm) : CfgWires tm height :=
  (transitionStmtStackActions_eval tm originStart height falseWire trueWire
      source context.stackActions).replaceState
    (context.state.wires tm originStart height source)

@[simp] theorem TransitionStmtAffineContext.wires_state
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (context : TransitionStmtAffineContext tm) :
    (context.wires tm originStart height falseWire trueWire source).state =
      context.state.wires tm originStart height source := by
  rfl

@[simp] theorem TransitionStmtAffineContext.wires_stack
    (tm : _root_.Turing.FinTM2) (originStart height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (context : TransitionStmtAffineContext tm) (k : tm.K) :
    (context.wires tm originStart height falseWire trueWire source).stack k =
      (transitionStmtStackActions_eval tm originStart height falseWire
        trueWire source context.stackActions).stack k := by
  simp [TransitionStmtAffineContext.wires]

/-- The affine state forms denote the typed state component of the context's
continuation configuration. -/
theorem TransitionStmtAffineContext.stateForm_eq_wires
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (target : Fin (stateCount tm)) :
    affineUnaryTripleFormValue
        (context.stateForm tm labelOffset target)
        (transitionTailAffineSeed seed) =
      (context.wires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)).state
        target := by
  rw [context.wires_state]
  exact context.stateForm_value tm seed labelOffset target

/-- Under the exact fixed-capacity budget, evaluating one selected compact
route gives the same stack as executing the context's typed action prefix. -/
theorem TransitionStmtAffineContext.stackRoute_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (hcapacity :
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ workHeight tm seed.height) :
    (context.stackRoute tm labelOffset k).eval seed
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k)) =
      TransitionStackValueBlock.ofWires
        ((context.wires tm
          (seed.start + labelOffset.eval seed.height)
          (workHeight tm seed.height) seed.start (seed.start + 1)
          (arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase)).stack k) := by
  let source := arithmeticWidenedCfgWires tm seed.height seed.start
    seed.rowBase
  let actions := transitionStmtStackActionsFor tm k context.stackActions
  have hshape :
      (TransitionStackValueBlock.ofWires (source.stack k)).HasShape tm k
        (workHeight tm seed.height) :=
    TransitionStackValueBlock.hasShape_ofWires tm k
      (workHeight tm seed.height) (source.stack k)
  rw [show context.stackRoute tm labelOffset k =
      transitionStmtSelectedStackAffineActionSpans tm k labelOffset
        TransitionStackAffineRouteSpanBlock.identity actions by rfl]
  rw [transitionStmtSelectedStackAffineActionSpans_values tm seed k
    labelOffset (TransitionStackValueBlock.ofWires (source.stack k)) actions
    hshape hcapacity]
  rw [← transitionStmtSelectedStackActions_eval_values tm k
    (seed.start + labelOffset.eval seed.height)
    (workHeight tm seed.height) seed.start (seed.start + 1)
    (source.stack k) actions]
  rw [← transitionStmtStackActions_eval_stack_eq_selected tm k
    (seed.start + labelOffset.eval seed.height)
    (workHeight tm seed.height) seed.start (seed.start + 1)
    source context.stackActions]
  exact congrArg TransitionStackValueBlock.ofWires
    (context.wires_stack tm
      (seed.start + labelOffset.eval seed.height)
      (workHeight tm seed.height) seed.start (seed.start + 1) source k).symm

end CLRS.Chapter34.Turing.CookLevin
