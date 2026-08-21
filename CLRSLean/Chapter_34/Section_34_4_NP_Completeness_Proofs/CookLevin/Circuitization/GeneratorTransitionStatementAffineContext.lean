import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackSpanHeadAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalPrefixAffine

/-!
# Affine contexts for recursive statement compilation

A continuation does not start from the public tableau row unchanged.  Earlier
primitive phases may have replaced the state family and may have pushed or
popped verifier stacks.  This module packages precisely that prefix effect:
an affine gate offset, a normalized state family, and the already executed
static stack-action table.  All coordinates remain relative to the enclosing
statement start, so the existing terminal-row and compact-span proofs can be
reused without recompiling the source word.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Symbolic effect of a statement prefix.  `gateOffset` and all coordinates
stored in the component layouts are functions of the positive workspace
height, not of the raw verifier height. -/
structure TransitionStmtAffineContext (tm : _root_.Turing.FinTM2) where
  gateOffset : TransitionAffineNat
  state : TransitionStmtStateLayout tm
  stackActions : List (TransitionStmtStackAction tm)

/-- Empty prefix at the beginning of one dispatch statement arm. -/
def TransitionStmtAffineContext.initial
    (tm : _root_.Turing.FinTM2) : TransitionStmtAffineContext tm :=
  { gateOffset := TransitionAffineNat.const 0
    state := .source
    stackActions := [] }

/-- Convert a workspace-relative offset to a transition-row-relative offset.
The enclosing label offset is already expressed in the raw verifier height. -/
def TransitionStmtAffineContext.absoluteOffset
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) : TransitionAffineNat :=
  labelOffset.add
    (context.gateOffset.shiftInput (maxPushesPerStep tm))

/-- Absolute affine wire form of the next fresh gate. -/
def TransitionStmtAffineContext.startForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) : AffineUnaryTripleForm :=
  transitionAbsoluteStartForm (context.absoluteOffset tm labelOffset)

/-- Affine form of one state coordinate after the recorded prefix. -/
def TransitionStmtAffineContext.stateForm
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (target : Fin (stateCount tm)) : AffineUnaryTripleForm :=
  match context.state with
  | .source => transitionWidenedStateForm tm target
  | .fixed offsets =>
      transitionAbsoluteStartForm
        (labelOffset.add
          ((offsets target).shiftInput (maxPushesPerStep tm)))

/-- Compact affine route of one selected stack after the recorded prefix. -/
def TransitionStmtAffineContext.stackRoute
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K) :
    TransitionStackAffineRouteSpanBlock :=
  transitionStmtSelectedStackAffineActionSpans tm k labelOffset
    TransitionStackAffineRouteSpanBlock.identity
    (transitionStmtStackActionsFor tm k context.stackActions)

/-- Advance past a fixed affine number of gates. -/
def TransitionStmtAffineContext.advance
    (context : TransitionStmtAffineContext tm)
    (cost : TransitionAffineNat) : TransitionStmtAffineContext tm :=
  { context with gateOffset := context.gateOffset.add cost }

/-- Record the state output of a one-hot map beginning at the current gate. -/
def TransitionStmtAffineContext.replaceStateByMap
    (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm)
    {n : Nat} (table : Fin n → Fin (stateCount tm)) :
    TransitionStmtAffineContext tm :=
  { context with
      state := .fixed fun target =>
        context.gateOffset.add
          (TransitionAffineNat.const (oneHotMapWireOffset table target)) }

/-- Record the state output of a one-hot pair map.  `pairPrefix` is the
number of gates emitted immediately before the pair map (one for `pop`, zero
for `peek`). -/
def TransitionStmtAffineContext.replaceStateByPairMap
    (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm) (pairPrefix : Nat)
    {n p : Nat} (table : Fin n → Fin p → Fin (stateCount tm)) :
    TransitionStmtAffineContext tm :=
  { context with
      state := .fixed fun target =>
        context.gateOffset.add
          (TransitionAffineNat.const
            (pairPrefix + oneHotPairMapWireOffset table target)) }

/-- Append the stack action induced by a push whose symbol lookup begins at
the current gate. -/
def TransitionStmtAffineContext.recordPush
    (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    {n : Nat} (table : Fin n → Fin (reachableAlphabet tm k).card) :
    TransitionStmtAffineContext tm :=
  { context with
      stackActions := context.stackActions ++
        [{ k := k
           kind := .push fun target =>
             context.gateOffset.add
               (TransitionAffineNat.const
                 (oneHotMapWireOffset table target)) }] }

/-- Append the stack action induced by a pop.  Its fresh height wire is the
first gate at the current offset. -/
def TransitionStmtAffineContext.recordPop
    (tm : _root_.Turing.FinTM2)
    (context : TransitionStmtAffineContext tm) (k : tm.K) :
    TransitionStmtAffineContext tm :=
  { context with
      stackActions := context.stackActions ++
        [{ k := k, kind := .pop context.gateOffset }] }

@[simp] theorem TransitionStmtAffineContext.initial_absoluteOffset
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat) :
    (TransitionStmtAffineContext.initial tm).absoluteOffset tm labelOffset =
      labelOffset := by
  cases labelOffset
  simp [TransitionStmtAffineContext.initial,
    TransitionStmtAffineContext.absoluteOffset,
    TransitionAffineNat.add, TransitionAffineNat.shiftInput,
    TransitionAffineNat.const]

@[simp] theorem TransitionStmtAffineContext.initial_stackRoute
    (tm : _root_.Turing.FinTM2) (labelOffset : TransitionAffineNat)
    (k : tm.K) :
    (TransitionStmtAffineContext.initial tm).stackRoute tm labelOffset k =
      TransitionStackAffineRouteSpanBlock.identity := by
  simp [TransitionStmtAffineContext.initial,
    TransitionStmtAffineContext.stackRoute,
    transitionStmtStackActionsFor,
    transitionStmtSelectedStackAffineActionSpans]

/-- The context start form is exactly the current recursive compiler start. -/
theorem TransitionStmtAffineContext.startForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) :
    affineUnaryTripleFormValue
        (context.startForm tm labelOffset)
        (transitionTailAffineSeed seed) =
      (seed.start + labelOffset.eval seed.height) +
        context.gateOffset.eval (workHeight tm seed.height) := by
  rw [TransitionStmtAffineContext.startForm,
    transitionAbsoluteStartForm_value]
  simp [TransitionStmtAffineContext.absoluteOffset, workHeight]
  omega

/-- State forms evaluate to the normalized state layout of the recorded
prefix. -/
theorem TransitionStmtAffineContext.stateForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (target : Fin (stateCount tm)) :
    affineUnaryTripleFormValue
        (context.stateForm tm labelOffset target)
        (transitionTailAffineSeed seed) =
      context.state.wires tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)
        target := by
  cases hstate : context.state with
  | source =>
      simp [TransitionStmtAffineContext.stateForm, hstate,
        TransitionStmtStateLayout.wires,
        transitionWidenedStateForm_value]
  | fixed offsets =>
      simp [TransitionStmtAffineContext.stateForm, hstate,
        TransitionStmtStateLayout.wires,
        transitionAbsoluteStartForm_value, workHeight]
      omega

/-- Replacing the state by a map exposes precisely the current-start output
coordinate of that map. -/
theorem TransitionStmtAffineContext.replaceStateByMap_stateForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    {n : Nat} (table : Fin n → Fin (stateCount tm))
    (target : Fin (stateCount tm)) :
    affineUnaryTripleFormValue
        ((context.replaceStateByMap tm table).stateForm tm labelOffset target)
        (transitionTailAffineSeed seed) =
      affineUnaryTripleFormValue (context.startForm tm labelOffset)
        (transitionTailAffineSeed seed) +
        oneHotMapWireOffset table target := by
  rw [TransitionStmtAffineContext.startForm_value]
  simp only [TransitionStmtAffineContext.replaceStateByMap,
    TransitionStmtAffineContext.stateForm]
  rw [transitionAbsoluteStartForm_value]
  simp only [TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_shiftInput, TransitionAffineNat.eval_const]
  simp only [workHeight]
  omega

/-- The pair-map replacement has the analogous exact coordinate equation. -/
theorem TransitionStmtAffineContext.replaceStateByPairMap_stateForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (pairPrefix : Nat)
    {n p : Nat} (table : Fin n → Fin p → Fin (stateCount tm))
    (target : Fin (stateCount tm)) :
    affineUnaryTripleFormValue
        ((context.replaceStateByPairMap tm pairPrefix table).stateForm tm
          labelOffset target)
        (transitionTailAffineSeed seed) =
      affineUnaryTripleFormValue (context.startForm tm labelOffset)
          (transitionTailAffineSeed seed) + pairPrefix +
        oneHotPairMapWireOffset table target := by
  rw [TransitionStmtAffineContext.startForm_value]
  simp only [TransitionStmtAffineContext.replaceStateByPairMap,
    TransitionStmtAffineContext.stateForm]
  rw [transitionAbsoluteStartForm_value]
  simp only [TransitionAffineNat.eval_add,
    TransitionAffineNat.eval_shiftInput, TransitionAffineNat.eval_const]
  simp only [workHeight]
  omega

end CLRS.Chapter34.Turing.CookLevin
