import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteAtomNormalization
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePushAffine

/-!
# Affine atoms for sequential statement stack routing

The static route normal form identifies every final coordinate with either an
original source position or a newly written wire.  This module keeps the new
wires symbolic as verifier-fixed affine forms.  Evaluating those forms at one
transition-row seed is proved to commute with every push, pop, and complete
selected-action fold.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Evaluate the constant payload of one affine route atom. -/
def transitionAffineRouteAtomEval (seed : TransitionRowSeed) :
    TransitionRouteAtom AffineUnaryTripleForm → TransitionRouteAtom Nat
  | .source index => .source index
  | .const form =>
      .const (affineUnaryTripleFormValue form (transitionTailAffineSeed seed))

/-- Evaluate every affine form in one constant cell-row atom. -/
def transitionAffineRouteRowAtomEval (seed : TransitionRowSeed) :
    TransitionRouteAtom (List AffineUnaryTripleForm) →
      TransitionRouteAtom (List Nat)
  | .source index => .source index
  | .const forms =>
      .const (affineUnaryTripleMap forms (transitionTailAffineSeed seed))

/-- Symbolic affine route atoms for both components of one stack block. -/
@[ext] structure TransitionStackAffineRouteAtomBlock where
  heightAtoms : List (TransitionRouteAtom AffineUnaryTripleForm)
  cellAtoms : List (TransitionRouteAtom (List AffineUnaryTripleForm))
deriving DecidableEq, Repr

/-- Identity affine atoms for a concrete source shape. -/
def TransitionStackAffineRouteAtomBlock.ofSource
    (source : TransitionStackValueBlock) :
    TransitionStackAffineRouteAtomBlock :=
  { heightAtoms := (List.range source.heightValues.length).map
      (TransitionRouteAtom.source (α := AffineUnaryTripleForm))
    cellAtoms := (List.range source.cellRows.length).map
      (TransitionRouteAtom.source (α := List AffineUnaryTripleForm)) }

/-- Evaluate symbolic constants while retaining original-source references. -/
def TransitionStackAffineRouteAtomBlock.eval
    (seed : TransitionRowSeed)
    (route : TransitionStackAffineRouteAtomBlock) :
    TransitionStackRouteAtomBlock :=
  { heightAtoms := route.heightAtoms.map (transitionAffineRouteAtomEval seed)
    cellAtoms := route.cellAtoms.map (transitionAffineRouteRowAtomEval seed) }

/-- Evaluating identity affine atoms gives the ordinary identity route. -/
@[simp] theorem TransitionStackAffineRouteAtomBlock.ofSource_eval
    (seed : TransitionRowSeed) (source : TransitionStackValueBlock) :
    (TransitionStackAffineRouteAtomBlock.ofSource source).eval seed =
      TransitionStackRouteAtomBlock.ofSource source := by
  apply TransitionStackRouteAtomBlock.ext <;>
    simp [TransitionStackAffineRouteAtomBlock.eval,
      TransitionStackAffineRouteAtomBlock.ofSource,
      TransitionStackRouteAtomBlock.ofSource,
      transitionRouteSourceAtoms, transitionAffineRouteAtomEval,
      transitionAffineRouteRowAtomEval]

/-- Symbolic one-hot row inserted by a push. -/
def transitionAffinePushedSymbolFormRow
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm) :
    List AffineUnaryTripleForm :=
  List.ofFn fun code : Fin ((reachableAlphabet tm k).card + 1) =>
    if h : code.val < (reachableAlphabet tm k).card then
      symbolForms ⟨code.val, h⟩
    else falseForm

/-- Evaluating a symbolic pushed row gives the established wire row. -/
theorem transitionAffinePushedSymbolFormRow_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm) :
    affineUnaryTripleMap
        (transitionAffinePushedSymbolFormRow tm k falseForm symbolForms)
        (transitionTailAffineSeed seed) =
      transitionPushedSymbolWireRow tm k
        (affineUnaryTripleFormValue falseForm (transitionTailAffineSeed seed))
        (fun target => affineUnaryTripleFormValue (symbolForms target)
          (transitionTailAffineSeed seed)) := by
  unfold affineUnaryTripleMap transitionAffinePushedSymbolFormRow
    transitionPushedSymbolWireRow
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext code
  simp only [Function.comp_apply]
  split_ifs <;> rfl

/-- Symbolic blank row appended by a pop. -/
def transitionAffineBlankSymbolFormRow
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseForm trueForm : AffineUnaryTripleForm) :
    List AffineUnaryTripleForm :=
  List.ofFn fun code : Fin ((reachableAlphabet tm k).card + 1) =>
    if code = encodeHeadCode none then trueForm else falseForm

/-- Evaluating a symbolic blank row gives the established blank-wire row. -/
theorem transitionAffineBlankSymbolFormRow_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (falseForm trueForm : AffineUnaryTripleForm) :
    affineUnaryTripleMap
        (transitionAffineBlankSymbolFormRow tm k falseForm trueForm)
        (transitionTailAffineSeed seed) =
      transitionBlankSymbolWireRow tm k
        (affineUnaryTripleFormValue falseForm (transitionTailAffineSeed seed))
        (affineUnaryTripleFormValue trueForm
          (transitionTailAffineSeed seed)) := by
  unfold affineUnaryTripleMap transitionAffineBlankSymbolFormRow
    transitionBlankSymbolWireRow arithmeticBlankHeadWires
  rw [List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext code
  simp only [Function.comp_apply]
  split_ifs <;> rfl

/-- Symbolic affine transformation corresponding to one fixed-capacity push.
-/
def TransitionStackAffineRouteAtomBlock.push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height : Nat) (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm)
    (route : TransitionStackAffineRouteAtomBlock) :
    TransitionStackAffineRouteAtomBlock :=
  match height with
  | 0 =>
      { heightAtoms := [.const falseForm]
        cellAtoms := [] }
  | previous + 1 =>
      { heightAtoms :=
          .const falseForm :: route.heightAtoms.take (previous + 1)
        cellAtoms :=
          .const (transitionAffinePushedSymbolFormRow
            tm k falseForm symbolForms) :: route.cellAtoms.take previous }

/-- Symbolic affine transformation corresponding to one fixed-capacity pop.
-/
def TransitionStackAffineRouteAtomBlock.pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height : Nat) (falseForm trueForm freshForm : AffineUnaryTripleForm)
    (route : TransitionStackAffineRouteAtomBlock) :
    TransitionStackAffineRouteAtomBlock :=
  match height with
  | 0 => route
  | _ + 1 =>
      { heightAtoms :=
          .const freshForm :: route.heightAtoms.drop 2 ++ [.const falseForm]
        cellAtoms := route.cellAtoms.drop 1 ++
          [.const (transitionAffineBlankSymbolFormRow
            tm k falseForm trueForm)] }

/-- Affine push normalization commutes with runtime seed evaluation. -/
theorem TransitionStackAffineRouteAtomBlock.eval_push
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (height : Nat) (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm)
    (route : TransitionStackAffineRouteAtomBlock) :
    (route.push tm k height falseForm symbolForms).eval seed =
      (route.eval seed).push tm k height
        (affineUnaryTripleFormValue falseForm (transitionTailAffineSeed seed))
        (fun target => affineUnaryTripleFormValue (symbolForms target)
          (transitionTailAffineSeed seed)) := by
  cases height with
  | zero =>
      apply TransitionStackRouteAtomBlock.ext <;>
        simp [TransitionStackAffineRouteAtomBlock.push,
          TransitionStackAffineRouteAtomBlock.eval,
          TransitionStackRouteAtomBlock.push,
          transitionAffineRouteAtomEval]
  | succ height =>
      apply TransitionStackRouteAtomBlock.ext
      · simp [TransitionStackAffineRouteAtomBlock.push,
          TransitionStackAffineRouteAtomBlock.eval,
          TransitionStackRouteAtomBlock.push,
          transitionAffineRouteAtomEval]
      · simp [TransitionStackAffineRouteAtomBlock.push,
          TransitionStackAffineRouteAtomBlock.eval,
          TransitionStackRouteAtomBlock.push,
          transitionAffineRouteRowAtomEval,
          transitionAffinePushedSymbolFormRow_value]

/-- Affine pop normalization commutes with runtime seed evaluation. -/
theorem TransitionStackAffineRouteAtomBlock.eval_pop
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (height : Nat) (falseForm trueForm freshForm : AffineUnaryTripleForm)
    (route : TransitionStackAffineRouteAtomBlock) :
    (route.pop tm k height falseForm trueForm freshForm).eval seed =
      (route.eval seed).pop tm k height
        (affineUnaryTripleFormValue falseForm (transitionTailAffineSeed seed))
        (affineUnaryTripleFormValue trueForm (transitionTailAffineSeed seed))
        (affineUnaryTripleFormValue freshForm
          (transitionTailAffineSeed seed)) := by
  cases height with
  | zero => rfl
  | succ height =>
      apply TransitionStackRouteAtomBlock.ext
      · simp [TransitionStackAffineRouteAtomBlock.pop,
          TransitionStackAffineRouteAtomBlock.eval,
          TransitionStackRouteAtomBlock.pop,
          transitionAffineRouteAtomEval]
      · simp [TransitionStackAffineRouteAtomBlock.pop,
          TransitionStackAffineRouteAtomBlock.eval,
          TransitionStackRouteAtomBlock.pop,
          transitionAffineRouteRowAtomEval,
          transitionAffineBlankSymbolFormRow_value, List.map_append]

/-- Runtime-height specialization of one affine selected action. -/
def TransitionStmtSelectedStackAction.evalAffineAtomsAtHeight
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat) (height : Nat)
    (route : TransitionStackAffineRouteAtomBlock) :
    TransitionStmtSelectedStackAction tm k →
      TransitionStackAffineRouteAtomBlock
  | .push symbolOffsets =>
      route.push tm k height
        (transitionAbsoluteStartForm (TransitionAffineNat.const 0))
        (fun target => transitionAbsoluteStartForm
          (labelOffset.add
            ((symbolOffsets target).shiftInput (maxPushesPerStep tm))))
  | .pop heightWireOffset =>
      route.pop tm k height
        (transitionAbsoluteStartForm (TransitionAffineNat.const 0))
        (transitionAbsoluteStartForm (TransitionAffineNat.const 1))
        (transitionAbsoluteStartForm
          (labelOffset.add
            (heightWireOffset.shiftInput (maxPushesPerStep tm))))

/-- Evaluating one affine selected action gives its ordinary static action at
the runtime workspace height. -/
theorem TransitionStmtSelectedStackAction.evalAffineAtomsAtHeight_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteAtomBlock)
    (action : TransitionStmtSelectedStackAction tm k) :
    (action.evalAffineAtomsAtHeight tm k labelOffset
        (workHeight tm seed.height) route).eval seed =
      action.evalAtoms tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (route.eval seed) := by
  cases action with
  | push symbolOffsets =>
      simp only [TransitionStmtSelectedStackAction.evalAffineAtomsAtHeight,
        TransitionStmtSelectedStackAction.evalAtoms]
      rw [TransitionStackAffineRouteAtomBlock.eval_push]
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
      simp only [TransitionStmtSelectedStackAction.evalAffineAtomsAtHeight,
        TransitionStmtSelectedStackAction.evalAtoms]
      rw [TransitionStackAffineRouteAtomBlock.eval_pop]
      rw [transitionAbsoluteStartForm_value,
        transitionAbsoluteStartForm_value,
        transitionAbsoluteStartForm_value,
        TransitionAffineNat.eval_add,
        TransitionAffineNat.eval_shiftInput]
      simp [workHeight, Nat.add_assoc]

/-- Complete symbolic affine normalization of one selected stack's actions. -/
def transitionStmtSelectedStackAffineActionAtoms
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (labelOffset : TransitionAffineNat) (height : Nat)
    (route : TransitionStackAffineRouteAtomBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    TransitionStackAffineRouteAtomBlock :=
  actions.foldl
    (fun current action =>
      action.evalAffineAtomsAtHeight tm k labelOffset height current)
    route

/-- Evaluating the complete affine fold recovers the established static atom
normal form for the same action sequence. -/
theorem transitionStmtSelectedStackAffineActionAtoms_eval_from
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (route : TransitionStackAffineRouteAtomBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionAtoms tm k labelOffset
        (workHeight tm seed.height) route actions).eval seed =
      transitionStmtSelectedStackActionAtoms tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (route.eval seed) actions := by
  induction actions generalizing route with
  | nil => rfl
  | cons action rest ih =>
      change (transitionStmtSelectedStackAffineActionAtoms tm k labelOffset
          (workHeight tm seed.height)
          (action.evalAffineAtomsAtHeight tm k labelOffset
            (workHeight tm seed.height) route) rest).eval seed = _
      rw [ih]
      rw [action.evalAffineAtomsAtHeight_eval tm seed k labelOffset route]
      rfl

/-- Starting from the identity affine route, symbolic normalization evaluates
to the complete ordinary static route. -/
theorem transitionStmtSelectedStackAffineActionAtoms_eval
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (source : TransitionStackValueBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackAffineActionAtoms tm k labelOffset
        (workHeight tm seed.height)
        (TransitionStackAffineRouteAtomBlock.ofSource source) actions).eval
        seed =
      transitionStmtSelectedStackActionAtoms tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (TransitionStackRouteAtomBlock.ofSource source) actions := by
  rw [transitionStmtSelectedStackAffineActionAtoms_eval_from]
  rw [TransitionStackAffineRouteAtomBlock.ofSource_eval]

/-- Interpreting the evaluated affine atoms against their original source
recovers the complete sequential stack-action value semantics. -/
theorem transitionStmtSelectedStackAffineActionAtoms_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (labelOffset : TransitionAffineNat)
    (source : TransitionStackValueBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    ((transitionStmtSelectedStackAffineActionAtoms tm k labelOffset
        (workHeight tm seed.height)
        (TransitionStackAffineRouteAtomBlock.ofSource source) actions).eval
        seed).eval source =
      transitionStmtSelectedStackActionValues_eval tm k
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        source actions := by
  rw [transitionStmtSelectedStackAffineActionAtoms_eval]
  exact transitionStmtSelectedStackActionAtoms_eval tm k
    (seed.start + labelOffset.eval seed.height)
    (workHeight tm seed.height) seed.start (seed.start + 1) source actions

end CLRS.Chapter34.Turing.CookLevin
