import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValueRouting

/-!
# Static atoms for sequential statement stack routing

A terminal statement may update the same stack more than once.  Running each
primitive compiler from the original tableau row is therefore insufficient:
later actions must observe earlier actions.  This module removes that dynamic
dependency.  Every final coordinate is first normalized to either a reference
to the original stack or a constant wire/row.  Interpreting the normalized
atoms once is proved equal to the original sequential push/pop fold.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- One statically routed output coordinate: either read an original source
coordinate or emit a constant value. -/
inductive TransitionRouteAtom (α : Type)
  | source (index : Nat)
  | const (value : α)
deriving DecidableEq, Repr

/-- Interpret one route atom.  The fallback is irrelevant for atoms produced
from a source list, because all such indices are in range. -/
def TransitionRouteAtom.eval (fallback : α) (source : List α) :
    TransitionRouteAtom α → α
  | .source index => source.getD index fallback
  | .const value => value

/-- Pointwise interpretation of a static route. -/
def transitionRouteAtomsEval (fallback : α) (source : List α)
    (atoms : List (TransitionRouteAtom α)) : List α :=
  atoms.map (TransitionRouteAtom.eval fallback source)

/-- Identity route over every coordinate of `source`. -/
def transitionRouteSourceAtoms (source : List α) :
    List (TransitionRouteAtom α) :=
  (List.range source.length).map TransitionRouteAtom.source

/-- Interpreting the identity route recovers the exact source list. -/
@[simp] theorem transitionRouteAtomsEval_source
    (fallback : α) (source : List α) :
    transitionRouteAtomsEval fallback source
      (transitionRouteSourceAtoms source) = source := by
  apply List.ext_get
  · simp [transitionRouteAtomsEval, transitionRouteSourceAtoms]
  · intro index hleft hright
    simp [transitionRouteAtomsEval, transitionRouteSourceAtoms,
      TransitionRouteAtom.eval, List.getD_eq_getElem?_getD, hright]

/-- Static route atoms for both components of one stack block. -/
@[ext] structure TransitionStackRouteAtomBlock where
  heightAtoms : List (TransitionRouteAtom Nat)
  cellAtoms : List (TransitionRouteAtom (List Nat))
deriving DecidableEq, Repr

/-- Identity atom block for one concrete source block. -/
def TransitionStackRouteAtomBlock.ofSource
    (source : TransitionStackValueBlock) : TransitionStackRouteAtomBlock :=
  { heightAtoms := transitionRouteSourceAtoms source.heightValues
    cellAtoms := transitionRouteSourceAtoms source.cellRows }

/-- Interpret a static atom block against the original stack block. -/
def TransitionStackRouteAtomBlock.eval
    (source : TransitionStackValueBlock)
    (route : TransitionStackRouteAtomBlock) : TransitionStackValueBlock :=
  { heightValues :=
      transitionRouteAtomsEval 0 source.heightValues route.heightAtoms
    cellRows :=
      transitionRouteAtomsEval [] source.cellRows route.cellAtoms }

/-- The identity atom block denotes its source exactly. -/
@[simp] theorem TransitionStackRouteAtomBlock.ofSource_eval
    (source : TransitionStackValueBlock) :
    (TransitionStackRouteAtomBlock.ofSource source).eval source = source := by
  apply TransitionStackValueBlock.ext <;>
    simp [TransitionStackRouteAtomBlock.eval,
      TransitionStackRouteAtomBlock.ofSource]

/-- Static atom transformation corresponding to one fixed-capacity push. -/
def TransitionStackRouteAtomBlock.push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire : Nat) (symbol : SymbolWires tm k)
    (route : TransitionStackRouteAtomBlock) :
    TransitionStackRouteAtomBlock :=
  match height with
  | 0 =>
      { heightAtoms := [.const falseWire]
        cellAtoms := [] }
  | previous + 1 =>
      { heightAtoms :=
          .const falseWire :: route.heightAtoms.take (previous + 1)
        cellAtoms :=
          .const (transitionPushedSymbolWireRow tm k falseWire symbol) ::
            route.cellAtoms.take previous }

/-- Static atom transformation corresponding to one fixed-capacity pop. -/
def TransitionStackRouteAtomBlock.pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire trueWire start : Nat)
    (route : TransitionStackRouteAtomBlock) :
    TransitionStackRouteAtomBlock :=
  match height with
  | 0 => route
  | _ + 1 =>
      { heightAtoms :=
          .const start :: route.heightAtoms.drop 2 ++ [.const falseWire]
        cellAtoms := route.cellAtoms.drop 1 ++
          [.const (transitionBlankSymbolWireRow tm k falseWire trueWire)] }

/-- Static push normalization commutes with interpreting route atoms. -/
theorem TransitionStackRouteAtomBlock.eval_push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire : Nat) (symbol : SymbolWires tm k)
    (source : TransitionStackValueBlock)
    (route : TransitionStackRouteAtomBlock) :
    (route.push tm k height falseWire symbol).eval source =
      (route.eval source).push tm k height falseWire symbol := by
  cases height with
  | zero =>
      apply TransitionStackValueBlock.ext <;>
        simp [TransitionStackRouteAtomBlock.push,
          TransitionStackRouteAtomBlock.eval,
          TransitionStackValueBlock.push, transitionRouteAtomsEval,
          TransitionRouteAtom.eval]
  | succ height =>
      apply TransitionStackValueBlock.ext <;>
        simp [TransitionStackRouteAtomBlock.push,
          TransitionStackRouteAtomBlock.eval,
          TransitionStackValueBlock.push, transitionRouteAtomsEval,
          TransitionRouteAtom.eval]

/-- Static pop normalization commutes with interpreting route atoms. -/
theorem TransitionStackRouteAtomBlock.eval_pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (height falseWire trueWire start : Nat)
    (source : TransitionStackValueBlock)
    (route : TransitionStackRouteAtomBlock) :
    (route.pop tm k height falseWire trueWire start).eval source =
      (route.eval source).pop tm k height falseWire trueWire start := by
  cases height with
  | zero => rfl
  | succ height =>
      apply TransitionStackValueBlock.ext <;>
        simp [TransitionStackRouteAtomBlock.pop,
          TransitionStackRouteAtomBlock.eval,
          TransitionStackValueBlock.pop, transitionRouteAtomsEval,
          TransitionRouteAtom.eval, List.map_append]

/-- Apply one selected statement action to static route atoms. -/
def TransitionStmtSelectedStackAction.evalAtoms
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (route : TransitionStackRouteAtomBlock) :
    TransitionStmtSelectedStackAction tm k → TransitionStackRouteAtomBlock
  | .push symbolOffsets =>
      route.push tm k height falseWire
        (fun target => originStart + (symbolOffsets target).eval height)
  | .pop heightWireOffset =>
      route.pop tm k height falseWire trueWire
        (originStart + heightWireOffset.eval height)

/-- Interpreting one normalized action agrees with its list-valued semantics. -/
theorem TransitionStmtSelectedStackAction.evalAtoms_eval
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock)
    (route : TransitionStackRouteAtomBlock)
    (action : TransitionStmtSelectedStackAction tm k) :
    (action.evalAtoms tm k originStart height falseWire trueWire route).eval
        source =
      action.evalValues tm k originStart height falseWire trueWire
        (route.eval source) := by
  cases action with
  | push symbolOffsets =>
      exact route.eval_push tm k height falseWire _ source
  | pop heightWireOffset =>
      exact route.eval_pop tm k height falseWire trueWire _ source

/-- Sequential normalization of a selected stack's complete action table. -/
def transitionStmtSelectedStackActionAtoms
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (route : TransitionStackRouteAtomBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    TransitionStackRouteAtomBlock :=
  actions.foldl
    (fun current action =>
      action.evalAtoms tm k originStart height falseWire trueWire current)
    route

/-- The complete normalized action fold denotes exactly the original
sequential list-valued stack transformation. -/
theorem transitionStmtSelectedStackActionAtoms_eval_from
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock)
    (route : TransitionStackRouteAtomBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackActionAtoms tm k originStart height falseWire
        trueWire route actions).eval source =
      transitionStmtSelectedStackActionValues_eval tm k originStart height
        falseWire trueWire (route.eval source) actions := by
  induction actions generalizing route with
  | nil => rfl
  | cons action rest ih =>
      change (transitionStmtSelectedStackActionAtoms tm k originStart height
          falseWire trueWire
          (action.evalAtoms tm k originStart height falseWire trueWire route)
          rest).eval source = _
      rw [ih]
      rw [action.evalAtoms_eval tm k originStart height falseWire trueWire
        source route]
      rfl

/-- Starting from the identity atoms, the normalized action table evaluates
to the exact selected-stack semantic fold. -/
theorem transitionStmtSelectedStackActionAtoms_eval
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart height falseWire trueWire : Nat)
    (source : TransitionStackValueBlock)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    (transitionStmtSelectedStackActionAtoms tm k originStart height falseWire
        trueWire (TransitionStackRouteAtomBlock.ofSource source) actions).eval
        source =
      transitionStmtSelectedStackActionValues_eval tm k originStart height
        falseWire trueWire source actions := by
  rw [transitionStmtSelectedStackActionAtoms_eval_from]
  rw [TransitionStackRouteAtomBlock.ofSource_eval]

end CLRS.Chapter34.Turing.CookLevin
