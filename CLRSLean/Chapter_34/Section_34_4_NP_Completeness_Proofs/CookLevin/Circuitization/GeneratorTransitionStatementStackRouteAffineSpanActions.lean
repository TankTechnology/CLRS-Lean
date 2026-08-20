import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteSpanNormalization

/-!
# Primitive stack actions on compact affine route spans

The affine atom representation is pointwise.  This module compresses the same
shape to one surviving source interval with affine values on either side, and
proves that the compact push/pop rewrites still denote the established
list-valued stack operations.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Compact affine spans for the height and cell-row components of one stack.
-/
@[ext] structure TransitionStackAffineRouteSpanBlock where
  heightSpan : TransitionRouteSpan AffineUnaryTripleForm
  cellSpan : TransitionRouteSpan (List AffineUnaryTripleForm)
deriving DecidableEq, Repr

/-- Identity compact affine route. -/
def TransitionStackAffineRouteSpanBlock.identity :
    TransitionStackAffineRouteSpanBlock :=
  { heightSpan := TransitionRouteSpan.identity
    cellSpan := TransitionRouteSpan.identity }

/-- Evaluate inserted affine forms and route the surviving source interval. -/
def TransitionStackAffineRouteSpanBlock.eval
    (seed : TransitionRowSeed) (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock) :
    TransitionStackValueBlock :=
  { heightValues :=
      (route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).eval source.heightValues
    cellRows :=
      (route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).eval source.cellRows }

@[simp] theorem TransitionStackAffineRouteSpanBlock.eval_identity
    (seed : TransitionRowSeed) (source : TransitionStackValueBlock) :
    TransitionStackAffineRouteSpanBlock.identity.eval seed source = source := by
  apply TransitionStackValueBlock.ext <;>
    simp [TransitionStackAffineRouteSpanBlock.identity,
      TransitionStackAffineRouteSpanBlock.eval,
      TransitionRouteSpan.map, TransitionRouteSpan.identity,
      TransitionRouteSpan.eval, TransitionRouteSpan.middle]

/-- Compact symbolic push: insert the new head values and remove one value or
row from the tail. -/
def TransitionStackAffineRouteSpanBlock.push
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm)
    (route : TransitionStackAffineRouteSpanBlock) :
    TransitionStackAffineRouteSpanBlock :=
  { heightSpan := (route.heightSpan.dropTail 1).prepend falseForm
    cellSpan := (route.cellSpan.dropTail 1).prepend
      (transitionAffinePushedSymbolFormRow
        tm k falseForm symbolForms) }

/-- Compact symbolic pop: remove two height values and one cell row, then
insert the fresh height, false tail, and blank cell row. -/
def TransitionStackAffineRouteSpanBlock.pop
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (falseForm trueForm freshForm : AffineUnaryTripleForm)
    (route : TransitionStackAffineRouteSpanBlock) :
    TransitionStackAffineRouteSpanBlock :=
  { heightSpan :=
      ((route.heightSpan.dropHead 2).prepend freshForm).append falseForm
    cellSpan := (route.cellSpan.dropHead 1).append
      (transitionAffineBlankSymbolFormRow tm k falseForm trueForm) }

/-- Compact affine push agrees with the established fixed-capacity value
transformation. -/
theorem TransitionStackAffineRouteSpanBlock.eval_push
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (height : Nat) (hheight : 0 < height)
    (falseForm : AffineUnaryTripleForm)
    (symbolForms :
      Fin (reachableAlphabet tm k).card → AffineUnaryTripleForm)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock)
    (hheightLength :
      ((route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).eval source.heightValues).length =
        height + 1)
    (hcellLength :
      ((route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).eval source.cellRows).length =
        height)
    (hheightInside : 1 ≤
      (route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).tailValues.length +
      ((route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).middle
            source.heightValues).length)
    (hcellInside : 1 ≤
      (route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).tailValues.length +
      ((route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).middle source.cellRows).length) :
    (route.push tm k falseForm symbolForms).eval seed source =
      (route.eval seed source).push tm k height
        (affineUnaryTripleFormValue falseForm
          (transitionTailAffineSeed seed))
        (fun target => affineUnaryTripleFormValue (symbolForms target)
          (transitionTailAffineSeed seed)) := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hheight)
  apply TransitionStackValueBlock.ext
  · simp only [TransitionStackAffineRouteSpanBlock.push,
      TransitionStackAffineRouteSpanBlock.eval,
      TransitionStackValueBlock.push,
      TransitionRouteSpan.map_prepend, TransitionRouteSpan.map_dropTail,
      TransitionRouteSpan.eval_prepend]
    rw [TransitionRouteSpan.eval_dropTail _ _ _ hheightInside]
    unfold List.rdrop
    rw [hheightLength]
    simp
  · simp only [TransitionStackAffineRouteSpanBlock.push,
      TransitionStackAffineRouteSpanBlock.eval,
      TransitionStackValueBlock.push,
      TransitionRouteSpan.map_prepend, TransitionRouteSpan.map_dropTail,
      TransitionRouteSpan.eval_prepend]
    rw [TransitionRouteSpan.eval_dropTail _ _ _ hcellInside]
    rw [transitionAffinePushedSymbolFormRow_value]
    unfold List.rdrop
    rw [hcellLength]
    simp

/-- Compact affine pop agrees with the established fixed-capacity value
transformation. -/
theorem TransitionStackAffineRouteSpanBlock.eval_pop
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (height : Nat) (hheight : 0 < height)
    (falseForm trueForm freshForm : AffineUnaryTripleForm)
    (source : TransitionStackValueBlock)
    (route : TransitionStackAffineRouteSpanBlock)
    (hheightInside : 2 ≤
      (route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).headValues.length +
      ((route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).middle
            source.heightValues).length)
    (hcellInside : 1 ≤
      (route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).headValues.length +
      ((route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).middle source.cellRows).length) :
    (route.pop tm k falseForm trueForm freshForm).eval seed source =
      (route.eval seed source).pop tm k height
        (affineUnaryTripleFormValue falseForm
          (transitionTailAffineSeed seed))
        (affineUnaryTripleFormValue trueForm
          (transitionTailAffineSeed seed))
        (affineUnaryTripleFormValue freshForm
          (transitionTailAffineSeed seed)) := by
  obtain ⟨previous, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hheight)
  apply TransitionStackValueBlock.ext
  · simp only [TransitionStackAffineRouteSpanBlock.pop,
      TransitionStackAffineRouteSpanBlock.eval,
      TransitionStackValueBlock.pop,
      TransitionRouteSpan.map_append, TransitionRouteSpan.map_prepend,
      TransitionRouteSpan.map_dropHead,
      TransitionRouteSpan.eval_append, TransitionRouteSpan.eval_prepend]
    rw [TransitionRouteSpan.eval_dropHead _ _ _ hheightInside]
  · simp only [TransitionStackAffineRouteSpanBlock.pop,
      TransitionStackAffineRouteSpanBlock.eval,
      TransitionStackValueBlock.pop,
      TransitionRouteSpan.map_append, TransitionRouteSpan.map_dropHead,
      TransitionRouteSpan.eval_append]
    rw [TransitionRouteSpan.eval_dropHead _ _ _ hcellInside]
    rw [transitionAffineBlankSymbolFormRow_value]

end CLRS.Chapter34.Turing.CookLevin
