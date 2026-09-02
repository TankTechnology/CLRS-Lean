import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackSourceAffine

/-!
# Affine front views of compact statement-stack spans

The compact stack route retains a verifier-fixed inserted prefix followed by
one interval of the original widened stack.  A subsequent `peek` or `pop`
only reads the first cell row and first two height coordinates.  This module
materializes any such fixed front coordinate as one affine form and proves
the pointwise connection to `TransitionRouteSpan.eval`.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Symbolic value at a fixed front position.  If the inserted prefix has
already supplied the position, use it; otherwise address the surviving
original-source interval. -/
def TransitionRouteSpan.frontForm (span : TransitionRouteSpan α)
    (sourceForm : Nat → α) (position : Nat) : α :=
  if h : position < span.headValues.length then
    span.headValues[position]
  else
    sourceForm (span.sourceDrop + (position - span.headValues.length))

/-- Evaluating a front form agrees with pointwise evaluation of the compact
span whenever the requested position lies before the inserted suffix. -/
theorem TransitionRouteSpan.frontForm_value
    (span : TransitionRouteSpan α) (sourceForm : Nat → α)
    (value : α → β) (source : List β) (fallback : β) (position : Nat)
    (hposition : position < span.headValues.length +
      ((span.map value).middle source).length)
    (hsourceIndex :
      span.sourceDrop + (position - span.headValues.length) < source.length)
    (hsource :
      value (sourceForm
        (span.sourceDrop + (position - span.headValues.length))) =
      source[span.sourceDrop + (position - span.headValues.length)]) :
    value (span.frontForm sourceForm position) =
      ((span.map value).eval source).getD position fallback := by
  unfold TransitionRouteSpan.frontForm
  split_ifs with hhead
  · have hhead' : position < (span.map value).headValues.length := by
      simpa [TransitionRouteSpan.map] using hhead
    rw [TransitionRouteSpan.eval, List.append_assoc]
    rw [List.getD_append _ _ _ _ hhead']
    rw [List.getD_eq_getElem _ _ hhead']
    simp [TransitionRouteSpan.map]
  · rw [TransitionRouteSpan.eval, List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (by
      simpa [TransitionRouteSpan.map] using Nat.le_of_not_gt hhead)]
    have hmiddle : position - span.headValues.length <
        ((span.map value).middle source).length := by omega
    rw [show (span.map value).headValues.length =
        span.headValues.length by simp [TransitionRouteSpan.map]]
    rw [List.getD_append _ _ _ _ hmiddle]
    rw [List.getD_eq_getElem _ _ hmiddle]
    unfold TransitionRouteSpan.middle List.rdrop
    rw [List.getElem_take, List.getElem_drop]
    exact hsource

/-! ## Widened-source front forms -/

/-- Affine row of all symbol coordinates in one fixed public stack cell. -/
noncomputable def transitionWidenedStackCellFormRow
    (tm : _root_.Turing.FinTM2) (k : tm.K) (cell : Nat) :
    List AffineUnaryTripleForm :=
  List.ofFn (transitionWidenedStackCellForm tm k cell)

/-- Affine form selected at one front height position of a compact route. -/
noncomputable def TransitionStackAffineRouteSpanBlock.heightFrontForm
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) (position : Nat) :
    AffineUnaryTripleForm :=
  route.heightSpan.frontForm
    (transitionWidenedStackHeightForm tm k) position

/-- Affine symbol row selected at one front cell position of a compact route.
-/
noncomputable def TransitionStackAffineRouteSpanBlock.cellFrontFormRow
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) (position : Nat) :
    List AffineUnaryTripleForm :=
  route.cellSpan.frontForm
    (transitionWidenedStackCellFormRow tm k) position

/-- Evaluation of a routed height-front form is the corresponding wire in the
compact route's list semantics. -/
theorem TransitionStackAffineRouteSpanBlock.heightFrontForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) (position : Nat)
    (hposition : position < route.heightSpan.headValues.length +
      ((route.heightSpan.map fun form =>
          affineUnaryTripleFormValue form
            (transitionTailAffineSeed seed)).middle
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k)).heightValues).length)
    (hpublic : route.heightSpan.sourceDrop +
        (position - route.heightSpan.headValues.length) < seed.height + 1) :
    affineUnaryTripleFormValue
        (route.heightFrontForm tm k position)
        (transitionTailAffineSeed seed) =
      (route.eval seed
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k))).heightValues.getD position 0 := by
  apply route.heightSpan.frontForm_value
      (transitionWidenedStackHeightForm tm k)
      (fun form => affineUnaryTripleFormValue form
        (transitionTailAffineSeed seed)) _ 0 position hposition
  case hsourceIndex =>
    have hindex : route.heightSpan.sourceDrop +
        (position - route.heightSpan.headValues.length) <
        workHeight tm seed.height + 1 := by
      unfold workHeight
      omega
    simpa [TransitionStackValueBlock.ofWires,
      transitionStackHeightWireValues] using hindex
  case hsource =>
    let index := route.heightSpan.sourceDrop +
      (position - route.heightSpan.headValues.length)
    have hindex : index < workHeight tm seed.height + 1 := by
      unfold index workHeight
      omega
    rw [transitionWidenedStackHeightForm_value tm seed k
      ⟨index, hindex⟩ hpublic]
    change
      ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k).height ⟨index, hindex⟩ =
      (List.ofFn ((arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase).stack k).height)[index]'(by simpa using hindex)
    rw [List.getElem_ofFn]

/-- Evaluation of a routed cell-front row is the exact one-hot wire row in
the compact route's list semantics. -/
theorem TransitionStackAffineRouteSpanBlock.cellFrontFormRow_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (route : TransitionStackAffineRouteSpanBlock) (position : Nat)
    (hposition : position < route.cellSpan.headValues.length +
      ((route.cellSpan.map fun forms =>
          affineUnaryTripleMap forms
            (transitionTailAffineSeed seed)).middle
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k)).cellRows).length)
    (hpublic : route.cellSpan.sourceDrop +
        (position - route.cellSpan.headValues.length) < seed.height) :
    affineUnaryTripleMap (route.cellFrontFormRow tm k position)
        (transitionTailAffineSeed seed) =
      (route.eval seed
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k))).cellRows.getD position [] := by
  apply route.cellSpan.frontForm_value
      (transitionWidenedStackCellFormRow tm k)
      (fun forms => affineUnaryTripleMap forms
        (transitionTailAffineSeed seed)) _ [] position hposition
  case hsourceIndex =>
    have hindex : route.cellSpan.sourceDrop +
        (position - route.cellSpan.headValues.length) <
        workHeight tm seed.height := by
      unfold workHeight
      omega
    simpa [TransitionStackValueBlock.ofWires,
      transitionStackCellWireRows] using hindex
  case hsource =>
    let index := route.cellSpan.sourceDrop +
      (position - route.cellSpan.headValues.length)
    have hindex : index < workHeight tm seed.height := by
      unfold index workHeight
      omega
    unfold transitionWidenedStackCellFormRow affineUnaryTripleMap
    rw [List.map_ofFn]
    change List.ofFn _ =
      (List.ofFn fun cell : Fin (workHeight tm seed.height) =>
        List.ofFn
          (((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k).cell cell))[index]'(by simpa using hindex)
    rw [List.getElem_ofFn]
    apply List.ofFn_inj.mpr
    funext code
    simp only [Function.comp_apply]
    rw [transitionWidenedStackCellForm_value tm seed k
      index code hpublic]
    rfl

end CLRS.Chapter34.Turing.CookLevin
