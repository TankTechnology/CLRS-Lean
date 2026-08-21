import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackSpanFrontBudget

/-!
# Routed-front semantics of affine statement contexts

The compact-span front forms are now reconnected to the typed continuation
configuration.  Under the static public-height padding, positions zero and
one are the real continuation height wires and the routed top row is the real
continuation cell zero.  This removes the last operand hypotheses from the
context-head compiler.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Either of the first two symbolic height forms evaluates to the matching
typed height wire of the continuation stack. -/
theorem TransitionStmtAffineContext.stackHeightFrontForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (position : Nat) (hposition : position < 2)
    (hpadding :
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) :
    affineUnaryTripleFormValue
        (context.stackHeightFrontForm tm labelOffset k position)
        (transitionTailAffineSeed seed) =
      ((context.rowWires tm seed labelOffset).stack k).height
        ⟨position, by
          unfold workHeight
          omega⟩ := by
  let actions := transitionStmtStackActionsFor tm k context.stackActions
  let route := context.stackRoute tm labelOffset k
  let source := TransitionStackValueBlock.ofWires
    ((arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase).stack k)
  have hcapacity : 2 * actions.length + 1 ≤ workHeight tm seed.height := by
    unfold actions workHeight
    omega
  have hfrontTwo :=
    transitionStmtSelectedStackAffineActionSpans_height_front_two tm seed k
      labelOffset actions hcapacity
  have hfrontTwo' :
      2 ≤ route.heightSpan.headValues.length +
        ((route.heightSpan.map fun form =>
          affineUnaryTripleFormValue form
            (transitionTailAffineSeed seed)).middle
          source.heightValues).length := by
    simpa [route, source, actions,
      TransitionStmtAffineContext.stackRoute] using hfrontTwo
  have hfrontPosition : position < route.heightSpan.headValues.length +
      ((route.heightSpan.map fun form =>
        affineUnaryTripleFormValue form
          (transitionTailAffineSeed seed)).middle
        source.heightValues).length := by
    omega
  have hpublic :=
    transitionStmtSelectedStackAffineActionSpans_height_front_public tm seed k
      labelOffset actions position hposition hpadding
  have hvalue :=
    route.heightFrontForm_value tm seed k position hfrontPosition hpublic
  have hroute := context.stackRoute_eval tm seed labelOffset k hcapacity
  rw [hroute] at hvalue
  have htyped : position < workHeight tm seed.height + 1 := by
    unfold workHeight
    omega
  have htyped' :
      position <
        (List.ofFn
          ((context.rowWires tm seed labelOffset).stack k).height).length := by
    simpa using htyped
  rw [show context.stackHeightFrontForm tm labelOffset k position =
      route.heightFrontForm tm k position by rfl]
  rw [hvalue]
  change (List.ofFn ((context.rowWires tm seed labelOffset).stack k).height).getD
      position 0 = _
  rw [List.getD_eq_getElem _ _ htyped', List.getElem_ofFn]

/-- The complete routed top-cell row evaluates to the actual continuation
cell-zero row. -/
theorem TransitionStmtAffineContext.stackCellFrontFormRow_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (hpadding :
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) :
    affineUnaryTripleMap
        ((context.stackRoute tm labelOffset k).cellFrontFormRow tm k 0)
        (transitionTailAffineSeed seed) =
      (TransitionStackValueBlock.ofWires
        ((context.rowWires tm seed labelOffset).stack k)).cellRows.getD 0 [] := by
  let actions := transitionStmtStackActionsFor tm k context.stackActions
  let route := context.stackRoute tm labelOffset k
  let source := TransitionStackValueBlock.ofWires
    ((arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase).stack k)
  have hcapacity : 2 * actions.length + 1 ≤ workHeight tm seed.height := by
    unfold actions workHeight
    omega
  have hfrontOne :=
    transitionStmtSelectedStackAffineActionSpans_cell_front_one tm seed k
      labelOffset actions hcapacity
  have hfrontOne' :
      1 ≤ route.cellSpan.headValues.length +
        ((route.cellSpan.map fun forms =>
          affineUnaryTripleMap forms
            (transitionTailAffineSeed seed)).middle
          source.cellRows).length := by
    simpa [route, source, actions,
      TransitionStmtAffineContext.stackRoute] using hfrontOne
  have hfrontPosition : 0 < route.cellSpan.headValues.length +
      ((route.cellSpan.map fun forms =>
        affineUnaryTripleMap forms
          (transitionTailAffineSeed seed)).middle
        source.cellRows).length := by
    omega
  have hpublic :=
    transitionStmtSelectedStackAffineActionSpans_cell_front_public tm seed k
      labelOffset actions hpadding
  have hvalue :=
    route.cellFrontFormRow_value tm seed k 0 hfrontPosition hpublic
  have hroute := context.stackRoute_eval tm seed labelOffset k hcapacity
  rw [hroute] at hvalue
  rw [show context.stackRoute tm labelOffset k = route by rfl]
  exact hvalue

/-- Each symbolic bit of the routed top cell is the corresponding typed
continuation head bit. -/
theorem TransitionStmtAffineContext.stackCellFrontForm_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (code : Fin ((reachableAlphabet tm k).card + 1))
    (hpadding :
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) :
    affineUnaryTripleFormValue
        (context.stackCellFrontForm tm labelOffset k code)
        (transitionTailAffineSeed seed) =
      arithmeticPeekCfgWires tm (workHeight tm seed.height)
        seed.start (seed.start + 1)
        (context.rowWires tm seed labelOffset) k code := by
  let row := (context.stackRoute tm labelOffset k).cellFrontFormRow tm k 0
  have hrow := context.stackCellFrontFormRow_value tm seed labelOffset k
    hpadding
  have hwork : 0 < workHeight tm seed.height := by
    unfold workHeight
    omega
  rw [arithmeticPeekCfgWires_eq_cell_zero tm
    (workHeight tm seed.height) hwork]
  change affineUnaryTripleFormValue
      (row.getD code.val transitionZeroForm)
      (transitionTailAffineSeed seed) = _
  calc
    _ = (affineUnaryTripleMap row (transitionTailAffineSeed seed)).getD
          code.val 0 := by
      symm
      simpa [affineUnaryTripleMap, transitionZeroForm,
        affineUnaryTripleFormValue] using
        (List.getD_map (l := row) (d := transitionZeroForm)
          (n := code.val) (fun form =>
            affineUnaryTripleFormValue form (transitionTailAffineSeed seed)))
    _ = _ := by
      rw [hrow]
      unfold TransitionStackValueBlock.ofWires transitionStackCellWireRows
      let rows := List.ofFn fun cell : Fin (workHeight tm seed.height) =>
        List.ofFn (((context.rowWires tm seed labelOffset).stack k).cell cell)
      have hzero : 0 < rows.length := by
        simp [rows, hwork]
      have hcode : code.val <
          (List.ofFn
            (((context.rowWires tm seed labelOffset).stack k).cell
              ⟨0, hwork⟩)).length := by
        simpa using code.isLt
      change (rows.getD 0 []).getD code.val 0 = _
      rw [List.getD_eq_getElem rows [] hzero, List.getElem_ofFn]
      rw [List.getD_eq_getElem _ _ hcode, List.getElem_ofFn]

/-- The two symbolic pop operands are exactly the ordinary pop frame of the
continuation stack. -/
theorem TransitionStmtAffineContext.stackHeightFrontFrames_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm) (k : tm.K)
    (hpadding :
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) :
    [(({ left := context.stackHeightFrontForm tm labelOffset k 0
         right := context.stackHeightFrontForm tm labelOffset k 1 } :
        TransitionAffineOrPairForm).eval
          (transitionTailAffineSeed seed))] =
      affinePopFrames (context.rowWires tm seed labelOffset) k := by
  have hwork : 0 < workHeight tm seed.height := by
    unfold workHeight
    omega
  rw [affinePopFrames_eq_single_of_pos hwork]
  congr 2
  apply congrArg₂ AffineOrFinPairFrame.mk
  · exact context.stackHeightFrontForm_value tm seed labelOffset k 0
      (by omega) hpadding
  · have hone := context.stackHeightFrontForm_value tm seed labelOffset k 1
      (by omega) hpadding
    change _ = ((context.rowWires tm seed labelOffset).stack k).height
      ⟨1, by unfold workHeight; omega⟩ at hone
    convert hone using 1
    apply congrArg ((context.rowWires tm seed labelOffset).stack k).height
    apply Fin.ext
    change 1 % (workHeight tm seed.height + 1) = 1
    rw [Nat.mod_eq_of_lt]
    unfold workHeight
    omega

/-- Context-head evaluation with both routed-front obligations discharged by
one per-stack padding hypothesis. -/
theorem transitionStmtContextHeadPhaseForm_eval_of_padding
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (labelOffset : TransitionAffineNat)
    (context : TransitionStmtAffineContext tm)
    (q : _root_.Turing.TM2.Stmt tm.Γ tm.Λ tm.σ)
    (hsupport : ∀ k, stmtPushSet tm q k ⊆ reachableAlphabet tm k)
    (hpadding : ∀ k,
      2 * (transitionStmtStackActionsFor tm k
        context.stackActions).length + 1 ≤ seed.height) :
    Option.map (fun phase => phase.eval (transitionTailAffineSeed seed))
        (transitionStmtContextHeadPhaseForm tm labelOffset context q
          hsupport) =
      transitionStmtHeadPhase tm (workHeight tm seed.height)
        ((seed.start + labelOffset.eval seed.height) +
          context.gateOffset.eval (workHeight tm seed.height))
        seed.start (seed.start + 1)
        (context.rowWires tm seed labelOffset) q hsupport := by
  apply transitionStmtContextHeadPhaseForm_eval tm seed labelOffset context q
    hsupport
  · intro k
    funext code
    exact context.stackCellFrontForm_value tm seed labelOffset k code
      (hpadding k)
  · intro k
    exact context.stackHeightFrontFrames_value tm seed labelOffset k
      (hpadding k)

end CLRS.Chapter34.Turing.CookLevin
