import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteRowSlices

/-!
# Descriptor routes for primitive stack-cell actions

This module connects the affine cell source to the ordinary list semantics of
one fixed-capacity push or pop.  The descriptor route inserts or removes one
whole machine-fixed symbol row, including the zero-capacity identity cases.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Descriptor-only cell route for push.  At positive capacity it inserts the
new top symbol row and removes one old bottom row. -/
noncomputable def transitionStackRoutePushCellValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (symbol : SymbolWires tm k) : List Nat :=
  match workHeight tm seed.height with
  | 0 => []
  | _ + 1 =>
      transitionPushedSymbolWireRow tm k seed.start symbol ++
        transitionStackRouteFirstValues
          (transitionStackRouteTrimSuffix
            ((reachableAlphabet tm k).card + 1)
            (transitionStackRouteCellProgressions tm seed k))

/-- Descriptor-only cell route for pop.  At positive capacity it removes the
old top symbol row and appends one fixed blank row. -/
noncomputable def transitionStackRoutePopCellValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    List Nat :=
  match workHeight tm seed.height with
  | 0 => transitionStackRouteFirstValues
      (transitionStackRouteCellProgressions tm seed k)
  | _ + 1 =>
      transitionStackRouteFirstValues
          (transitionStackRouteDropFamily
            ((reachableAlphabet tm k).card + 1)
            (transitionStackRouteCellProgressions tm seed k)) ++
        transitionBlankSymbolWireRow tm k seed.start (seed.start + 1)

/-- The descriptor push route is exactly the flattened cell component of the
real list-valued stack push. -/
theorem transitionStackRoutePushCellValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (symbol : SymbolWires tm k) :
    transitionStackRoutePushCellValues tm seed k symbol =
      ((TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).push tm k (workHeight tm seed.height)
            seed.start symbol).cellRows.flatten := by
  have hshape := TransitionStackValueBlock.hasShape_ofWires tm k
    (workHeight tm seed.height)
    ((arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).stack k)
  rcases hshape with ⟨_, hcells, hrows⟩
  unfold transitionStackRoutePushCellValues
  by_cases hzero : workHeight tm seed.height = 0
  · simp [hzero, TransitionStackValueBlock.push]
  · obtain ⟨height, hheight⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    simp only [hheight, TransitionStackValueBlock.push, List.flatten_cons]
    rw [transitionStackRouteFirstValues_trimSuffix]
    rw [← transitionWidenedStackCellValues_eq_routeSource]
    rw [List.flatten_rdrop_one_fixedWidth _ height
      ((reachableAlphabet tm k).card + 1) (by simpa [hheight] using hcells)
      hrows]

/-- The descriptor pop route is exactly the flattened cell component of the
real list-valued stack pop. -/
theorem transitionStackRoutePopCellValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRoutePopCellValues tm seed k =
      ((TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).pop tm k (workHeight tm seed.height)
            seed.start (seed.start + 1) seed.start).cellRows.flatten := by
  have hshape := TransitionStackValueBlock.hasShape_ofWires tm k
    (workHeight tm seed.height)
    ((arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).stack k)
  rcases hshape with ⟨_, hcells, hrows⟩
  unfold transitionStackRoutePopCellValues
  by_cases hzero : workHeight tm seed.height = 0
  · simp only [hzero, TransitionStackValueBlock.pop]
    exact (transitionWidenedStackCellValues_eq_routeSource tm seed k).symm
  · obtain ⟨height, hheight⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    simp only [hheight, TransitionStackValueBlock.pop]
    rw [transitionStackRouteFirstValues_drop]
    rw [← transitionWidenedStackCellValues_eq_routeSource]
    have hdrop :
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k)).cellRows.flatten.drop
              ((reachableAlphabet tm k).card + 1) =
          ((TransitionStackValueBlock.ofWires
            ((arithmeticWidenedCfgWires tm seed.height seed.start
              seed.rowBase).stack k)).cellRows.drop 1).flatten := by
      simpa using List.flatten_drop_fixedWidth
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k)).cellRows 1
        ((reachableAlphabet tm k).card + 1) (by
          rw [hcells, hheight]
          omega) hrows
    rw [hdrop]
    simp

end CLRS.Chapter34.Turing.CookLevin
