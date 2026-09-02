import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRoutePrimitive

/-!
# Sequential selected-stack routes

A terminal statement may touch the same stack more than once.  This module
reconstructs the grouped widened source block from the already verified affine
height stream and the closed cell-row formulas, then runs the complete fixed
action subsequence on that source.  It closes the semantic fold boundary; a
later module must still implement the corresponding descriptor rewrite by a
concrete fixed controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Grouped cell-row view underlying the flattened affine cell source. -/
noncomputable def transitionStackRouteCellRows
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    List (List Nat) :=
  List.ofFn fun cell : Fin (workHeight tm seed.height) =>
    List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
      if _h : cell.val < seed.height then
        seed.rowBase +
          (transitionEqPrefixWidth tm +
            cfgStackBitOffset tm seed.height k + (seed.height + 1) +
              (symbol.val +
                ((reachableAlphabet tm k).card + 1) * cell.val))
      else if symbol.val = (reachableAlphabet tm k).card then
        seed.start + 1
      else seed.start

/-- Complete grouped route source reconstructed from the affine height stream
and fixed-width cell rows. -/
noncomputable def transitionStackRouteSourceBlock
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    TransitionStackValueBlock :=
  { heightValues := transitionStackRouteFirstValues
      (transitionStackRouteHeightProgressions tm seed k)
    cellRows := transitionStackRouteCellRows tm seed k }

/-- The reconstructed route source is literally the real widened stack block.
-/
theorem transitionStackRouteSourceBlock_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K) :
    transitionStackRouteSourceBlock tm seed k =
      TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k) := by
  apply TransitionStackValueBlock.ext
  · exact (transitionWidenedStackHeightValues_eq_routeSource tm seed k).symm
  · unfold transitionStackRouteSourceBlock transitionStackRouteCellRows
      TransitionStackValueBlock.ofWires transitionStackCellWireRows
    apply List.ofFn_inj.mpr
    funext cell
    apply List.ofFn_inj.mpr
    funext symbol
    exact (arithmeticWidenedCfgWires_stackCell tm seed k cell symbol).symm

/-- Sequential value route for every selected action targeting one stack. -/
noncomputable def transitionStackRouteActionValues
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart : Nat) (seed : TransitionRowSeed)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    TransitionStackValueBlock :=
  transitionStmtSelectedStackActionValues_eval tm k originStart
    (workHeight tm seed.height) seed.start (seed.start + 1)
    (transitionStackRouteSourceBlock tm seed k) actions

/-- The one-action fold recovers the already verified primitive descriptor
route exactly. -/
theorem transitionStackRouteActionValues_singleton
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart : Nat) (seed : TransitionRowSeed)
    (action : TransitionStmtSelectedStackAction tm k) :
    (transitionStackRouteActionValues tm k originStart seed
      [action]).flatten =
      action.routeValues tm k originStart seed := by
  unfold transitionStackRouteActionValues
    transitionStmtSelectedStackActionValues_eval
  rw [transitionStackRouteSourceBlock_eq]
  exact (action.routeValues_eq tm k originStart seed).symm

/-- For an arbitrary action sequence, the descriptor-derived source fold is
exactly the established list semantics on the real widened stack. -/
theorem transitionStackRouteActionValues_eq
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart : Nat) (seed : TransitionRowSeed)
    (actions : List (TransitionStmtSelectedStackAction tm k)) :
    transitionStackRouteActionValues tm k originStart seed actions =
      transitionStmtSelectedStackActionValues_eval tm k originStart
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k)) actions := by
  unfold transitionStackRouteActionValues
  rw [transitionStackRouteSourceBlock_eq]

end CLRS.Chapter34.Turing.CookLevin
