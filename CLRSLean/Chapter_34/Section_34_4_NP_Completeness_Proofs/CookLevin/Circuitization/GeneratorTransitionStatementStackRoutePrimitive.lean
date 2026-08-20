import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteCellActions

/-!
# Complete descriptor routes for primitive stack actions

Height and cell routes are combined here in canonical stack-block order.  The
result covers one selected push or pop from the real widened source and agrees
with the full flattened list semantics, not merely its two projections.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Complete descriptor value route for one push. -/
noncomputable def transitionStackRoutePushBlockValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (symbol : SymbolWires tm k) : List Nat :=
  transitionStackRoutePushHeightValues tm seed k ++
    transitionStackRoutePushCellValues tm seed k symbol

/-- Complete descriptor value route for one pop. -/
noncomputable def transitionStackRoutePopBlockValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (fresh : Nat) : List Nat :=
  transitionStackRoutePopHeightValues tm seed k fresh ++
    transitionStackRoutePopCellValues tm seed k

/-- Combining the two verified push projections gives exactly the flattened
result of the actual list-valued push. -/
theorem transitionStackRoutePushBlockValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (symbol : SymbolWires tm k) :
    transitionStackRoutePushBlockValues tm seed k symbol =
      ((TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).push tm k (workHeight tm seed.height)
            seed.start symbol).flatten := by
  unfold transitionStackRoutePushBlockValues
    TransitionStackValueBlock.flatten
  rw [transitionStackRoutePushHeightValues_eq,
    transitionStackRoutePushCellValues_eq]

/-- Combining the two verified pop projections gives exactly the flattened
result of the actual list-valued pop. -/
theorem transitionStackRoutePopBlockValues_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) (k : tm.K)
    (fresh : Nat) :
    transitionStackRoutePopBlockValues tm seed k fresh =
      ((TransitionStackValueBlock.ofWires
        ((arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase).stack k)).pop tm k (workHeight tm seed.height)
            seed.start (seed.start + 1) fresh).flatten := by
  unfold transitionStackRoutePopBlockValues
    TransitionStackValueBlock.flatten
  rw [transitionStackRoutePopHeightValues_eq,
    transitionStackRoutePopCellValues_eq]

/-- Descriptor route for one verifier-fixed selected-stack action. -/
noncomputable def TransitionStmtSelectedStackAction.routeValues
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart : Nat) (seed : TransitionRowSeed) :
    TransitionStmtSelectedStackAction tm k → List Nat
  | .push symbolOffsets =>
      transitionStackRoutePushBlockValues tm seed k
        (fun target => originStart +
          (symbolOffsets target).eval (workHeight tm seed.height))
  | .pop heightWireOffset =>
      transitionStackRoutePopBlockValues tm seed k
        (originStart + heightWireOffset.eval (workHeight tm seed.height))

/-- A routed selected action agrees with its complete list-valued semantics on
the real widened source stack. -/
theorem TransitionStmtSelectedStackAction.routeValues_eq
    (tm : _root_.Turing.FinTM2) (k : tm.K)
    (originStart : Nat) (seed : TransitionRowSeed)
    (action : TransitionStmtSelectedStackAction tm k) :
    action.routeValues tm k originStart seed =
      (action.evalValues tm k originStart (workHeight tm seed.height)
        seed.start (seed.start + 1)
        (TransitionStackValueBlock.ofWires
          ((arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase).stack k))).flatten := by
  cases action with
  | push symbolOffsets =>
      exact transitionStackRoutePushBlockValues_eq tm seed k _
  | pop heightWireOffset =>
      exact transitionStackRoutePopBlockValues_eq tm seed k _

end CLRS.Chapter34.Turing.CookLevin
