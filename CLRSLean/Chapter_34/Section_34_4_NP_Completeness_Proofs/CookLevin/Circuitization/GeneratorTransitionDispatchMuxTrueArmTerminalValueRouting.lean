import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmNormalized
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalStackValueRouting

/-!
# Complete value routes for terminal true-arm rows

The normalized true-arm table interleaves branch-ending and terminal-ending
program labels.  This file assigns an empty terminal route to branch entries
and the affine-prefix-plus-stack-route representation to terminal entries.  It
then proves exact agreement with the complete structured terminal row for
every entry and for the whole fixed label table.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Complete semantic terminal row selected by one normalized entry. -/
def TransitionDispatchTrueArmNormalizedLayout.terminalRowValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      rowLayout.structuredValues tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)

/-- Complete list-valued route of the same selected terminal row. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.terminalRowValueRoute
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      let start := seed.start + labelOffset.eval seed.height
      let height := workHeight tm seed.height
      let source := arithmeticWidenedCfgWires tm seed.height seed.start
        seed.rowBase
      rowLayout.prefixValues tm start height seed.start (seed.start + 1)
          source ++
        (rowLayout.stackValueRouteValues tm start height seed.start
          (seed.start + 1) source).flatten

/-- Each selected route is literally the complete semantic terminal row. -/
theorem
    TransitionDispatchTrueArmNormalizedLayout.terminalRowValueRoute_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.terminalRowValueRoute tm seed =
      layout.terminalRowValues tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch => rfl
  | terminal labelOffset label rowLayout hlayout =>
      exact (rowLayout.structuredValues_eq_valueRoutes tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase)).symm

/-- Complete fixed-label terminal route family for one transition seed. -/
noncomputable def transitionDispatchTerminalRowValueRoutes
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.terminalRowValueRoute tm seed)

/-- Complete semantic terminal-row stream selected by the same label table. -/
def transitionDispatchTerminalRowValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.terminalRowValues tm seed)

/-- The whole fixed label table of routes equals the selected semantic
terminal-row stream, preserving original program-label order. -/
theorem transitionDispatchTerminalRowValueRoutes_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchTerminalRowValueRoutes tm seed =
      transitionDispatchTerminalRowValues tm seed := by
  unfold transitionDispatchTerminalRowValueRoutes
    transitionDispatchTerminalRowValues
  apply List.flatMap_congr
  intro layout hlayout
  exact layout.terminalRowValueRoute_eq tm seed

end CLRS.Chapter34.Turing.CookLevin
