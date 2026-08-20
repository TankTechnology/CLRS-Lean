import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValueRouting
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalValues

/-!
# List-valued stack routes of terminal rows

This module reconnects the per-stack list semantics to the public terminal-row
normal form.  It gives every terminal stack block a route built solely from
the source value lists and its verifier-fixed selected action subsequence, then
proves exact agreement with the canonical row values.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Per-stack list-valued route results, in the canonical machine-stack order. -/
noncomputable def TransitionStmtTerminalRowLayout.stackValueBlocks
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    List TransitionStackValueBlock :=
  (arithmeticRuntimeStackSourceIndices tm).map fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    transitionStmtSelectedStackActionValues_eval tm k start height falseWire
      trueWire (TransitionStackValueBlock.ofWires (source.stack k))
      (transitionStmtStackActionsFor tm k layout.stackActions)

/-- Canonical flat wire blocks denoted by the independent stack routes. -/
noncomputable def TransitionStmtTerminalRowLayout.stackValueRouteValues
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) : List (List Nat) :=
  (layout.stackValueBlocks tm start height falseWire trueWire source).map
    TransitionStackValueBlock.flatten

/-- Every canonical terminal stack block is exactly its independent
list-valued route, in the same fixed stack order. -/
theorem TransitionStmtTerminalRowLayout.stackBlocks_eq_valueRoutes
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    layout.stackBlocks tm start height falseWire trueWire source =
      layout.stackValueRouteValues tm start height falseWire trueWire
        source := by
  unfold TransitionStmtTerminalRowLayout.stackBlocks
    TransitionStmtTerminalRowLayout.stackValueRouteValues
    TransitionStmtTerminalRowLayout.stackValueBlocks
  rw [List.map_map]
  apply List.map_congr_left
  intro position hposition
  exact transitionStmtStackActions_eval_stack_values tm
    ((arithmeticStackEquiv tm).symm position) start height falseWire trueWire
    source layout.stackActions

/-- The complete structured terminal row is its already-affine prefix followed
by the flattened independent stack routes. -/
theorem TransitionStmtTerminalRowLayout.structuredValues_eq_valueRoutes
    (tm : _root_.Turing.FinTM2) (start height falseWire trueWire : Nat)
    (source : CfgWires tm height)
    (layout : TransitionStmtTerminalRowLayout tm) :
    layout.structuredValues tm start height falseWire trueWire source =
      layout.prefixValues tm start height falseWire trueWire source ++
        (layout.stackValueRouteValues tm start height falseWire trueWire
          source).flatten := by
  unfold TransitionStmtTerminalRowLayout.structuredValues
  rw [layout.stackBlocks_eq_valueRoutes]

end CLRS.Chapter34.Turing.CookLevin
