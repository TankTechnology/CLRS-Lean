import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteActionFold
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmTerminalValueRouting
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementTerminalPrefixAffine

/-!
# Complete terminal rows from sequential stack routes

The affine prefix and every per-stack selected-action fold are assembled here
in canonical stack order.  This produces a descriptor-derived value route for
each terminal statement row and proves exact agreement with the previously
verified semantic route across the whole fixed label table.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Complete routed stack blocks for one terminal row, in canonical machine
stack order. -/
noncomputable def TransitionStmtTerminalRowLayout.stackDescriptorRouteValues
    (tm : _root_.Turing.FinTM2) (originStart : Nat)
    (seed : TransitionRowSeed)
    (layout : TransitionStmtTerminalRowLayout tm) : List (List Nat) :=
  (arithmeticRuntimeStackSourceIndices tm).map fun position =>
    let k := (arithmeticStackEquiv tm).symm position
    (transitionStackRouteActionValues tm k originStart seed
      (transitionStmtStackActionsFor tm k layout.stackActions)).flatten

/-- The descriptor-derived action folds are exactly the established
list-valued stack routes. -/
theorem TransitionStmtTerminalRowLayout.stackDescriptorRouteValues_eq
    (tm : _root_.Turing.FinTM2) (originStart : Nat)
    (seed : TransitionRowSeed)
    (layout : TransitionStmtTerminalRowLayout tm) :
    layout.stackDescriptorRouteValues tm originStart seed =
      layout.stackValueRouteValues tm originStart
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start
          seed.rowBase) := by
  unfold TransitionStmtTerminalRowLayout.stackDescriptorRouteValues
    TransitionStmtTerminalRowLayout.stackValueRouteValues
    TransitionStmtTerminalRowLayout.stackValueBlocks
  rw [List.map_map]
  apply List.map_congr_left
  intro position hposition
  exact congrArg TransitionStackValueBlock.flatten
    (transitionStackRouteActionValues_eq tm
      ((arithmeticStackEquiv tm).symm position) originStart seed
      (transitionStmtStackActionsFor tm
        ((arithmeticStackEquiv tm).symm position) layout.stackActions))

/-- Descriptor-derived terminal row for one normalized true-arm entry. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch _ _ _ _ => []
  | .terminal labelOffset _ rowLayout _ =>
      let originStart := seed.start + labelOffset.eval seed.height
      affineUnaryTripleMap
          (transitionStmtTerminalPrefixForms tm labelOffset rowLayout)
          (transitionTailAffineSeed seed) ++
        (rowLayout.stackDescriptorRouteValues tm originStart seed).flatten

/-- Each descriptor-derived terminal route equals the prior complete semantic
terminal value route. -/
theorem
    TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.terminalRowDescriptorRoute tm seed =
      layout.terminalRowValueRoute tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch => rfl
  | terminal labelOffset label rowLayout hlayout =>
      simp only [
        TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute,
        TransitionDispatchTrueArmNormalizedLayout.terminalRowValueRoute]
      rw [transitionStmtTerminalPrefixForms_value]
      rw [rowLayout.stackDescriptorRouteValues_eq]

/-- Descriptor-derived terminal rows across the complete fixed label table. -/
noncomputable def transitionDispatchTerminalRowDescriptorRoutes
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  (transitionDispatchTrueArmNormalizedLayouts tm).flatMap
    (TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute
      tm seed)

/-- The complete descriptor-derived terminal-row family is byte-for-byte the
existing routed terminal family. -/
theorem transitionDispatchTerminalRowDescriptorRoutes_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchTerminalRowDescriptorRoutes tm seed =
      transitionDispatchTerminalRowValueRoutes tm seed := by
  unfold transitionDispatchTerminalRowDescriptorRoutes
    transitionDispatchTerminalRowValueRoutes
  apply List.flatMap_congr
  intro layout hlayout
  exact layout.terminalRowDescriptorRoute_eq tm seed

end CLRS.Chapter34.Turing.CookLevin
