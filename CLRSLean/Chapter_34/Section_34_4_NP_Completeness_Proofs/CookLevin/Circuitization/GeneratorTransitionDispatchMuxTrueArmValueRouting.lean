import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmTerminalValueRouting

/-!
# Unified complete value routes for transition true arms

Branch-ending labels already have direct affine output rows.  Terminal-ending
labels now have an affine prefix and exact list-valued stack route.  This file
merges those two representations in the original program-label order and
proves that the result is the complete semantic true-arm family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Complete routed row contributed by one normalized true-arm entry. -/
noncomputable def TransitionDispatchTrueArmNormalizedLayout.valueRoute
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | layout@(.branch _ _ _ _) => layout.values tm seed
  | layout@(.terminal _ _ _ _) => layout.terminalRowValueRoute tm seed

/-- Both route cases agree exactly with the normalized semantic row. -/
theorem TransitionDispatchTrueArmNormalizedLayout.valueRoute_eq_values
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.valueRoute tm seed = layout.values tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch => rfl
  | terminal labelOffset label rowLayout hlayout =>
      rw [TransitionDispatchTrueArmNormalizedLayout.valueRoute,
        TransitionDispatchTrueArmNormalizedLayout.terminalRowValueRoute_eq]
      unfold TransitionDispatchTrueArmNormalizedLayout.terminalRowValues
        TransitionDispatchTrueArmNormalizedLayout.values
        TransitionDispatchTrueArmNormalizedLayout.wires
      exact rowLayout.structuredValues_eq_canonical tm
        (seed.start + labelOffset.eval seed.height)
        (workHeight tm seed.height) seed.start (seed.start + 1)
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase)

/-- Unified routed rows in the verifier's fixed program-label order. -/
noncomputable def transitionDispatchTrueArmValueRoutes
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  (transitionDispatchTrueArmNormalizedLayouts tm).map
    (TransitionDispatchTrueArmNormalizedLayout.valueRoute tm seed)

/-- The routed table is exactly the previously verified normalized table. -/
theorem transitionDispatchTrueArmValueRoutes_eq_normalized
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionDispatchTrueArmValueRoutes tm seed =
      transitionDispatchTrueArmNormalizedRows tm seed := by
  unfold transitionDispatchTrueArmValueRoutes
    transitionDispatchTrueArmNormalizedRows
  apply List.map_congr_left
  intro layout hlayout
  exact layout.valueRoute_eq_values tm seed

/-- At positive workspace height, the routed table is therefore the complete
semantic true-arm family consumed by the dispatch muxes. -/
theorem transitionDispatchTrueArmValueRoutes_eq_seed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchTrueArmValueRoutes tm seed =
      transitionDispatchTrueArmRowsFromSeed tm seed := by
  rw [transitionDispatchTrueArmValueRoutes_eq_normalized]
  exact transitionDispatchTrueArmNormalizedRows_eq_seed tm seed hwork

end CLRS.Chapter34.Turing.CookLevin
