import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteTerminal
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxTrueArmValueRouting

/-!
# Unified descriptor routes for complete dispatch true arms

Branch-ending rows already form one affine progression.  Terminal-ending rows
now have an affine prefix plus complete sequential stack routes.  This module
merges both cases in the original program-label order.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Descriptor-derived row contributed by one normalized true-arm entry. -/
noncomputable def
    TransitionDispatchTrueArmNormalizedLayout.descriptorValueRoute
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    TransitionDispatchTrueArmNormalizedLayout tm → List Nat
  | .branch labelOffset _ branchOffset _ =>
      transitionProgressionFirstValues
        (transitionDispatchBranchOutputProgression tm seed labelOffset
          branchOffset)
  | layout@(.terminal _ _ _ _) =>
      layout.terminalRowDescriptorRoute tm seed

/-- Both descriptor cases equal the established complete true-arm value route.
-/
theorem
    TransitionDispatchTrueArmNormalizedLayout.descriptorValueRoute_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height)
    (layout : TransitionDispatchTrueArmNormalizedLayout tm) :
    layout.descriptorValueRoute tm seed = layout.valueRoute tm seed := by
  cases layout with
  | branch labelOffset label branchOffset hbranch =>
      calc
        transitionProgressionFirstValues
            (transitionDispatchBranchOutputProgression tm seed labelOffset
              branchOffset) =
          transitionCfgWireValues tm (workHeight tm seed.height)
            (transitionStmtOutputWires tm (workHeight tm seed.height)
              seed.start (seed.start + 1)
              (seed.start + labelOffset.eval seed.height)
              (arithmeticWidenedCfgWires tm seed.height seed.start
                seed.rowBase)
              (tm.m label) (stmtPushSet_program_subset tm label)) :=
            transitionDispatchBranchOutputProgression_values tm seed
              labelOffset branchOffset label hbranch hwork
        _ = (TransitionDispatchTrueArmNormalizedLayout.branch labelOffset
              label branchOffset hbranch).values tm seed :=
            (TransitionDispatchTrueArmNormalizedLayout.values_eq_semantic
              tm seed hwork
              (.branch labelOffset label branchOffset hbranch)).symm
        _ = (TransitionDispatchTrueArmNormalizedLayout.branch labelOffset
              label branchOffset hbranch).valueRoute tm seed := rfl
  | terminal labelOffset label rowLayout hlayout =>
      exact
        (TransitionDispatchTrueArmNormalizedLayout.terminalRowDescriptorRoute_eq
          tm seed (.terminal labelOffset label rowLayout hlayout)).trans rfl

/-- Descriptor-derived rows in the verifier's complete fixed label order. -/
noncomputable def transitionDispatchTrueArmDescriptorRoutes
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    List (List Nat) :=
  (transitionDispatchTrueArmNormalizedLayouts tm).map
    (TransitionDispatchTrueArmNormalizedLayout.descriptorValueRoute tm seed)

/-- The descriptor table is exactly the previous complete routed table. -/
theorem transitionDispatchTrueArmDescriptorRoutes_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchTrueArmDescriptorRoutes tm seed =
      transitionDispatchTrueArmValueRoutes tm seed := by
  unfold transitionDispatchTrueArmDescriptorRoutes
    transitionDispatchTrueArmValueRoutes
  apply List.map_congr_left
  intro layout hlayout
  exact layout.descriptorValueRoute_eq tm seed hwork

/-- At positive workspace height the descriptor table is therefore the exact
semantic true-arm family consumed by dispatch. -/
theorem transitionDispatchTrueArmDescriptorRoutes_eq_seed
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionDispatchTrueArmDescriptorRoutes tm seed =
      transitionDispatchTrueArmRowsFromSeed tm seed := by
  rw [transitionDispatchTrueArmDescriptorRoutes_eq tm seed hwork]
  exact transitionDispatchTrueArmValueRoutes_eq_seed tm seed hwork

end CLRS.Chapter34.Turing.CookLevin
