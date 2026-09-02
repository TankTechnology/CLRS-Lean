import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValues
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchMuxFalseArmLayout

/-!
# Structured flattening of transition configuration rows

This file factors the canonical flat row into its fixed status/state prefix
and one block per verifier stack.  It is intentionally independent of any
particular statement action or TM2 controller.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Halted, label, and state wires in canonical prefix order. -/
def transitionCfgPrefixWireValues
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) : List Nat :=
  (transitionEqPrefixSlots tm height).map source

/-- One canonical flat wire block for every stack in fixed-machine order. -/
def transitionCfgStackWireBlocks
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) : List (List Nat) :=
  (arithmeticRuntimeStackSourceIndices tm).map fun position =>
    transitionStackWireValues
      (source.stack ((arithmeticStackEquiv tm).symm position))

/-- Structured row flattening: fixed prefix followed by all stack blocks. -/
def transitionCfgStructuredWireValues
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) : List Nat :=
  transitionCfgPrefixWireValues tm height source ++
    (transitionCfgStackWireBlocks tm height source).flatten

/-- The structured factorization is literally the canonical coordinate-order
row used by every transition controller. -/
theorem transitionCfgStructuredWireValues_eq_canonical
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (source : CfgWires tm height) :
    transitionCfgStructuredWireValues tm height source =
      transitionCfgWireValues tm height source := by
  have hstructured :
      transitionCfgStructuredWireValues tm height source =
        (transitionEqPublicSlots tm height).map source := by
    unfold transitionCfgStructuredWireValues
      transitionCfgPrefixWireValues transitionCfgStackWireBlocks
      transitionEqPublicSlots
    rw [List.map_append, List.map_flatten, List.map_map]
    congr 1
    apply congrArg List.flatten
    apply List.map_congr_left
    intro position hposition
    exact transitionStackWireValues_eq_slot_map tm height source
      ((arithmeticStackEquiv tm).symm position)
  rw [hstructured, transitionEqPublicSlots_eq_canonical]
  unfold transitionCfgWireValues
  rw [List.map_ofFn]
  rfl

end CLRS.Chapter34.Turing.CookLevin
