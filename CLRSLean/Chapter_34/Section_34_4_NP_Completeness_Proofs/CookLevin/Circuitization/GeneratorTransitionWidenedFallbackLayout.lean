import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotEnumeration
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionWidening
import Mathlib.Tactic

/-!
# Canonical widened-source fallback layout

The first dispatch label uses the widened public row as its `whenFalse` arm.
This module enumerates that complete workspace row in canonical coordinate
order, including the extra height bits and blank cells introduced by
widening, and proves exact agreement with the semantic wire bundle.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Halted, label, and state wires of the widened source. -/
def transitionWidenedFallbackPrefixValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  List.range' seed.rowBase (transitionEqPrefixWidth tm)

/-- Height wires of one widened stack, with fresh overflow positions fixed to
the local false wire. -/
def transitionWidenedFallbackStackHeightValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) : List Nat :=
  List.ofFn fun index : Fin (workHeight tm seed.height + 1) =>
    if _h : index.val < seed.height + 1 then
      seed.rowBase +
        (transitionEqPrefixWidth tm +
          cfgStackBitOffset tm seed.height k + index.val)
    else seed.start

/-- Cell-symbol wires of one widened stack.  Public cells retain their row
wires; every extra cell is the fixed blank one-hot vector. -/
def transitionWidenedFallbackStackCellValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) : List Nat :=
  (List.ofFn fun cell : Fin (workHeight tm seed.height) =>
    List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
      if _h : cell.val < seed.height then
        seed.rowBase +
          (transitionEqPrefixWidth tm +
            cfgStackBitOffset tm seed.height k + (seed.height + 1) +
              (symbol.val +
                ((reachableAlphabet tm k).card + 1) * cell.val))
      else if symbol.val = (reachableAlphabet tm k).card then
        seed.start + 1
      else seed.start).flatten

/-- Complete canonical values of one widened stack block. -/
def transitionWidenedFallbackStackValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) : List Nat :=
  transitionWidenedFallbackStackHeightValues tm seed k ++
    transitionWidenedFallbackStackCellValues tm seed k

/-- Complete workspace row in the same fixed-stack order as
`cfgSlotEquivFin`. -/
def transitionWidenedFallbackValues
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) : List Nat :=
  transitionWidenedFallbackPrefixValues tm seed ++
    ((arithmeticRuntimeStackSourceIndices tm).map fun position =>
      transitionWidenedFallbackStackValues tm seed
        ((arithmeticStackEquiv tm).symm position)).flatten

@[simp] theorem arithmeticWidenedCfgWires_halted
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).halted = seed.rowBase := by
  rfl

@[simp] theorem arithmeticWidenedCfgWires_label
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (index : Fin (labelCount tm + 1)) :
    (arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).label index = seed.rowBase + (1 + index.val) := by
  rfl

@[simp] theorem arithmeticWidenedCfgWires_state
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (index : Fin (stateCount tm)) :
    (arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).state index =
        seed.rowBase + (1 + (labelCount tm + 1) + index.val) := by
  change (arithmeticCfgWires tm seed.height seed.rowBase).state index = _
  rw [arithmeticCfgWires_state]

/-- Pointwise closed formula for one widened height coordinate. -/
theorem arithmeticWidenedCfgWires_stackHeight
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (index : Fin (workHeight tm seed.height + 1)) :
    (arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).stackHeight k index =
      if _h : index.val < seed.height + 1 then
        seed.rowBase +
          (transitionEqPrefixWidth tm +
            cfgStackBitOffset tm seed.height k + index.val)
      else seed.start := by
  simp only [CfgBundle.stackHeight_apply, arithmeticWidenedCfgWires]
  split
  · change seed.rowBase +
        (cfgSlotEquivFin tm seed.height
          (CfgSlot.stackHeight k ⟨index.val, by omega⟩)).val = _
    rw [cfgSlotEquivFin_stackHeight_val]
    unfold transitionEqPrefixWidth
    ring
  · rfl

/-- Pointwise closed formula for one widened cell-symbol coordinate. -/
theorem arithmeticWidenedCfgWires_stackCell
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (cell : Fin (workHeight tm seed.height))
    (symbol : Fin ((reachableAlphabet tm k).card + 1)) :
    (arithmeticWidenedCfgWires tm seed.height seed.start
      seed.rowBase).stackCell k cell symbol =
      if _h : cell.val < seed.height then
        seed.rowBase +
          (transitionEqPrefixWidth tm +
            cfgStackBitOffset tm seed.height k + (seed.height + 1) +
              (symbol.val +
                ((reachableAlphabet tm k).card + 1) * cell.val))
      else if symbol.val = (reachableAlphabet tm k).card then
        seed.start + 1
      else seed.start := by
  simp only [CfgBundle.stackCell_apply, arithmeticWidenedCfgWires]
  split
  · change seed.rowBase +
        (cfgSlotEquivFin tm seed.height
          (CfgSlot.stackCell k ⟨cell.val, by omega⟩ symbol)).val = _
    rw [cfgSlotEquivFin_stackCell_val]
    unfold transitionEqPrefixWidth
    ring
  · split <;> rfl

/-- The explicit prefix slot enumeration reads exactly the closed prefix
value interval. -/
theorem transitionWidenedFallbackPrefixValues_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionEqPrefixSlots tm (workHeight tm seed.height)).map
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase) =
      transitionWidenedFallbackPrefixValues tm seed := by
  unfold transitionEqPrefixSlots transitionWidenedFallbackPrefixValues
    transitionEqPrefixWidth
  rw [List.map_append, List.map_cons, List.map_ofFn, List.map_ofFn]
  let wires := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
  change wires.halted ::
      (List.ofFn fun index : Fin (labelCount tm + 1) => wires.label index) ++
      (List.ofFn fun index : Fin (stateCount tm) => wires.state index) = _
  simp_rw [wires, arithmeticWidenedCfgWires_halted,
    arithmeticWidenedCfgWires_label, arithmeticWidenedCfgWires_state]
  have hlabels :
      (List.ofFn fun index : Fin (labelCount tm + 1) =>
        seed.rowBase + (1 + index.val)) =
        List.range' (seed.rowBase + 1) (labelCount tm + 1) := by
    rw [show (List.ofFn fun index : Fin (labelCount tm + 1) =>
        seed.rowBase + (1 + index.val)) =
      List.ofFn fun index : Fin (labelCount tm + 1) =>
        (seed.rowBase + 1) + index.val by
          apply List.ofFn_inj.mpr
          funext index
          omega]
    exact transitionEqOfFnAdd_eq_range _ _
  have hstates :
      (List.ofFn fun index : Fin (stateCount tm) =>
        seed.rowBase + (1 + (labelCount tm + 1) + index.val)) =
        List.range' (seed.rowBase + (1 + (labelCount tm + 1)))
          (stateCount tm) := by
    rw [show (List.ofFn fun index : Fin (stateCount tm) =>
        seed.rowBase + (1 + (labelCount tm + 1) + index.val)) =
      List.ofFn fun index : Fin (stateCount tm) =>
        (seed.rowBase + (1 + (labelCount tm + 1))) + index.val by
          apply List.ofFn_inj.mpr
          funext index
          omega]
    exact transitionEqOfFnAdd_eq_range _ _
  rw [hlabels, hstates]
  change [seed.rowBase] ++
      List.range' (seed.rowBase + 1) (labelCount tm + 1) ++
      List.range' (seed.rowBase + (1 + (labelCount tm + 1)))
        (stateCount tm) = _
  rw [← List.range'_one (s := seed.rowBase) (step := 1)]
  rw [List.range'_append]
  simpa only [Nat.one_mul] using
    (List.range'_append (s := seed.rowBase)
      (m := 1 + (labelCount tm + 1))
      (n := stateCount tm) (step := 1))

/-- The explicit workspace stack slots read exactly the closed piecewise
height-and-cell formulas. -/
theorem transitionWidenedFallbackStackValues_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) :
    (transitionEqStackSlots tm (workHeight tm seed.height) k).map
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase) =
      transitionWidenedFallbackStackValues tm seed k := by
  unfold transitionEqStackSlots transitionWidenedFallbackStackValues
    transitionWidenedFallbackStackHeightValues
    transitionWidenedFallbackStackCellValues
  rw [List.map_append, List.map_flatten, List.map_ofFn]
  rw [List.map_ofFn]
  congr 1
  · apply List.ofFn_inj.mpr
    funext index
    exact arithmeticWidenedCfgWires_stackHeight tm seed k index
  · apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    simp only [Function.comp_apply]
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext symbol
    exact arithmeticWidenedCfgWires_stackCell tm seed k cell symbol

/-- The fixed explicit workspace-slot order evaluates to the complete closed
widened fallback list. -/
theorem transitionWidenedFallbackValues_eq_explicitSlots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    (transitionEqPublicSlots tm (workHeight tm seed.height)).map
        (arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase) =
      transitionWidenedFallbackValues tm seed := by
  unfold transitionEqPublicSlots transitionWidenedFallbackValues
  rw [List.map_append, List.map_flatten, List.map_map,
    transitionWidenedFallbackPrefixValues_eq_slots]
  congr 1
  apply congrArg List.flatten
  apply List.map_congr_left
  intro position hposition
  exact transitionWidenedFallbackStackValues_eq_slots tm seed
    ((arithmeticStackEquiv tm).symm position)

/-- The closed fallback list is exactly the canonical `Fin` enumeration of
the semantic widened wire bundle. -/
theorem transitionWidenedFallbackValues_eq_canonical
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    transitionWidenedFallbackValues tm seed =
      List.ofFn fun coordinate : Fin (cfgBitCount tm
          (workHeight tm seed.height)) =>
        arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase
          ((cfgSlotEquivFin tm (workHeight tm seed.height)).symm coordinate) := by
  calc
    transitionWidenedFallbackValues tm seed =
        (transitionEqPublicSlots tm (workHeight tm seed.height)).map
          (arithmeticWidenedCfgWires tm seed.height seed.start
            seed.rowBase) :=
      (transitionWidenedFallbackValues_eq_explicitSlots tm seed).symm
    _ = _ := by
      rw [transitionEqPublicSlots_eq_canonical, List.map_ofFn]
      rfl

end CLRS.Chapter34.Turing.CookLevin
