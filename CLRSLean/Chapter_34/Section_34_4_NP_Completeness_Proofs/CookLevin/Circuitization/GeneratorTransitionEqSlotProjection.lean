import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotEnumeration
import Mathlib.Tactic

/-!
# Transition equality slot projection

This module embeds public tableau slots into the widened workspace and records
the local arithmetic facts needed to align runtime equality progressions.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Embed one public slot into the corresponding widened-workspace slot. -/
def transitionEqWorkspaceSlot (tm : _root_.Turing.FinTM2) (height : Nat) :
    CfgSlot tm height → CfgSlot tm (workHeight tm height)
  | .inl _ => CfgSlot.halted tm (workHeight tm height)
  | .inr (.inl label) => CfgSlot.label label
  | .inr (.inr (.inl state)) => CfgSlot.state state
  | .inr (.inr (.inr ⟨k, .inl stackHeight⟩)) =>
      CfgSlot.stackHeight k
        ⟨stackHeight.val, by simp only [workHeight]; omega⟩
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      CfgSlot.stackCell k
        ⟨cell.val, by simp only [workHeight]; omega⟩ symbol

/-- Narrowing a workspace wire bundle is evaluation at the embedded slot. -/
theorem narrowCfgWireProjection_eq_workspaceSlot
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (source : CfgWires tm (workHeight tm height))
    (slot : CfgSlot tm height) :
    narrowCfgWireProjection source slot =
      source (transitionEqWorkspaceSlot tm height slot) := by
  rcases slot with (_ | label | state | ⟨k, stackHeight | cell⟩)
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases cell with ⟨cell, symbol⟩
    rfl

/-- Semantic triple attached to one explicit public slot. -/
def transitionEqSlotRow (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) (slot : CfgSlot tm seed.height) :
    Nat × Nat × Nat :=
  (transitionEqStart tm seed.height seed.start +
      6 * (cfgSlotEquivFin tm seed.height slot).val,
    narrowCfgWireProjection (transitionDispatchOutputWires tm seed) slot,
    seed.rowBase + cfgBitCount tm seed.height +
      (cfgSlotEquivFin tm seed.height slot).val)

/-- Closed positional semantics of the progression compiled from one segment. -/
theorem transitionEqSegmentProgressionRows_eq_ofFn
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleProgressionRows
        (transitionEqSegmentProgression tm seed segment) =
      List.ofFn fun index : Fin (segment.count.eval seed.height) =>
        (transitionEqStart tm seed.height seed.start +
            6 * (segment.publicBase.eval seed.height + index.val),
          seed.start + 2 +
              transitionDispatchListFinalMuxOffset tm seed.height
                (programLabels tm) + 3 +
            3 * (segment.workspaceBase.eval seed.height + index.val),
          seed.rowBase + cfgBitCount tm seed.height +
            segment.publicBase.eval seed.height + index.val) := by
  rw [affineUnaryTripleProgressionRows_eq_ofFn]
  change (List.ofFn fun index : Fin (segment.count.eval seed.height) =>
    ((transitionEqSegmentProgression tm seed segment).base₁ + index.val * 6,
      (transitionEqSegmentProgression tm seed segment).base₂ + index.val * 3,
      (transitionEqSegmentProgression tm seed segment).base₃ + index.val * 1)) = _
  apply List.ofFn_inj.mpr
  funext index
  rw [transitionEqSegmentProgression_base₁ tm seed segment hwork,
    transitionEqSegmentProgression_base₂ tm seed segment hwork,
    transitionEqSegmentProgression_base₃]
  apply Prod.ext
  · ring
  · apply Prod.ext <;> ring

def transitionEqStackHeightSlots
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    List (CfgSlot tm height) :=
  List.ofFn fun index : Fin (height + 1) => CfgSlot.stackHeight k index

def transitionEqStackCellSlots
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    List (CfgSlot tm height) :=
  (List.ofFn fun cell : Fin height =>
    List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
      CfgSlot.stackCell k cell symbol).flatten

theorem transitionEqStackSlots_eq_parts
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    transitionEqStackSlots tm height k =
      transitionEqStackHeightSlots tm height k ++
        transitionEqStackCellSlots tm height k := by
  rfl

theorem transitionEqStackHeightSlots_publicValues
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionEqStackHeightSlots tm height k).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) =
      List.range'
        (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k)
        (height + 1) := by
  unfold transitionEqStackHeightSlots
  rw [List.map_ofFn]
  change (List.ofFn fun index : Fin (height + 1) =>
    (cfgSlotEquivFin tm height (CfgSlot.stackHeight k index)).val) = _
  simp only [cfgSlotEquivFin_stackHeight_val]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_range']
    unfold transitionEqPrefixWidth
    ring

theorem transitionEqStackHeightSlots_workspaceValues
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionEqStackHeightSlots tm height k).map
        (fun slot => (cfgSlotEquivFin tm (workHeight tm height)
          (transitionEqWorkspaceSlot tm height slot)).val) =
      List.range'
        (transitionEqPrefixWidth tm +
          cfgStackBitOffset tm (workHeight tm height) k)
        (height + 1) := by
  unfold transitionEqStackHeightSlots
  rw [List.map_ofFn]
  change (List.ofFn fun index : Fin (height + 1) =>
    (cfgSlotEquivFin tm (workHeight tm height)
      (CfgSlot.stackHeight k
        ⟨index.val, by simp only [workHeight]; omega⟩)).val) = _
  simp only [cfgSlotEquivFin_stackHeight_val]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_range']
    unfold transitionEqPrefixWidth
    ring

/-- Public cell slots occupy the cell portion of one public stack block. -/
theorem transitionEqStackCellSlots_publicValues
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionEqStackCellSlots tm height k).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) =
      List.range'
        (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k +
          (height + 1))
        (height * ((reachableAlphabet tm k).card + 1)) := by
  unfold transitionEqStackCellSlots
  rw [List.map_flatten, List.map_ofFn]
  change (List.ofFn fun cell : Fin height =>
    List.map (fun slot => (cfgSlotEquivFin tm height slot).val)
      (List.ofFn fun symbol :
        Fin ((reachableAlphabet tm k).card + 1) =>
          CfgSlot.stackCell k cell symbol)).flatten = _
  simp_rw [List.map_ofFn]
  change (List.ofFn fun cell : Fin height =>
    List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
      (cfgSlotEquivFin tm height
        (CfgSlot.stackCell k cell symbol)).val).flatten = _
  simp only [cfgSlotEquivFin_stackCell_val]
  rw [show (List.ofFn fun cell : Fin height =>
      List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
        1 + (labelCount tm + 1) + stateCount tm +
          cfgStackBitOffset tm height k + (height + 1) +
            (symbol.val +
              ((reachableAlphabet tm k).card + 1) * cell.val)).flatten =
      List.ofFn fun coordinate :
          Fin (height * ((reachableAlphabet tm k).card + 1)) =>
        1 + (labelCount tm + 1) + stateCount tm +
          cfgStackBitOffset tm height k + (height + 1) + coordinate.val by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    apply List.ofFn_inj.mpr
    funext symbol
    congr 1
    ring]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_range']
    unfold transitionEqPrefixWidth
    ring

/-- Public cell slots project to the corresponding prefix of the widened
workspace cell block. -/
theorem transitionEqStackCellSlots_workspaceValues
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionEqStackCellSlots tm height k).map
        (fun slot => (cfgSlotEquivFin tm (workHeight tm height)
          (transitionEqWorkspaceSlot tm height slot)).val) =
      List.range'
        (transitionEqPrefixWidth tm +
          cfgStackBitOffset tm (workHeight tm height) k +
            (workHeight tm height + 1))
        (height * ((reachableAlphabet tm k).card + 1)) := by
  unfold transitionEqStackCellSlots
  rw [List.map_flatten, List.map_ofFn]
  change (List.ofFn fun cell : Fin height =>
    List.map (fun slot =>
      (cfgSlotEquivFin tm (workHeight tm height)
        (transitionEqWorkspaceSlot tm height slot)).val)
      (List.ofFn fun symbol :
        Fin ((reachableAlphabet tm k).card + 1) =>
          CfgSlot.stackCell k cell symbol)).flatten = _
  simp_rw [List.map_ofFn]
  change (List.ofFn fun cell : Fin height =>
    List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
      (cfgSlotEquivFin tm (workHeight tm height)
        (CfgSlot.stackCell k
          ⟨cell.val, by simp only [workHeight]; omega⟩ symbol)).val).flatten = _
  simp only [cfgSlotEquivFin_stackCell_val]
  rw [show (List.ofFn fun cell : Fin height =>
      List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
        1 + (labelCount tm + 1) + stateCount tm +
          cfgStackBitOffset tm (workHeight tm height) k +
            (workHeight tm height + 1) +
              (symbol.val +
                ((reachableAlphabet tm k).card + 1) * cell.val)).flatten =
      List.ofFn fun coordinate :
          Fin (height * ((reachableAlphabet tm k).card + 1)) =>
        1 + (labelCount tm + 1) + stateCount tm +
          cfgStackBitOffset tm (workHeight tm height) k +
            (workHeight tm height + 1) + coordinate.val by
    rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply List.ofFn_inj.mpr
    funext cell
    apply List.ofFn_inj.mpr
    funext symbol
    congr 1
    ring]
  apply List.ext_getElem
  · simp
  · intro index hleft hright
    simp only [List.getElem_ofFn, List.getElem_range']
    unfold transitionEqPrefixWidth
    ring

end CLRS.Chapter34.Turing.CookLevin
