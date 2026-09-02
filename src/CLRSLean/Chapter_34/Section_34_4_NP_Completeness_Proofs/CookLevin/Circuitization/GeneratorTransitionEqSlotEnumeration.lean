import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotIntervals
import Mathlib.Tactic

/-!
# Canonical transition equality slot enumeration

The runtime equality source visits a fixed prefix followed by fixed-machine
stack blocks.  This module enumerates the corresponding `CfgSlot`s and proves
that their canonical numeric coordinates are exactly the full row interval.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-- Halted, label, and state slots in canonical public-row order. -/
def transitionEqPrefixSlots (tm : _root_.Turing.FinTM2) (height : Nat) :
    List (CfgSlot tm height) :=
  CfgSlot.halted tm height ::
    (List.ofFn fun index : Fin (labelCount tm + 1) =>
      CfgSlot.label index) ++
    (List.ofFn fun index : Fin (stateCount tm) =>
      CfgSlot.state index)

/-- Height followed by cell-symbol slots of one fixed stack. -/
def transitionEqStackSlots (tm : _root_.Turing.FinTM2) (height : Nat)
    (k : tm.K) : List (CfgSlot tm height) :=
  (List.ofFn fun index : Fin (height + 1) =>
    CfgSlot.stackHeight k index) ++
  (List.ofFn fun cell : Fin height =>
    List.ofFn fun symbol : Fin ((reachableAlphabet tm k).card + 1) =>
      CfgSlot.stackCell k cell symbol).flatten

/-- Explicit public slots in the same fixed-stack order as the runtime
equality progression family. -/
def transitionEqPublicSlots (tm : _root_.Turing.FinTM2) (height : Nat) :
    List (CfgSlot tm height) :=
  transitionEqPrefixSlots tm height ++
    ((arithmeticRuntimeStackSourceIndices tm).map fun position =>
      transitionEqStackSlots tm height
        ((arithmeticStackEquiv tm).symm position)).flatten

/-- Prefix slots occupy the initial canonical interval. -/
theorem transitionEqPrefixSlots_values
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionEqPrefixSlots tm height).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) =
      List.range' 0 (transitionEqPrefixWidth tm) := by
  unfold transitionEqPrefixSlots transitionEqPrefixWidth
  rw [List.map_append, List.map_cons, List.map_ofFn, List.map_ofFn]
  change (cfgSlotEquivFin tm height (CfgSlot.halted tm height)).val ::
      (List.ofFn fun index : Fin (labelCount tm + 1) =>
        (cfgSlotEquivFin tm height (CfgSlot.label index)).val) ++
      (List.ofFn fun index : Fin (stateCount tm) =>
        (cfgSlotEquivFin tm height (CfgSlot.state index)).val) = _
  simp only [cfgSlotEquivFin_halted_val,
    cfgSlotEquivFin_label_val, cfgSlotEquivFin_state_val]
  rw [transitionEqOfFnAdd_eq_range 1 (labelCount tm + 1)]
  rw [transitionEqOfFnAdd_eq_range
    (1 + (labelCount tm + 1)) (stateCount tm)]
  change [0] ++ List.range' 1 (labelCount tm + 1) ++
      List.range' (1 + (labelCount tm + 1)) (stateCount tm) = _
  rw [← List.range'_one (s := 0) (step := 1), List.range'_append]
  simpa only [Nat.one_mul, Nat.zero_add] using
    (List.range'_append (s := 0)
      (m := 1 + (labelCount tm + 1)) (n := stateCount tm) (step := 1))

/-- One stack's slots occupy its exact canonical stack interval. -/
theorem transitionEqStackSlots_values
    (tm : _root_.Turing.FinTM2) (height : Nat) (k : tm.K) :
    (transitionEqStackSlots tm height k).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) =
      List.range'
        (transitionEqPrefixWidth tm + cfgStackBitOffset tm height k)
        (cfgStackBitWidth tm height k) := by
  unfold transitionEqStackSlots transitionEqPrefixWidth
  rw [List.map_append, List.map_flatten, List.map_ofFn]
  rw [List.map_ofFn]
  change (List.ofFn fun index : Fin (height + 1) =>
      (cfgSlotEquivFin tm height
        (CfgSlot.stackHeight k index)).val) ++
      (List.ofFn fun cell : Fin height =>
        List.map (fun slot => (cfgSlotEquivFin tm height slot).val)
          (List.ofFn fun symbol :
            Fin ((reachableAlphabet tm k).card + 1) =>
              CfgSlot.stackCell k cell symbol)).flatten = _
  simp_rw [List.map_ofFn]
  change (List.ofFn fun index : Fin (height + 1) =>
      (cfgSlotEquivFin tm height
        (CfgSlot.stackHeight k index)).val) ++
      (List.ofFn fun cell : Fin height =>
        List.ofFn fun symbol :
            Fin ((reachableAlphabet tm k).card + 1) =>
          (cfgSlotEquivFin tm height
            (CfgSlot.stackCell k cell symbol)).val).flatten = _
  simp only [cfgSlotEquivFin_stackHeight_val]
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
  unfold cfgStackBitWidth
  rw [← List.range'_append]
  · apply congrArg₂ (fun left right => left ++ right)
    · apply List.ext_getElem
      · simp
      · intro index hleft hright
        simp only [List.getElem_ofFn, List.getElem_range']
        ring
    · apply List.ext_getElem
      · simp
      · intro index hleft hright
        simp only [List.getElem_ofFn, List.getElem_range']
        ring

private theorem transitionEqPublicWidth_eq
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    transitionEqPrefixWidth tm +
        (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
          cfgStackBitWidth tm height
            ((arithmeticStackEquiv tm).symm position)).sum =
      cfgBitCount tm height := by
  letI : Fintype tm.K := tm.kFin
  rw [List.sum_ofFn]
  rw [(arithmeticStackEquiv tm).symm.sum_comp
    (fun k => cfgStackBitWidth tm height k)]
  unfold transitionEqPrefixWidth cfgBitCount cfgStackBitWidth
  congr

/-- The explicit runtime slot order maps to every canonical row coordinate,
once and in increasing order. -/
theorem transitionEqPublicSlots_values
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionEqPublicSlots tm height).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) =
      List.range' 0 (cfgBitCount tm height) := by
  unfold transitionEqPublicSlots
  rw [List.map_append, List.map_flatten, List.map_map]
  have hstacks :
      (List.map
        ((List.map fun slot => (cfgSlotEquivFin tm height slot).val) ∘
          fun position => transitionEqStackSlots tm height
            ((arithmeticStackEquiv tm).symm position))
        (arithmeticRuntimeStackSourceIndices tm)).flatten =
      (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
        List.range'
          (transitionEqPrefixWidth tm + cfgStackBitOffset tm height
            ((arithmeticStackEquiv tm).symm position))
          (cfgStackBitWidth tm height
            ((arithmeticStackEquiv tm).symm position))).flatten := by
    apply congrArg List.flatten
    unfold arithmeticRuntimeStackSourceIndices
    rw [← List.ofFn_eq_map]
    apply List.ofFn_inj.mpr
    funext position
    change (transitionEqStackSlots tm height
      ((arithmeticStackEquiv tm).symm position)).map
        (fun slot => (cfgSlotEquivFin tm height slot).val) = _
    exact transitionEqStackSlots_values tm height
      ((arithmeticStackEquiv tm).symm position)
  rw [hstacks, transitionEqPrefixSlots_values]
  rw [transitionEqStackIntervals_eq_range tm height
    (transitionEqPrefixWidth tm)]
  calc
    List.range' 0 (transitionEqPrefixWidth tm) ++
        List.range' (transitionEqPrefixWidth tm)
          (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
            cfgStackBitWidth tm height
              ((arithmeticStackEquiv tm).symm position)).sum =
      List.range' 0
        (transitionEqPrefixWidth tm +
          (List.ofFn fun position : Fin (arithmeticStackCount tm) =>
            cfgStackBitWidth tm height
              ((arithmeticStackEquiv tm).symm position)).sum) := by
        simpa only [Nat.one_mul, Nat.zero_add] using
          (List.range'_append (s := 0)
            (m := transitionEqPrefixWidth tm)
            (n := (List.ofFn fun position :
                Fin (arithmeticStackCount tm) =>
              cfgStackBitWidth tm height
                ((arithmeticStackEquiv tm).symm position)).sum)
            (step := 1))
    _ = _ := by rw [transitionEqPublicWidth_eq]

/-- The explicit runtime enumeration is literally the canonical inverse
enumeration of `cfgSlotEquivFin`. -/
theorem transitionEqPublicSlots_eq_canonical
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    transitionEqPublicSlots tm height =
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        (cfgSlotEquivFin tm height).symm coordinate := by
  have hvalues := transitionEqPublicSlots_values tm height
  have hlength : (transitionEqPublicSlots tm height).length =
      cfgBitCount tm height := by
    simpa using congrArg List.length hvalues
  apply List.ext_getElem
  · simp [hlength]
  · intro index hleft hright
    simp only [List.getElem_ofFn]
    apply (cfgSlotEquivFin tm height).injective
    apply Fin.ext
    rw [(cfgSlotEquivFin tm height).apply_symm_apply]
    have hget := congrArg (fun values : List Nat => values[index]?) hvalues
    simp only [List.getElem?_map] at hget
    have hcfg : index < cfgBitCount tm height := by omega
    rw [List.getElem?_eq_getElem hleft,
      List.getElem?_range' hcfg] at hget
    simpa using hget

end CLRS.Chapter34.Turing.CookLevin
