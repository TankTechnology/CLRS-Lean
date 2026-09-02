import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqSlotProjection
import Mathlib.Tactic

/-!
# Transition equality segment alignment

This module joins the separately compiled prefix, stack-height, and stack-cell
facts into the complete runtime progression-to-public-slot correspondence.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem transitionEqPrefixSlots_workspaceSlots
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionEqPrefixSlots tm height).map
        (transitionEqWorkspaceSlot tm height) =
      transitionEqPrefixSlots tm (workHeight tm height) := by
  unfold transitionEqPrefixSlots
  rw [List.map_append, List.map_cons, List.map_ofFn, List.map_ofFn]
  rfl

private theorem transitionEqPrefixSlots_workspaceValues
    (tm : _root_.Turing.FinTM2) (height : Nat) :
    (transitionEqPrefixSlots tm height).map
        (fun slot => (cfgSlotEquivFin tm (workHeight tm height)
          (transitionEqWorkspaceSlot tm height slot)).val) =
      List.range' 0 (transitionEqPrefixWidth tm) := by
  calc
    _ = ((transitionEqPrefixSlots tm height).map
          (transitionEqWorkspaceSlot tm height)).map
            (fun slot =>
              (cfgSlotEquivFin tm (workHeight tm height) slot).val) := by
        rw [List.map_map]
        rfl
    _ = (transitionEqPrefixSlots tm (workHeight tm height)).map
          (fun slot =>
            (cfgSlotEquivFin tm (workHeight tm height) slot).val) := by
        rw [transitionEqPrefixSlots_workspaceSlots]
    _ = _ := transitionEqPrefixSlots_values tm (workHeight tm height)

private theorem transitionEqMapValue_of_eq_range {alpha : Type}
    (slots : List alpha) (value : alpha → Nat) (base count : Nat)
    (hvalues : slots.map value = List.range' base count)
    (index : Nat) (hindex : index < slots.length) :
    value slots[index] = base + index := by
  have hcount : slots.length = count := by
    simpa using congrArg List.length hvalues
  have hbound : index < count := by omega
  have hget := congrArg (fun values : List Nat => values[index]?) hvalues
  simp only [List.getElem?_map] at hget
  rw [List.getElem?_eq_getElem hindex,
    List.getElem?_range' hbound] at hget
  simpa using hget

private theorem transitionEqSlotRow_eq
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (slot : CfgSlot tm seed.height) :
    transitionEqSlotRow tm seed slot =
      (transitionEqStart tm seed.height seed.start +
          6 * (cfgSlotEquivFin tm seed.height slot).val,
        seed.start + 2 +
            transitionDispatchListFinalMuxOffset tm seed.height
              (programLabels tm) + 3 +
          3 * (cfgSlotEquivFin tm (workHeight tm seed.height)
            (transitionEqWorkspaceSlot tm seed.height slot)).val,
        seed.rowBase + cfgBitCount tm seed.height +
          (cfgSlotEquivFin tm seed.height slot).val) := by
  unfold transitionEqSlotRow
  rw [narrowCfgWireProjection_eq_workspaceSlot,
    transitionDispatchOutputWires_eq_finalMux]
  rfl

private theorem transitionEqSlotRows_eq_of_ranges
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (slots : List (CfgSlot tm seed.height))
    (publicBase workspaceBase count : Nat)
    (hpublic : slots.map
        (fun slot => (cfgSlotEquivFin tm seed.height slot).val) =
      List.range' publicBase count)
    (hworkspace : slots.map (fun slot =>
        (cfgSlotEquivFin tm (workHeight tm seed.height)
          (transitionEqWorkspaceSlot tm seed.height slot)).val) =
      List.range' workspaceBase count) :
    slots.map (transitionEqSlotRow tm seed) =
      List.ofFn fun index : Fin count =>
        (transitionEqStart tm seed.height seed.start +
            6 * (publicBase + index.val),
          seed.start + 2 +
              transitionDispatchListFinalMuxOffset tm seed.height
                (programLabels tm) + 3 +
            3 * (workspaceBase + index.val),
          seed.rowBase + cfgBitCount tm seed.height +
            publicBase + index.val) := by
  have hlength : slots.length = count := by
    simpa using congrArg List.length hpublic
  apply List.ext_getElem
  · simp [hlength]
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_ofFn]
    rw [transitionEqSlotRow_eq]
    have hslotIndex : index < slots.length := by simpa using hleft
    have hp := transitionEqMapValue_of_eq_range slots
      (fun slot => (cfgSlotEquivFin tm seed.height slot).val)
      publicBase count hpublic index hslotIndex
    have hw := transitionEqMapValue_of_eq_range slots
      (fun slot => (cfgSlotEquivFin tm (workHeight tm seed.height)
        (transitionEqWorkspaceSlot tm seed.height slot)).val)
      workspaceBase count hworkspace index hslotIndex
    rw [hp, hw]
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> ring

private theorem transitionEqSegmentRows_eq_evaluated
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (segment : TransitionEqSegment)
    (publicBase workspaceBase count : Nat)
    (hpublic : segment.publicBase.eval seed.height = publicBase)
    (hworkspace : segment.workspaceBase.eval seed.height = workspaceBase)
    (hcount : segment.count.eval seed.height = count)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleProgressionRows
        (transitionEqSegmentProgression tm seed segment) =
      List.ofFn fun index : Fin count =>
        (transitionEqStart tm seed.height seed.start +
            6 * (publicBase + index.val),
          seed.start + 2 +
              transitionDispatchListFinalMuxOffset tm seed.height
                (programLabels tm) + 3 +
            3 * (workspaceBase + index.val),
          seed.rowBase + cfgBitCount tm seed.height +
            publicBase + index.val) := by
  rw [transitionEqSegmentProgressionRows_eq_ofFn tm seed segment hwork]
  apply List.ext_getElem
  · simp [hcount]
  · intro index hleft hright
    simp only [List.getElem_ofFn]
    rw [hpublic, hworkspace]

private theorem transitionEqPrefixProgressionRows_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleProgressionRows
        (transitionEqSegmentProgression tm seed
          (transitionEqPrefixSegment tm)) =
      (transitionEqPrefixSlots tm seed.height).map
        (transitionEqSlotRow tm seed) := by
  have heval := transitionEqPrefixSegment_eval tm seed.height
  have hp : (transitionEqPrefixSegment tm).publicBase.eval seed.height = 0 := by
    simpa only using congrArg (fun triple => triple.1) heval
  have hw : (transitionEqPrefixSegment tm).workspaceBase.eval seed.height = 0 := by
    simpa only using congrArg (fun triple => triple.2.1) heval
  have hc : (transitionEqPrefixSegment tm).count.eval seed.height =
      transitionEqPrefixWidth tm := by
    simpa only using congrArg (fun triple => triple.2.2) heval
  exact (transitionEqSegmentRows_eq_evaluated tm seed
    (transitionEqPrefixSegment tm) 0 0 (transitionEqPrefixWidth tm)
    hp hw hc hwork).trans
      (transitionEqSlotRows_eq_of_ranges tm seed
        (transitionEqPrefixSlots tm seed.height) 0 0
        (transitionEqPrefixWidth tm)
        (transitionEqPrefixSlots_values tm seed.height)
        (transitionEqPrefixSlots_workspaceValues tm seed.height)).symm

private theorem transitionEqStackHeightProgressionRows_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleProgressionRows
        (transitionEqSegmentProgression tm seed
          (transitionEqStackHeightSegment tm k)) =
      (transitionEqStackHeightSlots tm seed.height k).map
        (transitionEqSlotRow tm seed) := by
  have heval := transitionEqStackHeightSegment_eval tm seed.height k
  have hp : (transitionEqStackHeightSegment tm k).publicBase.eval seed.height =
      transitionEqPrefixWidth tm + cfgStackBitOffset tm seed.height k := by
    simpa only using congrArg (fun triple => triple.1) heval
  have hw : (transitionEqStackHeightSegment tm k).workspaceBase.eval seed.height =
      transitionEqPrefixWidth tm +
        cfgStackBitOffset tm (workHeight tm seed.height) k := by
    simpa only using congrArg (fun triple => triple.2.1) heval
  have hc : (transitionEqStackHeightSegment tm k).count.eval seed.height =
      seed.height + 1 := by
    simpa only using congrArg (fun triple => triple.2.2) heval
  exact (transitionEqSegmentRows_eq_evaluated tm seed
    (transitionEqStackHeightSegment tm k) _ _ _ hp hw hc hwork).trans
      (transitionEqSlotRows_eq_of_ranges tm seed
        (transitionEqStackHeightSlots tm seed.height k) _ _ _
        (transitionEqStackHeightSlots_publicValues tm seed.height k)
        (transitionEqStackHeightSlots_workspaceValues tm seed.height k)).symm

private theorem transitionEqStackCellProgressionRows_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (k : tm.K) (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleProgressionRows
        (transitionEqSegmentProgression tm seed
          (transitionEqStackCellSegment tm k)) =
      (transitionEqStackCellSlots tm seed.height k).map
        (transitionEqSlotRow tm seed) := by
  have heval := transitionEqStackCellSegment_eval tm seed.height k
  have hp : (transitionEqStackCellSegment tm k).publicBase.eval seed.height =
      transitionEqPrefixWidth tm + cfgStackBitOffset tm seed.height k +
        (seed.height + 1) := by
    simpa only using congrArg (fun triple => triple.1) heval
  have hw : (transitionEqStackCellSegment tm k).workspaceBase.eval seed.height =
      transitionEqPrefixWidth tm +
        cfgStackBitOffset tm (workHeight tm seed.height) k +
          (workHeight tm seed.height + 1) := by
    simpa only using congrArg (fun triple => triple.2.1) heval
  have hc : (transitionEqStackCellSegment tm k).count.eval seed.height =
      seed.height * ((reachableAlphabet tm k).card + 1) := by
    simpa only using congrArg (fun triple => triple.2.2) heval
  exact (transitionEqSegmentRows_eq_evaluated tm seed
    (transitionEqStackCellSegment tm k) _ _ _ hp hw hc hwork).trans
      (transitionEqSlotRows_eq_of_ranges tm seed
        (transitionEqStackCellSlots tm seed.height k) _ _ _
        (transitionEqStackCellSlots_publicValues tm seed.height k)
        (transitionEqStackCellSlots_workspaceValues tm seed.height k)).symm

private theorem transitionEqStackProgressionRows_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (positions : List (Fin (arithmeticStackCount tm)))
    (hwork : 0 < workHeight tm seed.height) :
    ((positions.flatMap fun position =>
        let k := (arithmeticStackEquiv tm).symm position
        [transitionEqStackHeightSegment tm k,
          transitionEqStackCellSegment tm k]).map
        (transitionEqSegmentProgression tm seed)).flatMap
          affineUnaryTripleProgressionRows =
      ((positions.map fun position =>
        transitionEqStackSlots tm seed.height
          ((arithmeticStackEquiv tm).symm position)).flatten).map
        (transitionEqSlotRow tm seed) := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
      let k := (arithmeticStackEquiv tm).symm position
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        List.map_nil, List.flatMap_append, List.flatMap_nil,
        List.flatten_cons]
      rw [transitionEqStackHeightProgressionRows_eq_slots tm seed k hwork,
        transitionEqStackCellProgressionRows_eq_slots tm seed k hwork,
        transitionEqStackSlots_eq_parts, List.map_append, ih]
      simp only [k, List.nil_append, List.append_assoc]

/-- All runtime progression rows are exactly the semantic rows attached to
the explicit public-slot enumeration. -/
theorem transitionEqProgressionRows_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    (transitionEqProgressions tm seed).flatMap
        affineUnaryTripleProgressionRows =
      (transitionEqPublicSlots tm seed.height).map
        (transitionEqSlotRow tm seed) := by
  unfold transitionEqProgressions transitionEqSegments
    transitionEqPublicSlots
  simp only [List.map_cons, List.flatMap_cons, List.map_append]
  rw [transitionEqPrefixProgressionRows_eq_slots tm seed hwork]
  apply congrArg
    (fun suffix =>
      (transitionEqPrefixSlots tm seed.height).map
          (transitionEqSlotRow tm seed) ++ suffix)
  exact transitionEqStackProgressionRows_eq_slots tm seed
    (arithmeticRuntimeStackSourceIndices tm) hwork

/-- Coordinate seed attached to one canonical public slot. -/
def transitionEqSlotSeed (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) (slot : CfgSlot tm seed.height) :
    AffineUnaryTripleSeed :=
  { first := transitionEqStart tm seed.height seed.start +
      6 * (cfgSlotEquivFin tm seed.height slot).val
    second := narrowCfgWireProjection
      (transitionDispatchOutputWires tm seed) slot
    third := seed.rowBase + cfgBitCount tm seed.height +
      (cfgSlotEquivFin tm seed.height slot).val }

/-- Generated coordinate seeds follow the explicit canonical slot list. -/
theorem transitionEqCoordinateSeeds_eq_slots
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionEqCoordinateSeeds tm seed =
      (transitionEqPublicSlots tm seed.height).map
        (transitionEqSlotSeed tm seed) := by
  unfold transitionEqCoordinateSeeds
  rw [← List.map_flatMap]
  rw [transitionEqProgressionRows_eq_slots tm seed hwork, List.map_map]
  rfl

/-- Equality frame attached to one canonical public slot. -/
def transitionEqSlotFrame (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) (slot : CfgSlot tm seed.height) :
    AffineEqFinPairFrame :=
  transitionEqCoordinateFrame (transitionEqSlotSeed tm seed slot)

/-- Generated equality frames follow the explicit canonical slot list. -/
theorem transitionEqGeneratedFrames_eq_slotFrames
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    transitionEqGeneratedFrames tm seed =
      (transitionEqPublicSlots tm seed.height).map
        (transitionEqSlotFrame tm seed) := by
  unfold transitionEqGeneratedFrames transitionEqSlotFrame
  rw [transitionEqCoordinateSeeds_eq_slots tm seed hwork, List.map_map]
  rfl

end CLRS.Chapter34.Turing.CookLevin
