import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceFieldCore
import Mathlib.Tactic

/-!
# Choice fields: one-item simulation

This file proves the two local phases: collecting one little-endian segment in
reverse work-tape order, then streaming its canonical big-endian field.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

def choiceFieldScanSteps (bits : List Bool) : Nat := 2 * bits.length + 1

private def choiceField_scan_run (bits : List Bool)
    (tail : List ChoiceBlockSym) (output : List SubsetSumSym)
    (work₁ work₂ : List ChoiceBlockSym)
    (buffer₁ buffer₂ : Option ChoiceBlockSym) (test : Bool) :
    EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .scan buffer₁ buffer₂ test
        (bits.map .bit ++ .itemEnd :: tail) output work₁ work₂)
      (some (choiceFieldCfg .startField (some .itemEnd) buffer₂ test
        tail output ((bits.map ChoiceBlockSym.bit).reverse ++ work₁) work₂))
      (choiceFieldScanSteps bits) := by
  induction bits generalizing work₁ buffer₁ with
  | nil =>
      exact ⟨⟨1, rfl⟩, le_rfl⟩
  | cons bit bits ih =>
      let afterFirst := choiceFieldCfg .scan (some (.bit bit)) buffer₂ test
        (bits.map ChoiceBlockSym.bit ++ .itemEnd :: tail) output
        (.bit bit :: work₁) work₂
      have first : EvalsToInTime (step choiceFieldProgram)
          (choiceFieldCfg .scan buffer₁ buffer₂ test
            ((bit :: bits).map ChoiceBlockSym.bit ++ .itemEnd :: tail)
            output work₁ work₂)
          (some afterFirst) 2 := by
        exact ⟨⟨2, by
          simp [Function.iterate_succ_apply, flip, step, stepOp,
            choiceFieldProgram, choiceFieldCfg, afterFirst]⟩, le_rfl⟩
      have rest := ih (work₁ := .bit bit :: work₁)
        (buffer₁ := some (.bit bit))
      let full := EvalsToInTime.trans (step choiceFieldProgram)
        2 (choiceFieldScanSteps bits) _ afterFirst _ first rest
      convert full using 1
      · simp [List.reverse_cons, List.append_assoc]
      · simp [choiceFieldScanSteps]
        omega

def choiceFieldCanonSteps : Bool → List Bool → Nat
  | true, [] => 1
  | false, [] => 2
  | true, _ :: bits => 2 + choiceFieldCanonSteps true bits
  | false, false :: bits => 1 + choiceFieldCanonSteps false bits
  | false, true :: bits => 2 + choiceFieldCanonSteps true bits

private def canonicalOutput (started : Bool) (bits : List Bool) :
    List SubsetSumSym :=
  (rewriteStatefulFlatMapFrom binaryCanonicalizerSpec started bits).reverse.map
    .bit

private def choiceField_canon_run (started : Bool) (bits : List Bool)
    (input : List ChoiceBlockSym) (output : List SubsetSumSym)
    (work₂ : List ChoiceBlockSym)
    (buffer₁ buffer₂ : Option ChoiceBlockSym) (test : Bool) :
    EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg (.canon started) buffer₁ buffer₂ test input output
        (bits.map .bit) work₂)
      (some (choiceFieldCfg .finishField none buffer₂ test input
        (canonicalOutput started bits ++ output) [] work₂))
      (choiceFieldCanonSteps started bits) := by
  induction bits generalizing started output buffer₁ with
  | nil =>
      cases started <;>
        exact ⟨⟨_, by
          simp [Function.iterate_succ_apply, flip, step, stepOp,
            choiceFieldProgram, choiceFieldCfg,
            canonicalOutput, rewriteStatefulFlatMapFrom,
            binaryCanonicalizerSpec]⟩, le_rfl⟩
  | cons bit bits ih =>
      cases started with
      | false =>
          cases bit with
          | false =>
              let afterFirst := choiceFieldCfg (.canon false)
                (some (.bit false)) buffer₂ test input output
                (bits.map ChoiceBlockSym.bit) work₂
              have first : EvalsToInTime (step choiceFieldProgram)
                  (choiceFieldCfg (.canon false) buffer₁ buffer₂ test
                    input output ((false :: bits).map .bit) work₂)
                  (some afterFirst) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
              have rest := ih (started := false)
                (output := output)
                (buffer₁ := some (.bit false))
              let full := EvalsToInTime.trans (step choiceFieldProgram)
                1 (choiceFieldCanonSteps false bits) _ afterFirst _ first rest
              simpa [afterFirst, choiceFieldCanonSteps, canonicalOutput,
                rewriteStatefulFlatMapFrom, binaryCanonicalizerSpec,
                Nat.add_comm] using full
          | true =>
              let afterFirst := choiceFieldCfg (.canon true)
                (some (.bit true)) buffer₂ test input
                (.bit true :: output) (bits.map ChoiceBlockSym.bit) work₂
              have first : EvalsToInTime (step choiceFieldProgram)
                  (choiceFieldCfg (.canon false) buffer₁ buffer₂ test
                    input output ((true :: bits).map .bit) work₂)
                  (some afterFirst) 2 := by
                exact ⟨⟨2, by
                  simp [Function.iterate_succ_apply, flip, step, stepOp,
                    choiceFieldProgram, choiceFieldCfg, afterFirst]⟩, le_rfl⟩
              have rest := ih (started := true)
                (output := .bit true :: output)
                (buffer₁ := some (.bit true))
              let full := EvalsToInTime.trans (step choiceFieldProgram)
                2 (choiceFieldCanonSteps true bits) _ afterFirst _ first rest
              simpa [afterFirst, choiceFieldCanonSteps, canonicalOutput,
                rewriteStatefulFlatMapFrom, binaryCanonicalizerSpec,
                List.map_append, List.append_assoc, Nat.add_comm] using full
      | true =>
          let afterFirst := choiceFieldCfg (.canon true)
            (some (.bit bit)) buffer₂ test input
            (.bit bit :: output) (bits.map ChoiceBlockSym.bit) work₂
          have first : EvalsToInTime (step choiceFieldProgram)
              (choiceFieldCfg (.canon true) buffer₁ buffer₂ test
                input output ((bit :: bits).map .bit) work₂)
              (some afterFirst) 2 := by
            exact ⟨⟨2, by
              simp [Function.iterate_succ_apply, flip, step, stepOp,
                choiceFieldProgram, choiceFieldCfg, afterFirst]⟩, le_rfl⟩
          have rest := ih (started := true)
            (output := .bit bit :: output)
            (buffer₁ := some (.bit bit))
          let full := EvalsToInTime.trans (step choiceFieldProgram)
            2 (choiceFieldCanonSteps true bits) _ afterFirst _ first rest
          simpa [afterFirst, choiceFieldCanonSteps, canonicalOutput,
            rewriteStatefulFlatMapFrom, binaryCanonicalizerSpec,
            List.map_append, List.append_assoc, Nat.add_comm] using full

/-- Exact cost of one complete item field. -/
def choiceFieldItemSteps (bits : List Bool) : Nat :=
  choiceFieldScanSteps bits + 1 +
    choiceFieldCanonSteps false bits.reverse + 1

/-- One complete segment becomes one canonical public numeric field. -/
def choiceField_itemRun (bits : List Bool)
    (tail : List ChoiceBlockSym) (output : List SubsetSumSym)
    (buffer₁ buffer₂ : Option ChoiceBlockSym) (test : Bool) :
    EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .scan buffer₁ buffer₂ test
        (bits.map .bit ++ .itemEnd :: tail) output [] [])
      (some (choiceFieldCfg .scan none buffer₂ test tail
        ((choiceBitField bits).reverse ++ output) [] []))
      (choiceFieldItemSteps bits) := by
  have scan : EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .scan buffer₁ buffer₂ test
        (bits.map .bit ++ .itemEnd :: tail) output [] [])
      (some (choiceFieldCfg .startField (some .itemEnd) buffer₂ test
        tail output (bits.map ChoiceBlockSym.bit).reverse []))
      (choiceFieldScanSteps bits) := by
    simpa only [List.append_nil] using
      (choiceField_scan_run bits tail output [] []
        buffer₁ buffer₂ test)
  have start : EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .startField (some .itemEnd) buffer₂ test tail output
        (bits.map ChoiceBlockSym.bit).reverse [])
      (some (choiceFieldCfg (.canon false) (some .itemEnd) buffer₂ test
        tail (.numberMark :: output)
        (bits.map ChoiceBlockSym.bit).reverse [])) 1 :=
    ⟨⟨1, rfl⟩, le_rfl⟩
  have canon : EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg (.canon false) (some .itemEnd) buffer₂ test
        tail (.numberMark :: output)
        (bits.map ChoiceBlockSym.bit).reverse [])
      (some (choiceFieldCfg .finishField none buffer₂ test tail
        (canonicalOutput false bits.reverse ++ .numberMark :: output) [] []))
      (choiceFieldCanonSteps false bits.reverse) := by
    simpa only [List.map_reverse] using
      (choiceField_canon_run false bits.reverse tail
        (.numberMark :: output) [] (some .itemEnd) buffer₂ test)
  have finish : EvalsToInTime (step choiceFieldProgram)
      (choiceFieldCfg .finishField none buffer₂ test tail
        (canonicalOutput false bits.reverse ++ .numberMark :: output) [] [])
      (some (choiceFieldCfg .scan none buffer₂ test tail
        (.fieldEnd :: canonicalOutput false bits.reverse ++
          .numberMark :: output) [] [])) 1 := ⟨⟨1, rfl⟩, le_rfl⟩
  let throughStart := EvalsToInTime.trans (step choiceFieldProgram)
    (choiceFieldScanSteps bits) 1 _ _ _ scan start
  let throughCanon := EvalsToInTime.trans (step choiceFieldProgram)
    (1 + choiceFieldScanSteps bits)
    (choiceFieldCanonSteps false bits.reverse) _ _ _ throughStart canon
  let full := EvalsToInTime.trans (step choiceFieldProgram)
    (choiceFieldCanonSteps false bits.reverse +
      (1 + choiceFieldScanSteps bits)) 1 _ _ _ throughCanon finish
  simpa [choiceFieldItemSteps, choiceBitField, encodeCanonicalBitField,
    binaryCanonicalizer, binaryCanonicalizerSpec,
    rewriteStatefulFlatMap, canonicalOutput,
    List.reverse_append, List.map_reverse,
    List.append_assoc, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

end CLRS.Chapter34.Turing.SubsetSumReduction
