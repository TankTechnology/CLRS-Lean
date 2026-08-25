import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ItemFields
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.ReductionMachine.Codec
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Fixed-machine formatting of the SUBSET-SUM target field

The target payload is already generated from raw CNF syntax.  This file adds
the public compact-number delimiters with fixed transducers and proves the
result is the exact first numeric field of the textbook reduction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Relabel the canonical Boolean target payload into public record symbols. -/
def targetBitSymbols (input : List CNFSym) : List SubsetSumSym :=
  (targetBits input).map .bit

/-- One constant output word generated after consuming the arbitrary source. -/
def constantSubsetSumWordSpec (word : List SubsetSumSym) :
    StatefulFlatMapSpec Unit CNFSym SubsetSumSym where
  initial := ()
  action _ _ := ([], ())
  finish _ := word

def constantSubsetSumWord (word : List SubsetSumSym)
    (input : List CNFSym) : List SubsetSumSym :=
  rewriteStatefulFlatMap (constantSubsetSumWordSpec word) input

theorem constantSubsetSumWord_eq (word : List SubsetSumSym)
    (input : List CNFSym) :
    constantSubsetSumWord word input = word := by
  induction input with
  | nil => rfl
  | cons symbol input ih =>
      change rewriteStatefulFlatMapFrom (constantSubsetSumWordSpec word) ()
        input = word
      simpa [constantSubsetSumWord, rewriteStatefulFlatMap] using ih

/-- Public target field generated from arbitrary raw CNF syntax. -/
def targetField (input : List CNFSym) : List SubsetSumSym :=
  [.numberMark] ++ targetBitSymbols input ++ [.fieldEnd]

theorem targetField_eq (input : List CNFSym) :
    targetField input =
      encodeTSPField (reductionTarget (decodeCNF input)) := by
  rw [targetField, targetBitSymbols, targetBits_eq,
    reductionTargetBits_eq]
  rfl

noncomputable def targetBitSymbols_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetBitSymbols := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      targetBits_computableInPolyTime
      (listMap_computableInPolyTime TSPSym.bit)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => (targetBits input).map TSPSym.bit)
  simpa [Function.comp_def] using Classical.choice composed

noncomputable def constantSubsetSumWord_computableInPolyTime
    (word : List SubsetSumSym) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (constantSubsetSumWord word) :=
  statefulFlatMap_computableInPolyTime (constantSubsetSumWordSpec word)

private noncomputable def targetFieldPrefix_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym => [.numberMark] ++ targetBitSymbols input) := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    (constantSubsetSumWord_computableInPolyTime [.numberMark])
    targetBitSymbols_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [constantSubsetSumWord_eq] at output
        simpa using output }

/-- One fixed polynomial-time TM2 emits the exact canonical target field from
every raw CNF input. -/
noncomputable def targetField_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id targetField := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    targetFieldPrefix_computableInPolyTime
    (constantSubsetSumWord_computableInPolyTime [.fieldEnd])
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [constantSubsetSumWord_eq] at output
        simpa [targetField, List.append_assoc] using output }

end CLRS.Chapter34.Turing.SubsetSumReduction
