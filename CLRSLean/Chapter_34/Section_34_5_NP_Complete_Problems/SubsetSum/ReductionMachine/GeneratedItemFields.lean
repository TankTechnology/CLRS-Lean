import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceFieldRuntime
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.SlackFields

/-!
# Complete generated SUBSET-SUM item fields

The two choice families and three slack families are joined in the stable
textbook order and identified with the public `itemFields` abstraction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- The two polarity-indexed choice families. -/
def generatedChoiceFields (input : List CNFSym) : List SubsetSumSym :=
  choiceGeneratedFields false input ++ choiceGeneratedFields true input

/-- Both choice families agree with the first two public item families. -/
theorem generatedChoiceFields_eq_items {input : List CNFSym}
    (hthree : IsThreeCNF (decodeCNF input)) :
    generatedChoiceFields input =
      (List.range (reductionVariableCount (decodeCNF input))).flatMap
        (fun index => encodeCanonicalBitField
          (reductionItemBits (decodeCNF input) (.choice index false))) ++
      (List.range (reductionVariableCount (decodeCNF input))).flatMap
        (fun index => encodeCanonicalBitField
          (reductionItemBits (decodeCNF input) (.choice index true))) := by
  unfold generatedChoiceFields
  rw [choiceGeneratedFields_eq_items hthree false,
    choiceGeneratedFields_eq_items hthree true]

/-- A fixed polynomial-time TM2 emits both choice families. -/
noncomputable def generatedChoiceFields_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      generatedChoiceFields :=
  fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    (choiceGeneratedFields_computableInPolyTime false)
    (choiceGeneratedFields_computableInPolyTime true)

/-- All generated item fields in the public reduction order. -/
def generatedItemFields (input : List CNFSym) : List SubsetSumSym :=
  generatedChoiceFields input ++ slackFields input

/-- On the source language, the generated suffix is exactly `itemFields`. -/
theorem generatedItemFields_eq {input : List CNFSym}
    (hthree : IsThreeCNF (decodeCNF input)) :
    generatedItemFields input = itemFields (decodeCNF input) := by
  rw [generatedItemFields, generatedChoiceFields_eq_items hthree,
    slackFields_eq_items input hthree, itemFields,
    itemBitPayloads_eq_families]
  simp only [List.flatMap_append, List.flatMap_map]
  simp [List.append_assoc]

/-- A fixed polynomial-time TM2 emits the complete item-field suffix. -/
noncomputable def generatedItemFields_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      generatedItemFields :=
  fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    generatedChoiceFields_computableInPolyTime
    slackFields_computableInPolyTime

end CLRS.Chapter34.Turing.SubsetSumReduction
