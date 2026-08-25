import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.GeneratedItemFields

/-!
# Complete generated SUBSET-SUM record

The independently generated target and item suffix are enclosed by the public
record markers.  This is the unguarded, valid-branch output used by the final
total raw reduction.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Target followed by every generated item field. -/
def generatedRecordBody (input : List CNFSym) : List SubsetSumSym :=
  targetField input ++ generatedItemFields input

/-- Complete public record generated from an arbitrary raw CNF word. -/
def generatedTypedRecord (input : List CNFSym) : List SubsetSumSym :=
  [.instanceMark] ++ generatedRecordBody input ++ [.recordEnd]

/-- On the source three-CNF branch, the generated record is byte-for-byte the
textbook serialized reduction. -/
theorem generatedTypedRecord_eq {input : List CNFSym}
    (hthree : IsThreeCNF (decodeCNF input)) :
    generatedTypedRecord input =
      encodeCnfToSubsetSum (decodeCNF input) := by
  rw [generatedTypedRecord, generatedRecordBody,
    generatedItemFields_eq hthree]
  rw [targetField, targetBitSymbols, targetBits_eq]
  change [.instanceMark] ++
      (encodeCanonicalBitField
        (reductionTargetBits (decodeCNF input)) ++
        itemFields (decodeCNF input)) ++ [.recordEnd] = _
  simpa [typedRecord, List.append_assoc] using
    typedRecord_eq hthree

private noncomputable def generatedRecordBody_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      generatedRecordBody :=
  fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    targetField_computableInPolyTime
    generatedItemFields_computableInPolyTime

private noncomputable def generatedRecordPrefix_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym =>
        [.instanceMark] ++ generatedRecordBody input) := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    (constantSubsetSumWord_computableInPolyTime [.instanceMark])
    generatedRecordBody_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [constantSubsetSumWord_eq] at output
        simpa using output }

/-- One fixed polynomial-time TM2 emits the complete valid-branch record. -/
noncomputable def generatedTypedRecord_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      generatedTypedRecord := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    generatedRecordPrefix_computableInPolyTime
    (constantSubsetSumWord_computableInPolyTime [.recordEnd])
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [constantSubsetSumWord_eq] at output
        simpa [generatedTypedRecord, List.append_assoc] using output }

end CLRS.Chapter34.Turing.SubsetSumReduction
