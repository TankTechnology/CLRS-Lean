import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.TargetBits
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.Semantics

/-!
# Exact item-field boundary for the SUBSET-SUM reduction machine

The numeric reduction has already fixed a stable item order.  This file
expresses every item value by its verified fixed-width bit construction and
then restores the public compact-record syntax.  Consequently the remaining
machine work is isolated to one function, `itemFields`: it no longer needs to
reason simultaneously about record syntax or the target field.
-/

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Canonical field syntax when the canonical binary payload is already
available. -/
def encodeCanonicalBitField (bits : List Bool) : List SubsetSumSym :=
  .numberMark :: bits.map .bit ++ [.fieldEnd]

@[simp] theorem encodeCanonicalBitField_encodeBinaryNat (value : Nat) :
    encodeCanonicalBitField (encodeBinaryNat value) = encodeTSPField value :=
  rfl

/-- Bit payload of every generated item in the stable reduction order. -/
def itemBitPayloads (formula : CNF) : List (List Bool) :=
  (reductionItemList formula).map (reductionItemBits formula)

/-- Complete compact fields for every generated item. -/
def itemFields (formula : CNF) : List SubsetSumSym :=
  (itemBitPayloads formula).flatMap encodeCanonicalBitField

/-- The item payloads split into the two choice families followed by the
three slack families, exactly as prescribed by `reductionItemList`. -/
theorem itemBitPayloads_eq_families (formula : CNF) :
    itemBitPayloads formula =
      (List.range (reductionVariableCount formula)).map
          (fun index => reductionItemBits formula (.choice index false)) ++
      (List.range (reductionVariableCount formula)).map
          (fun index => reductionItemBits formula (.choice index true)) ++
      (List.range formula.length).map
          (fun clause => reductionItemBits formula (.slack clause 0)) ++
      (List.range formula.length).map
          (fun clause => reductionItemBits formula (.slack clause 1)) ++
      (List.range formula.length).map
          (fun clause => reductionItemBits formula (.slack clause 2)) := by
  simp [itemBitPayloads, reductionItemList, variableItemList, slackItemList,
    List.map_append, List.append_assoc, Function.comp_def]

/-- On the source language's three-CNF branch, every constructed payload is
the public canonical binary encoding of the corresponding mathematical item
value. -/
theorem itemBitPayloads_eq_values {formula : CNF}
    (hthree : IsThreeCNF formula) :
    itemBitPayloads formula =
      (cnfToSubsetSumData formula).values.map encodeBinaryNat := by
  unfold itemBitPayloads cnfToSubsetSumData
    SubsetSumInstance.toDataFromList
  simp only [cnfToSubsetSum, List.map_map]
  apply List.map_congr_left
  intro item hitem
  exact reductionItemBits_eq hthree item

/-- The complete item-field suffix agrees byte-for-byte with the public
compact-number serializer. -/
theorem itemFields_eq {formula : CNF} (hthree : IsThreeCNF formula) :
    itemFields formula =
      encodeTSPFields (cnfToSubsetSumData formula).values := by
  rw [itemFields, itemBitPayloads_eq_values hthree]
  simp only [encodeTSPFields, List.flatMap_map]
  apply List.flatMap_congr
  intro value hvalue
  exact encodeCanonicalBitField_encodeBinaryNat value

/-- Machine-facing typed record assembled from the already generated target
and the isolated item-field suffix. -/
def typedRecord (formula : CNF) : List SubsetSumSym :=
  .instanceMark ::
    (encodeCanonicalBitField (reductionTargetBits formula) ++
      itemFields formula ++ [.recordEnd])

/-- The assembled record is exactly the public serialized reduction on every
three-CNF formula. -/
theorem typedRecord_eq {formula : CNF} (hthree : IsThreeCNF formula) :
    typedRecord formula = encodeCnfToSubsetSum formula := by
  rw [typedRecord, reductionTargetBits_eq, itemFields_eq hthree]
  simp [encodeCnfToSubsetSum, encodeSubsetSumData, cnfToSubsetSumData,
    SubsetSumInstance.toDataFromList, cnfToSubsetSum, encodeTSPFields,
    List.append_assoc]

end CLRS.Chapter34.Turing.SubsetSumReduction
