import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Basic

/-!
# Enumerating finite SUBSET-SUM instances

The typed reduction uses stable item labels, whereas the public serialized
language uses list positions.  This file fixes the canonical enumeration that
connects those two representations.
-/

namespace CLRS.Chapter34
namespace SubsetSumInstance

/-- Forget the labels after recording their values in an explicit item order. -/
def toDataFromList (I : SubsetSumInstance)
    (items : List SubsetSumItem) : SubsetSumData where
  target := I.target
  values := items.map I.value

/-- Item represented by an in-range serialized certificate index. -/
def itemAtFromList (items : List SubsetSumItem)
    (index : Nat) : SubsetSumItem :=
  items.getD index (.choice 0 false)

/-- Translate serialized indices back to their stable item labels. -/
def selectedItemsFromList (items : List SubsetSumItem)
    (indices : List Nat) : List SubsetSumItem :=
  indices.map (itemAtFromList items)

/-- Translate a finite family of stable labels to canonical list positions. -/
noncomputable def chosenIndicesFromList (items : List SubsetSumItem)
    (chosen : Finset SubsetSumItem) : List Nat :=
  chosen.toList.map (fun item => items.idxOf item)

end SubsetSumInstance
end CLRS.Chapter34
