import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.ItemList
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Bridge
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Parser

/-! # Computable serialized SUBSET-SUM construction from 3-CNF -/

namespace CLRS.Chapter34.SubsetSumReduction

local instance (formula : CNF) : Decidable (IsThreeCNF formula) := by
  unfold IsThreeCNF
  infer_instance

/-- Proof-free list data produced by the textbook numeric construction. -/
def cnfToSubsetSumData (formula : CNF) : SubsetSumData :=
  (cnfToSubsetSum formula).toDataFromList (reductionItemList formula)

/-- Canonical serialized target for a decoded 3-CNF formula. -/
def encodeCnfToSubsetSum (formula : CNF) : List SubsetSumSym :=
  encodeSubsetSumData (cnfToSubsetSumData formula)

/-- A fixed no-instance used for source strings that are not 3-CNF. -/
def subsetSumNoData : SubsetSumData where
  target := 1
  values := []

/-- Total raw reduction function from the project's 3-CNF alphabet. -/
def rawThreeCNFToSubsetSum (input : List CNFSym) : List SubsetSumSym :=
  let formula := decodeCNF input
  if IsThreeCNF formula then
    encodeCnfToSubsetSum formula
  else
    encodeSubsetSumData subsetSumNoData

end CLRS.Chapter34.SubsetSumReduction
