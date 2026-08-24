import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Language

/-! # Raw SUBSET-SUM certificate checker -/

namespace CLRS.Chapter34

/-- Total Boolean checker for duplicate-free, in-range selected indices with
the exact requested sum. -/
def subsetSumVerifier
    (certificate input : List SubsetSumSym) : Bool :=
  match decodeSubsetSumData input,
      decodeSubsetSumCertificate certificate with
  | some data, some indices =>
      decide (indices.Nodup ∧
        (∀ index ∈ indices, index < data.values.length) ∧
        data.selectedSum indices = data.target)
  | _, _ => false

end CLRS.Chapter34
