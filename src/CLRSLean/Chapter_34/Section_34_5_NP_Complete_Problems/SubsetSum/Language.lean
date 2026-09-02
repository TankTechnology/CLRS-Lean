import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-! # Honest serialized SUBSET-SUM language -/

namespace CLRS.Chapter34

/-- Raw compact SUBSET-SUM strings whose decoded indexed values admit an exact
target subfamily. -/
def GeneralSUBSETSUM : Language SubsetSumSym :=
  { input | ∃ data,
      decodeSubsetSumData input = some data ∧ data.HasSubsetSum }

/-- Textbook public name for the honest raw language. -/
abbrev SUBSETSUM : Language SubsetSumSym := GeneralSUBSETSUM

theorem encodeSubsetSumData_mem_iff (data : SubsetSumData) :
    encodeSubsetSumData data ∈ GeneralSUBSETSUM ↔ data.HasSubsetSum := by
  constructor
  · rintro ⟨decoded, hdecode, hhas⟩
    have hEq : data = decoded :=
      Option.some.inj ((decode_encodeSubsetSumData data).symm.trans hdecode)
    simpa [hEq] using hhas
  · intro hhas
    exact ⟨data, decode_encodeSubsetSumData data, hhas⟩

end CLRS.Chapter34
