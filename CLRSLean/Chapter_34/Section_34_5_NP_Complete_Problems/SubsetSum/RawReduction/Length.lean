import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.Construction
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.NumericBounds
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Length

/-! # Polynomial output-length bound for 3-CNF to SUBSET-SUM -/

namespace CLRS.Chapter34.SubsetSumReduction

/-- A list of compact fields with uniformly bounded binary sizes has the
expected linear aggregate encoding bound. -/
theorem encodeTSPFields_length_le_of_size_le
    (values : List Nat) (bound : Nat)
    (hsize : ∀ value ∈ values, Nat.size value ≤ bound) :
    (encodeTSPFields values).length ≤ values.length * (bound + 3) := by
  rw [encodeTSPFields_length]
  induction values with
  | nil => simp
  | cons value values ih =>
      have hhead : (encodeBinaryNat value).length + 2 ≤ bound + 3 := by
        have hbinary := encodeBinaryNat_length_le value
        have := hsize value (by simp)
        omega
      have htail := ih (fun tail htail => hsize tail (by simp [htail]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      calc
        (encodeBinaryNat value).length + 2 +
            (values.map (fun value =>
              (encodeBinaryNat value).length + 2)).sum ≤
            (bound + 3) + values.length * (bound + 3) :=
          Nat.add_le_add hhead htail
        _ = (values.length + 1) * (bound + 3) := by ring

/-- Formula-relative length bound before replacing decoded dimensions by the
raw source length. -/
theorem encodeCnfToSubsetSum_length_le_formula {formula : CNF}
    (hthree : IsThreeCNF formula) :
    (encodeCnfToSubsetSum formula).length ≤
      ((reductionItemList formula).length + 1) *
          (reductionBlockWidth formula * reductionWidth formula + 3) + 2 := by
  rw [encodeCnfToSubsetSum, encodeSubsetSumData_length]
  change (encodeTSPFields
      (reductionTarget formula ::
        (reductionItemList formula).map (itemValue formula))).length + 2 ≤ _
  apply Nat.add_le_add_right
  have hfields := encodeTSPFields_length_le_of_size_le
    (reductionTarget formula ::
      (reductionItemList formula).map (itemValue formula))
    (reductionBlockWidth formula * reductionWidth formula) (by
      intro value hvalue
      simp only [List.mem_cons, List.mem_map] at hvalue
      rcases hvalue with rfl | ⟨item, _, rfl⟩
      · exact reductionTarget_size_le formula
      · exact itemValue_size_le hthree item)
  simpa using hfields

/-- Explicit cubic bound used by the total raw reduction. -/
def subsetSumReductionLengthBound (inputLength : Nat) : Nat :=
  (5 * inputLength + 1) *
      ((5 * inputLength + 3) * (2 * inputLength) + 3) + 2

theorem encodeCnfToSubsetSum_length_le_input
    (input : List CNFSym) (hthree : IsThreeCNF (decodeCNF input)) :
    (encodeCnfToSubsetSum (decodeCNF input)).length ≤
      subsetSumReductionLengthBound input.length := by
  let formula := decodeCNF input
  have hvariables : reductionVariableCount formula ≤ input.length :=
    reductionVariableCount_decodeCNF_le input
  have hclauses : formula.length ≤ input.length :=
    decodeCNF_length_le input
  have hitems : (reductionItemList formula).length ≤
      5 * input.length := by
    rw [reductionItemList_length]
    omega
  have hblockWidth : reductionBlockWidth formula ≤
      5 * input.length + 3 := by
    rw [reductionBlockWidth_eq]
    omega
  have hwidth : reductionWidth formula ≤ 2 * input.length := by
    rw [reductionWidth]
    omega
  calc
    (encodeCnfToSubsetSum formula).length ≤
        ((reductionItemList formula).length + 1) *
            (reductionBlockWidth formula * reductionWidth formula + 3) + 2 :=
      encodeCnfToSubsetSum_length_le_formula hthree
    _ ≤ (5 * input.length + 1) *
          ((5 * input.length + 3) * (2 * input.length) + 3) + 2 := by
      apply Nat.add_le_add_right
      exact Nat.mul_le_mul
        (Nat.add_le_add_right hitems 1)
        (Nat.add_le_add_right (Nat.mul_le_mul hblockWidth hwidth) 3)
    _ = subsetSumReductionLengthBound input.length := rfl

/-- Every raw input, including malformed or non-3-CNF strings, produces an
output whose physical length is bounded by one fixed cubic expression. -/
theorem rawThreeCNFToSubsetSum_length_le (input : List CNFSym) :
    (rawThreeCNFToSubsetSum input).length ≤
      subsetSumReductionLengthBound input.length := by
  by_cases hthree : IsThreeCNF (decodeCNF input)
  · rw [rawThreeCNFToSubsetSum, if_pos hthree]
    exact encodeCnfToSubsetSum_length_le_input input hthree
  · rw [rawThreeCNFToSubsetSum, if_neg hthree]
    have hno : (encodeSubsetSumData subsetSumNoData).length = 5 := by
      rfl
    rw [hno]
    change 5 ≤ (5 * input.length + 1) *
        ((5 * input.length + 3) * (2 * input.length) + 3) + 2
    have hproduct : 1 * 3 ≤ (5 * input.length + 1) *
        ((5 * input.length + 3) * (2 * input.length) + 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

end CLRS.Chapter34.SubsetSumReduction
