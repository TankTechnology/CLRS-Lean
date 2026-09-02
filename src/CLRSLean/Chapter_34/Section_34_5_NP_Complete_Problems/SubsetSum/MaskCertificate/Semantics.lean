import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.MaskCertificate.FiniteSelection
import Mathlib.Tactic

/-! # Equivalence of index-list and Boolean-mask SUBSET-SUM certificates -/

namespace CLRS.Chapter34

private def finIndices (data : SubsetSumData) (indices : List Nat)
    (hrange : ∀ index ∈ indices, index < data.values.length) :
    List (Fin data.values.length) :=
  indices.attach.map fun index => ⟨index.1, hrange index.1 index.2⟩

private theorem finIndices_nodup (data : SubsetSumData)
    {indices : List Nat} (hnodup : indices.Nodup)
    (hrange : ∀ index ∈ indices, index < data.values.length) :
    (finIndices data indices hrange).Nodup := by
  apply hnodup.attach.map_on
  intro left _ right _ heq
  exact Subtype.ext (Fin.ext_iff.mp heq)

private theorem finIndices_sum (data : SubsetSumData)
    (indices : List Nat)
    (hrange : ∀ index ∈ indices, index < data.values.length) :
    ((finIndices data indices hrange).map fun index =>
      data.values.get index).sum = data.selectedSum indices := by
  simp only [finIndices, List.map_map, SubsetSumData.selectedSum]
  rw [← List.attach_map_val (l := indices)
    (f := fun index => data.values.getD index 0)]
  apply congrArg List.sum
  apply List.map_congr_left
  rintro ⟨index, hindex⟩ _
  rw [List.getD_eq_getElem _ _ (hrange index hindex)]
  rfl

private noncomputable def indicesOfFinset {values : List Nat}
    (chosen : Finset (Fin values.length)) : List Nat :=
  chosen.toList.map Fin.val

private theorem indicesOfFinset_nodup {values : List Nat}
    (chosen : Finset (Fin values.length)) :
    (indicesOfFinset chosen).Nodup := by
  exact chosen.nodup_toList.map_on fun _ _ _ _ heq => Fin.ext heq

private theorem indicesOfFinset_range {values : List Nat}
    (chosen : Finset (Fin values.length)) :
    ∀ index ∈ indicesOfFinset chosen, index < values.length := by
  intro index hindex
  rcases List.mem_map.1 hindex with ⟨finiteIndex, _, rfl⟩
  exact finiteIndex.isLt

private theorem indicesOfFinset_sum (data : SubsetSumData)
    (chosen : Finset (Fin data.values.length)) :
    data.selectedSum (indicesOfFinset chosen) =
      ∑ index ∈ chosen, data.values.get index := by
  rw [SubsetSumData.selectedSum, indicesOfFinset, List.map_map]
  change
    (chosen.toList.map fun index =>
      data.values.getD index.val 0).sum = _
  have hmap :
      (chosen.toList.map fun index =>
          data.values.getD index.val 0) =
        chosen.toList.map fun index => data.values.get index := by
    apply List.map_congr_left
    intro index _
    rw [List.getD_eq_getElem _ _ index.isLt]
    rfl
  rw [hmap]
  simpa using
    (List.sum_toFinset (fun index : Fin data.values.length =>
      data.values.get index) chosen.nodup_toList).symm

theorem hasSubsetSum_iff_exists_finset (data : SubsetSumData) :
    data.HasSubsetSum ↔
      ∃ chosen : Finset (Fin data.values.length),
        (∑ index ∈ chosen, data.values.get index) = data.target := by
  constructor
  · rintro ⟨indices, hnodup, hrange, hsum⟩
    let finiteIndices := finIndices data indices hrange
    refine ⟨finiteIndices.toFinset, ?_⟩
    rw [List.sum_toFinset (fun index : Fin data.values.length =>
      data.values.get index) (finIndices_nodup data hnodup hrange)]
    rw [finIndices_sum data indices hrange]
    exact hsum
  · rintro ⟨chosen, hsum⟩
    refine ⟨indicesOfFinset chosen, indicesOfFinset_nodup chosen,
      indicesOfFinset_range chosen, ?_⟩
    rw [indicesOfFinset_sum]
    exact hsum

/-- Boolean masks and duplicate-free in-range index lists express exactly the
same SUBSET-SUM witnesses. -/
theorem hasSubsetSum_iff_exists_mask (data : SubsetSumData) :
    data.HasSubsetSum ↔ ∃ mask, data.MaskSumsTo mask := by
  rw [hasSubsetSum_iff_exists_finset]
  constructor
  · rintro ⟨chosen, hsum⟩
    refine ⟨subsetMaskOfFinset chosen, ?_⟩
    rw [SubsetSumData.MaskSumsTo, subsetSumMaskOfFinset_sum]
    exact hsum
  · rintro ⟨mask, hsum⟩
    let keep : Fin data.values.length → Bool := fun index =>
      mask.getD index.val false
    let chosen : Finset (Fin data.values.length) :=
      Finset.univ.filter fun index => keep index
    refine ⟨chosen, ?_⟩
    have hmask : subsetSumMaskValues mask data.values =
        subsetSumMaskValues (List.ofFn keep) data.values := by
      exact selectListByBool_eq_canonicalMask mask data.values
    rw [SubsetSumData.MaskSumsTo, hmask] at hsum
    have hchosenMask : subsetMaskOfFinset chosen = List.ofFn keep := by
      simp [subsetMaskOfFinset, chosen]
    have hselected := subsetSumMaskOfFinset_sum chosen
    rw [hchosenMask] at hselected
    rw [← hselected]
    exact hsum

end CLRS.Chapter34
