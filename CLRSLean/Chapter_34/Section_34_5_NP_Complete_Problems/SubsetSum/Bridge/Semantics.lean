import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Bridge.Construction

/-! # Exact semantic preservation of the finite-instance enumeration -/

namespace CLRS.Chapter34
namespace SubsetSumInstance

noncomputable section

theorem toDataFromList_value_at (I : SubsetSumInstance)
    (items : List SubsetSumItem) {index : Nat}
    (hindex : index < items.length) :
    (I.toDataFromList items).values.getD index 0 =
      I.value (itemAtFromList items index) := by
  change (items.map I.value).getD index 0 =
    I.value (items.getD index (.choice 0 false))
  have hmap : index < (items.map I.value).length := by simpa
  rw [List.getD_eq_getElem _ _ hmap,
    List.getD_eq_getElem _ _ hindex, List.getElem_map]

theorem itemAtFromList_mem_items (I : SubsetSumInstance)
    (items : List SubsetSumItem)
    (hmem : ∀ item, item ∈ items ↔ item ∈ I.items) {index : Nat}
    (hindex : index < items.length) :
    itemAtFromList items index ∈ I.items := by
  rw [itemAtFromList, List.getD_eq_getElem _ _ hindex]
  exact (hmem _).1 (List.getElem_mem hindex)

theorem itemAtFromList_injective_on_range (items : List SubsetSumItem)
    (hnodup : items.Nodup)
    {left right : Nat}
    (hleft : left < items.length) (hright : right < items.length)
    (heq : itemAtFromList items left = itemAtFromList items right) :
    left = right := by
  change items.getD left (.choice 0 false) =
    items.getD right (.choice 0 false) at heq
  rw [List.getD_eq_getElem _ _ hleft,
    List.getD_eq_getElem _ _ hright] at heq
  exact (List.getElem_inj hnodup).1 heq

theorem selectedItemsFromList_nodup (items : List SubsetSumItem)
    (hitemsNodup : items.Nodup)
    {indices : List Nat} (hnodup : indices.Nodup)
    (hrange : ∀ index ∈ indices, index < items.length) :
    (selectedItemsFromList items indices).Nodup := by
  exact hnodup.map_on (fun left hleft right hright heq =>
    itemAtFromList_injective_on_range items hitemsNodup
      (hrange left hleft) (hrange right hright) heq)

theorem selectedItemsFromList_sum (I : SubsetSumInstance)
    (items : List SubsetSumItem)
    {indices : List Nat}
    (hrange : ∀ index ∈ indices, index < items.length) :
    ((selectedItemsFromList items indices).map I.value).sum =
      (I.toDataFromList items).selectedSum indices := by
  simp only [selectedItemsFromList, SubsetSumData.selectedSum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro index hindex
  exact (toDataFromList_value_at I items (hrange index hindex)).symm

theorem chosenIndicesFromList_nodup (I : SubsetSumInstance)
    (items : List SubsetSumItem)
    (hmem : ∀ item, item ∈ items ↔ item ∈ I.items)
    {chosen : Finset SubsetSumItem} (hsubset : chosen ⊆ I.items) :
    (chosenIndicesFromList items chosen).Nodup := by
  apply (Finset.nodup_toList chosen).map_on
  intro left hleft right hright heq
  have hleftMem : left ∈ items :=
    (hmem left).2 (hsubset (Finset.mem_toList.1 hleft))
  have hrightMem : right ∈ items :=
    (hmem right).2 (hsubset (Finset.mem_toList.1 hright))
  exact (List.idxOf_inj hleftMem).1 heq

theorem chosenIndicesFromList_in_range (I : SubsetSumInstance)
    (items : List SubsetSumItem)
    (hmem : ∀ item, item ∈ items ↔ item ∈ I.items)
    {chosen : Finset SubsetSumItem} (hsubset : chosen ⊆ I.items) :
    ∀ index ∈ chosenIndicesFromList items chosen, index < items.length := by
  intro index hindex
  rcases List.mem_map.1 hindex with ⟨item, hitem, rfl⟩
  rw [List.idxOf_lt_length_iff]
  exact (hmem item).2
    (hsubset (Finset.mem_toList.1 hitem))

theorem chosenIndicesFromList_itemAt (I : SubsetSumInstance)
    (items : List SubsetSumItem)
    (hmem : ∀ item, item ∈ items ↔ item ∈ I.items)
    {item : SubsetSumItem} (hitem : item ∈ I.items) :
    itemAtFromList items (items.idxOf item) = item := by
  have hlist : item ∈ items := (hmem item).2 hitem
  rw [itemAtFromList, List.getD_eq_getElem _ _
    (List.idxOf_lt_length_iff.mpr hlist)]
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hlist)

theorem chosenIndicesFromList_sum (I : SubsetSumInstance)
    (items : List SubsetSumItem)
    (hmem : ∀ item, item ∈ items ↔ item ∈ I.items)
    {chosen : Finset SubsetSumItem} (hsubset : chosen ⊆ I.items) :
    (I.toDataFromList items).selectedSum
        (chosenIndicesFromList items chosen) =
      ∑ item ∈ chosen, I.value item := by
  have hitems : selectedItemsFromList items
      (chosenIndicesFromList items chosen) =
      chosen.toList := by
    simp only [selectedItemsFromList, chosenIndicesFromList, List.map_map]
    calc
      List.map (itemAtFromList items ∘ fun item => items.idxOf item)
          chosen.toList = List.map id chosen.toList := by
        apply List.map_congr_left
        intro item hitem
        exact chosenIndicesFromList_itemAt I items hmem
          (hsubset (Finset.mem_toList.1 hitem))
      _ = chosen.toList := List.map_id _
  calc
    (I.toDataFromList items).selectedSum
        (chosenIndicesFromList items chosen) =
        ((selectedItemsFromList items
          (chosenIndicesFromList items chosen)).map I.value).sum :=
      (selectedItemsFromList_sum I items
        (chosenIndicesFromList_in_range I items hmem hsubset)).symm
    _ = (chosen.toList.map I.value).sum := by rw [hitems]
    _ = ∑ item ∈ chosen, I.value item := by
      simpa using
        (List.sum_toFinset I.value (Finset.nodup_toList chosen)).symm

/-- The canonical list enumeration preserves SUBSET-SUM semantics exactly,
including distinct copies that happen to carry equal numerical values. -/
theorem toDataFromList_hasSubsetSum_iff (I : SubsetSumInstance)
    (items : List SubsetSumItem) (hitemsNodup : items.Nodup)
    (hmem : ∀ item, item ∈ items ↔ item ∈ I.items) :
    (I.toDataFromList items).HasSubsetSum ↔ I.HasSubsetSum := by
  constructor
  · rintro ⟨indices, hnodup, hrange, hsum⟩
    have hrangeItems : ∀ index ∈ indices, index < items.length := by
      simpa [toDataFromList] using hrange
    let chosen := (selectedItemsFromList items indices).toFinset
    refine ⟨chosen, ?_, ?_⟩
    · intro item hitem
      simp only [chosen, List.mem_toFinset] at hitem
      rcases List.mem_map.1 hitem with ⟨index, hindex, rfl⟩
      exact itemAtFromList_mem_items I items hmem
        (hrangeItems index hindex)
    · have hselectedNodup :=
        selectedItemsFromList_nodup items hitemsNodup hnodup hrangeItems
      change ∑ item ∈ (selectedItemsFromList items indices).toFinset,
        I.value item = I.target
      rw [List.sum_toFinset I.value hselectedNodup]
      rw [selectedItemsFromList_sum I items hrangeItems]
      simpa [toDataFromList] using hsum
  · rintro ⟨chosen, hsubset, hsum⟩
    refine ⟨chosenIndicesFromList items chosen,
      chosenIndicesFromList_nodup I items hmem hsubset, ?_, ?_⟩
    · simpa [toDataFromList] using
        chosenIndicesFromList_in_range I items hmem hsubset
    rw [chosenIndicesFromList_sum I items hmem hsubset]
    simpa [toDataFromList] using hsum

end
end SubsetSumInstance
end CLRS.Chapter34
