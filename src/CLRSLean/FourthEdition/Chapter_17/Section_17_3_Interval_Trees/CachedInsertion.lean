import CLRSLean.FourthEdition.Chapter_17.Section_17_3_Interval_Trees
import CLRSLean.FourthEdition.Chapter_17.Section_17_2_Augmenting_Data_Structures.Execution

/-! # Interval search after the counted cached-field insertion -/
namespace CLRS.Chapter14

/-- The counted cached-field insertion inherits complete post-insert search semantics. -/
theorem intervalSearch_cachedInsert_spec (q query : Interval) {t : AugmentedRBTree Interval Nat}
    (hB : IntervalTree.IsBST (AugmentedRBTree.toIntervalTree t))
    (hW : AugmentedRBTree.WellAugmented IntervalTree.maxHighAug t) :
    let run := AugmentationExecution.insert IntervalTree.maxHighAug AugmentedRBTree.intervalLt q t
    let updated := AugmentedRBTree.toIntervalTree run.tree
    (IntervalTree.intervalSearch? updated query = none ↔
      ¬ (Interval.overlaps q query = true ∨ IntervalTree.hasOverlap (AugmentedRBTree.toIntervalTree t) query)) ∧
    (∀ i, IntervalTree.intervalSearch? updated query = some i →
      (i = q ∨ i ∈ AugmentedRBTree.keys t) ∧ Interval.overlaps i query = true) := by
  dsimp only
  rw [AugmentationExecution.insert_refines _ _ _ _ hW]
  exact intervalSearch_insert_spec q query hB hW

end CLRS.Chapter14
