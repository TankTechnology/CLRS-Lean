import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Costs.Span.WitnessInput

/-!
# CLRS Chapter 27.3 — Order-Embedding Cost Invariance

Strictly monotone key transformations preserve every comparison made by
binary lower bound, P-MERGE, and P-MERGE-SORT.  Consequently they preserve
the attached work and span while mapping only the returned values.
-/

namespace CLRS
namespace Chapter27

namespace ParallelMergeSort
namespace Costs
namespace Span

variable [LinearOrder α] [LinearOrder β]

private theorem loop_map (f : α → β) (hf : StrictMono f)
    (xs : List α) (pivot : α) (lo hi : ℕ) :
    ParallelMerge.Internal.loop (xs.map f) (f pivot) lo hi =
      Costed.map id (ParallelMerge.Internal.loop xs pivot lo hi) := by
  induction lo, hi using ParallelMerge.Internal.loop.induct xs with
  | case1 lo hi hlt mid hnone =>
      rw [ParallelMerge.Internal.loop, ParallelMerge.Internal.loop]
      simp only [hlt, if_true, mid, List.getElem?_map,
        hnone, Option.map_none]
      rfl
  | case2 lo hi hlt mid x hget ihRight ihLeft =>
      rw [ParallelMerge.Internal.loop, ParallelMerge.Internal.loop]
      simp only [hlt, if_true, mid, List.getElem?_map,
        hget, Option.map_some, Costed.seq, Costed.charge, Costed.map]
      by_cases hx : x < pivot
      · have hfx : f x < f pivot := hf hx
        simp only [hx, hfx, if_true]
        rw [ihRight]
        rfl
      · have hfx : ¬ f x < f pivot := by
          intro hcontra
          exact hx (hf.lt_iff_lt.mp hcontra)
        simp only [hx, hfx, if_false]
        rw [ihLeft]
        rfl
  | case3 lo hi hnlt =>
      rw [ParallelMerge.Internal.loop, ParallelMerge.Internal.loop]
      simp [hnlt, Costed.pure, Costed.map]

private theorem binaryLowerBound_map (f : α → β) (hf : StrictMono f)
    (xs : List α) (pivot : α) :
    binaryLowerBound (xs.map f) (f pivot) =
      Costed.map id (binaryLowerBound xs pivot) := by
  simpa [binaryLowerBound] using loop_map f hf xs pivot 0 xs.length

private theorem mergeSplit_map_data (f : α → β) (hf : StrictMono f)
    (xs ys : List α) (htotal : 0 < xs.length + ys.length) :
    let S := mergeSplit xs ys htotal
    let T := mergeSplit (xs.map f) (ys.map f) (by simpa using htotal)
    T.search = Costed.map id S.search ∧
      T.lowerPrimary = S.lowerPrimary.map f ∧
      T.lowerSecondary = S.lowerSecondary.map f ∧
      T.upperPrimary = S.upperPrimary.map f ∧
      T.upperSecondary = S.upperSecondary.map f ∧
      T.pivot = f S.pivot := by
  dsimp only
  by_cases hxy : xs.length < ys.length
  · simp [mergeSplit, hxy, binaryLowerBound_map f hf,
      MergeSplit.lowerPrimary, MergeSplit.lowerSecondary,
      MergeSplit.upperPrimary, MergeSplit.upperSecondary,
      MergeSplit.pivotIndex, MergeSplit.splitIndex,
      List.map_take, List.map_drop]
  · simp [mergeSplit, hxy, binaryLowerBound_map f hf,
      MergeSplit.lowerPrimary, MergeSplit.lowerSecondary,
      MergeSplit.upperPrimary, MergeSplit.upperSecondary,
      MergeSplit.pivotIndex, MergeSplit.splitIndex,
      List.map_take, List.map_drop]

private theorem pMerge_map (f : α → β) (hf : StrictMono f) (n : ℕ) :
    ∀ (xs ys : List α), xs.length + ys.length = n →
      pMerge (xs.map f) (ys.map f) =
        Costed.map (List.map f) (pMerge xs ys) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs ys htotal
      by_cases hzero : xs.length + ys.length = 0
      · rw [pMerge, pMerge]
        simp [hzero, Costed.pure, Costed.map]
      · let S := mergeSplit xs ys (Nat.pos_of_ne_zero hzero)
        let T := mergeSplit (xs.map f) (ys.map f) (by
          simpa using (Nat.pos_of_ne_zero hzero))
        obtain ⟨hsearch, hlowerP, hlowerS, hupperP, hupperS, hpivot⟩ :=
          mergeSplit_map_data f hf xs ys (Nat.pos_of_ne_zero hzero)
        have hleft_lt : S.leftSize < n := by
          calc
            S.leftSize < S.totalSize := S.leftSize_lt
            _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have hright_lt : S.rightSize < n := by
          calc
            S.rightSize < S.totalSize := S.rightSize_lt
            _ = xs.length + ys.length := by simp [S, MergeSplit.totalSize]
            _ = n := htotal
        have ihlower := ih S.leftSize hleft_lt
          S.lowerPrimary S.lowerSecondary rfl
        have ihupper := ih S.rightSize hright_lt
          S.upperPrimary S.upperSecondary rfl
        rw [pMerge, pMerge]
        simp only [List.length_map, hzero]
        change Costed.seq T.search (fun _ =>
            Costed.seq
              (Costed.par (pMerge T.lowerPrimary T.lowerSecondary)
                (pMerge T.upperPrimary T.upperSecondary))
              (fun parts => Costed.charge 1 1
                (parts.1 ++ T.pivot :: parts.2))) =
          Costed.map (List.map f)
            (Costed.seq S.search (fun _ =>
              Costed.seq
                (Costed.par (pMerge S.lowerPrimary S.lowerSecondary)
                  (pMerge S.upperPrimary S.upperSecondary))
                (fun parts => Costed.charge 1 1
                  (parts.1 ++ S.pivot :: parts.2))))
        rw [hsearch, hlowerP, hlowerS, hupperP, hupperS, hpivot,
          ihlower, ihupper]
        simp [Costed.seq, Costed.par, Costed.charge, Costed.map, S]

/-- P-MERGE-SORT's complete cost annotation is invariant under a strict order
embedding; only its returned list is mapped. -/
theorem pMergeSort_map (f : α → β) (hf : StrictMono f) (n : ℕ) :
    ∀ (xs : List α), xs.length = n →
      pMergeSort (xs.map f) = Costed.map (List.map f) (pMergeSort xs) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro xs hlength
      by_cases hsmall : xs.length ≤ 1
      · rw [pMergeSort, pMergeSort]
        simp [hsmall, Costed.charge, Costed.map]
      · let mid := xs.length / 2
        let left := xs.take mid
        let right := xs.drop mid
        have hn : 2 ≤ n := by omega
        have hleft_lt : left.length < n := by
          simp [left, mid, hlength]
          omega
        have hright_lt : right.length < n := by
          simp [right, mid, hlength]
          omega
        have hleft := ih left.length hleft_lt left rfl
        have hright := ih right.length hright_lt right rfl
        have hmerge := pMerge_map f hf
          ((pMergeSort left).value.length + (pMergeSort right).value.length)
          (pMergeSort left).value (pMergeSort right).value rfl
        rw [pMergeSort, pMergeSort]
        simp only [List.length_map]
        simp only [hsmall]
        rw [← List.map_take, ← List.map_drop]
        change Costed.seq
            (Costed.par (pMergeSort (left.map f)) (pMergeSort (right.map f)))
            (fun sorted => pMerge sorted.1 sorted.2) =
          Costed.map (List.map f)
            (Costed.seq (Costed.par (pMergeSort left) (pMergeSort right))
              (fun sorted => pMerge sorted.1 sorted.2))
        rw [hleft, hright]
        simp only [Costed.seq, Costed.par, Costed.map]
        rw [hmerge]
        rfl

end Span
end Costs
end ParallelMergeSort

end Chapter27
end CLRS
