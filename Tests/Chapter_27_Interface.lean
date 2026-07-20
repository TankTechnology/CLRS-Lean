import CLRSLean.Chapter_27

namespace CLRS
namespace Chapter27

#check Strand
#check CompDAG
#check CompDAG.work
#check CompDAG.longestTo
#check CompDAG.span
#check CompDAG.longestTo_le
#check CompDAG.span_le_work
#check CompDAG.speedup
#check CompDAG.parallelism
#check SpawnTree
#check SpawnTree.work
#check SpawnTree.span
#check SpawnTree.span_le_work
#check parallelLoopTree
#check parallelLoopTree_unfold
#check parallelLoop_work
#check parallelLoopDepth
#check parallelLoop_span
#check parallelLoopDepth_pow
#check pMatMulWork
#check pMatMulWork_unfold
#check pMatMulWork_pow_two
#check pMatMulWork_le
#check pMatMulSpan
#check pMatMulSpan_pow_two
#check pMatMulSpan_le
#check pMergeWork
#check pMergeWork_unfold
#check pMergeWork_pow_two
#check pMergeSpan
#check pMergeSpan_pow_two
#check pMergeSortWork
#check pMergeSortWork_pow_two
#check pMergeSortSpan
#check pMergeSortSpan_pow_two
#check strassenWork
#check strassenWork_pow_two
#check strassenSpan
#check strassenSpan_pow_two

/-- A three-node chain with unit-weight edges forward: work and span both 6. -/
def chainDAG : CompDAG where
  n := 3
  node_work := fun _ => 2
  edges := [(0, 1), (1, 2)]
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

/-- A fork: node 0 (weight 1) precedes nodes 1 (weight 5) and 2 (weight 1).
The span follows the heavier branch: 1 + 5 = 6, while the work is 7. -/
def forkJoinDAG : CompDAG where
  n := 3
  node_work := fun i => match i with
    | 0 => 1
    | 1 => 5
    | _ => 1
  edges := [(0, 1), (0, 2)]
  h_edges_in_bounds := by decide
  h_edges_forward := by decide

example : chainDAG.work = 6 := by native_decide

example : chainDAG.span = 6 := by native_decide

example : forkJoinDAG.work = 7 := by native_decide

example : forkJoinDAG.span = 6 := by native_decide

example (G : CompDAG) : G.span ≤ G.work := G.span_le_work

-- A balanced parallel loop over 8 unit iterations: 15 work (8 leaves plus 7
-- internal spawn nodes) and span 4 (one unit leaf plus depth 3).
example : (parallelLoopTree 8 1).work = 15 := by native_decide

example : (parallelLoopTree 8 1).span = 4 := by native_decide

example : parallelLoopDepth 8 = 3 := by native_decide

example (n : ℕ) (hn : 1 ≤ n) (w : ℕ) :
    (parallelLoopTree n w).work + 1 = n * w + n := parallelLoop_work hn w

example (n : ℕ) : n ≤ 2 ^ parallelLoopDepth n := parallelLoopDepth_pow n

-- Concrete cost values, cross-checked against the power-of-two closed forms.
example : pMatMulWork 8 = 960 := by native_decide

example : pMatMulSpan 8 = 4 := by native_decide

example : pMergeWork 8 = 26 := by native_decide

example : pMergeSpan 8 = 10 := by native_decide

example : pMergeSortWork 8 = 32 := by native_decide

example : pMergeSortSpan 8 = 20 := by native_decide

example : strassenWork 8 = 715 := by native_decide

example : strassenSpan 8 = 4 := by native_decide

example (k : ℕ) : pMatMulWork (2 ^ k) + 4 ^ k = 2 * 8 ^ k :=
  pMatMulWork_pow_two k

example (n : ℕ) : pMatMulWork n + n * n ≤ 2 * n * n * n := pMatMulWork_le n

example (n : ℕ) : pMatMulSpan n ≤ Nat.log 2 n + 1 := pMatMulSpan_le n

example (k : ℕ) : pMergeWork (2 ^ k) + (k + 3) = 4 * 2 ^ k :=
  pMergeWork_pow_two k

example (k : ℕ) : 2 * pMergeSpan (2 ^ k) = (k + 1) * (k + 2) :=
  pMergeSpan_pow_two k

example (k : ℕ) : pMergeSortWork (2 ^ k) = 2 ^ k * (k + 1) :=
  pMergeSortWork_pow_two k

example (k : ℕ) : 6 * pMergeSortSpan (2 ^ k) = 6 + k * (k * k + 6 * k + 11) :=
  pMergeSortSpan_pow_two k

example (k : ℕ) : 3 * strassenWork (2 ^ k) + 4 ^ (k + 1) = 7 ^ (k + 1) :=
  strassenWork_pow_two k

end Chapter27
end CLRS
