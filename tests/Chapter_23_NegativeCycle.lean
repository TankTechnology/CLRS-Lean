import CLRSLean.FourthEdition.Chapter_23.Section_23_2_Floyd_Warshall.NegativeCycle
import CLRSLean.Audit.Axioms
open CLRS.Chapter24 CLRS.Chapter24.WeightedGraph Finset

private theorem univ_one : (univ : Finset (Fin 1)) = {0} := by
  ext i
  simp [Subsingleton.elim i (0 : Fin 1)]

private def negativeSelf : WeightedGraph (Fin 1) := ⟨{(0, 0)}, fun _ _ => -1⟩

-- The original forced-zero initializer misses this graph.
example : negativeSelf.floydWarshall 0 0 = 0 := by
  simp [floydWarshall, D, weightMatrix]
example : negativeSelf.cycleWeightMatrix 0 0 = (-1 : WithTop ℝ) := by
  norm_num [cycleWeightMatrix, negativeSelf, Adj]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_le_coe]
  norm_num
example : negativeSelf.cycleFloydWarshall 0 0 = (-2 : WithTop ℝ) := by
  norm_num [cycleFloydWarshall, cycleD, floydFrom, univ_one, cycleWeightMatrix, negativeSelf, Adj]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, ← WithTop.coe_one, ← WithTop.coe_ofNat, ← WithTop.coe_add, ← WithTop.coe_min, WithTop.coe_inj]
  norm_num
example : negativeSelf.detectsNegativeCycle = true := by
  norm_num [detectsNegativeCycle, hasNegativeDiagonal, cycleFloydWarshall, cycleD,
    floydFrom, univ_one, cycleWeightMatrix, negativeSelf, Adj]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, ← WithTop.coe_one, WithTop.coe_lt_coe]
  norm_num

private def positiveSelf : WeightedGraph (Fin 1) := ⟨{(0, 0)}, fun _ _ => 4⟩
example : positiveSelf.detectsNegativeCycle = false := by
  norm_num [detectsNegativeCycle, hasNegativeDiagonal, cycleFloydWarshall, cycleD,
    floydFrom, univ_one, cycleWeightMatrix, positiveSelf, Adj]

private def noEdges : WeightedGraph (Fin 1) := ⟨∅, fun _ _ => -100⟩
example : noEdges.detectsNegativeCycle = false := by
  norm_num [detectsNegativeCycle, hasNegativeDiagonal, cycleFloydWarshall, cycleD,
    floydFrom, univ_one, cycleWeightMatrix, noEdges, Adj]

private def twoCycle : WeightedGraph Bool :=
  ⟨{(false, true), (true, false)}, fun i _ => if i then 1 else -2⟩
example : twoCycle.cycleD [false, true] false false = (-2 : WithTop ℝ) := by
  norm_num [cycleD, floydFrom, cycleWeightMatrix, twoCycle, Adj]
  simp only [← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_zero, ← WithTop.coe_one, ← WithTop.coe_ofNat, ← WithTop.coe_add, ← WithTop.coe_min, WithTop.coe_inj]
  norm_num
example : twoCycle.detectsNegativeCycle = true := by
  apply negative_closed_walk_detected twoCycle false [false, true, false]
  · constructor <;> simp [List.isChain_cons, twoCycle, Adj]
  · norm_num [walkWeight, twoCycle]

private def isolatedCycle : WeightedGraph Bool := ⟨{(true, true)}, fun _ _ => -3⟩
example : isolatedCycle.detectsNegativeCycle = true := by
  apply negative_closed_walk_detected isolatedCycle true [true, true]
  · constructor <;> simp [List.isChain_cons, isolatedCycle, Adj]
  · norm_num [walkWeight, isolatedCycle]

#assert_axioms floydFrom_triangle
#assert_axioms floydFrom_weightMatrix
#assert_axioms noNegCycle_of_cycleFloydWarshall_nonneg_diag
#assert_axioms cycleWeightMatrix_eq_weightMatrix
#assert_axioms cycleD_eq_D
#assert_axioms cycleFloydWarshall_negative_iff
#assert_axioms cycleFloydWarshall_negative_iff_closed_walk
#assert_axioms detectsNegativeCycle_iff
#assert_axioms cycleFloydWarshall_isShortestDist
