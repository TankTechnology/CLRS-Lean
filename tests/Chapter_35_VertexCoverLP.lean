import CLRSLean.FourthEdition.Chapter_35.Section_35_4_Randomization_And_Linear_Programming.VertexCoverLP
import CLRSLean.Audit.Axioms

open CLRS.RandomizedLP CLRS.RandomizedLP.VertexCoverLP Finset
noncomputable section

private def edge : CLRS.ApproxVertexCover.Graph (Fin 2) (Fin 1) := ⟨fun _ => 0,fun _ => 1⟩
private def unitWeight : Fin 2 → ℚ := fun _ => 1

-- Edge constraints reject the zero vector and accept an endpoint indicator.
example : ¬ (program edge univ unitWeight).IsFeasible (fun _ => 0) := by
  rw [feasible_iff]
  norm_num [edge]
example : (program edge univ unitWeight).IsFeasible (fun v => if v=0 then 1 else 0) := by
  rw [feasible_iff]
  norm_num [edge]

-- The actual solver output covers the edge; no supplied fractional vector.
example : edge.IsVertexCoverOn univ (execute edge univ unitWeight (by intro; norm_num [unitWeight])) :=
  execute_isVertexCover _ _ _ _
example : vertexWeight unitWeight (execute edge univ unitWeight (by intro; norm_num [unitWeight])) ≤ 2 := by
  have h := execute_two_approx edge univ unitWeight (by intro; norm_num [unitWeight]) {0}
    (by intro e _; exact Or.inl (by simp [edge]))
  simpa [vertexWeight,unitWeight] using h

-- A self-loop contributes both incidences: its LP optimum can be 1/2.
private def loop : CLRS.ApproxVertexCover.Graph (Fin 1) (Fin 1) := ⟨id,id⟩
example : (program loop univ (fun _ => 1)).IsFeasible (fun _ => (1:ℝ)/2) := by
  rw [feasible_iff]
  norm_num [loop]
example : (0 : Fin 1) ∈ execute loop univ (fun _ => 0) (by simp) := by
  have h := execute_isVertexCover loop univ (fun _ => 0) (by simp) 0 (mem_univ _)
  simpa [loop] using h

-- With no active edges, the optimum and returned weight are zero.
example : vertexWeight unitWeight (execute edge ∅ unitWeight (by intro; norm_num [unitWeight])) = 0 := by
  have h := execute_two_approx edge ∅ unitWeight (by intro; norm_num [unitWeight]) ∅ (by simp [CLRS.ApproxVertexCover.Graph.IsVertexCoverOn])
  have hn : 0 ≤ vertexWeight unitWeight (execute edge ∅ unitWeight (by intro; norm_num [unitWeight])) := by
    unfold vertexWeight
    exact sum_nonneg (by intro v _; norm_num [unitWeight])
  simp only [vertexWeight, sum_empty, mul_zero] at h
  exact le_antisymm h hn

#assert_axioms feasible_iff
#assert_axioms solve_weight_le
#assert_axioms execute_correct

-- The empty carrier also has a total solver-to-cover interface.
example : execute (⟨Fin.elim0,Fin.elim0⟩ : CLRS.ApproxVertexCover.Graph (Fin 0) (Fin 0))
    ∅ (fun _ => 0) (by simp) = ∅ := by
  ext v
  exact Fin.elim0 v
