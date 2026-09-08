import CLRSLean.FourthEdition.Chapter_35.Section_35_4_Randomization_And_Linear_Programming
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.InitializedSimplex

/-!
# Vertex-cover LP construction and initialized-solver composition

The graph supplies all constraints. The initialized Chapter 29 solver produces
a fractional optimum; feasibility and boundedness discharge its other outcomes.
Rounding that returned vector gives a cover within twice every comparator cover.
The new solver bridge uses real fractional vectors and rational input weights;
the older rational-vector rounding interface is retained. This is a classical
exact-real construction, without a polynomial SIMPLEX runtime claim.
-/
noncomputable section
namespace CLRS.RandomizedLP.VertexCoverLP
open Finset Matrix
variable {n m : Nat} (G : ApproxVertexCover.Graph (Fin n) (Fin m))
    (edges : Finset (Fin m)) (w : Fin n → ℚ)

/-- Maximize the negated cover weight under edge and upper-bound constraints. -/
def program : Chapter29.StandardLP (m+n) n where
  A := Fin.addCases
    (fun e j => if e ∈ edges then
      -(if j = G.src e then 1 else 0) - (if j = G.dst e then 1 else 0) else 0)
    (fun v j => if j = v then 1 else 0)
  b := Fin.addCases (fun e => if e ∈ edges then -1 else 0) (fun _ => 1)
  c := fun v => -(w v : ℝ)

@[simp] theorem edge_row (x : Fin n → ℝ) (e : Fin m) :
    ((program G edges w).A *ᵥ x) (Fin.castAdd n e) =
      if e ∈ edges then -(x (G.src e) + x (G.dst e)) else 0 := by
  by_cases he : e ∈ edges <;>
    simp [program, Matrix.mulVec, dotProduct, he, sub_mul, Finset.sum_sub_distrib]
  ring

@[simp] theorem upper_row (x : Fin n → ℝ) (v : Fin n) :
    ((program G edges w).A *ᵥ x) (Fin.natAdd m v) = x v := by
  simp [program, Matrix.mulVec, dotProduct]

/-- Exact LP encoding of fractional cover constraints. -/
theorem feasible_iff (x : Fin n → ℝ) :
    (program G edges w).IsFeasible x ↔
      (∀ v, 0 ≤ x v) ∧ (∀ v, x v ≤ 1) ∧ ∀ e ∈ edges, 1 ≤ x (G.src e)+x (G.dst e) := by
  constructor
  · intro h
    refine ⟨h.1,?_,?_⟩
    · intro v
      have hb := h.2 (Fin.natAdd m v)
      rw [upper_row] at hb
      simpa [program] using hb
    · intro e he
      have heq := edge_row G edges w x e
      have hb := h.2 (Fin.castAdd n e)
      rw [heq] at hb
      simpa [program,he] using hb
  · rintro ⟨hzero,hupper,hedge⟩
    refine ⟨hzero,?_⟩
    intro i
    refine Fin.addCases (fun e => ?_) (fun v => ?_) i
    · rw [edge_row]
      by_cases he : e ∈ edges
      · simpa [program,he] using neg_le_neg (hedge e he)
      · simp [program,he]
    · rw [upper_row]
      simpa [program] using hupper v

@[simp] theorem objective_eq (x : Fin n → ℝ) :
    (program G edges w).objective x = -(∑ v, (w v : ℝ)*x v) := by
  simp [Chapter29.StandardLP.objective, program, dotProduct, Finset.sum_neg_distrib]

theorem feasible_one : (program G edges w).IsFeasible (fun _ => 1) := by
  rw [feasible_iff]
  norm_num

theorem objective_nonpos (hw : ∀ v, 0 ≤ w v) {x : Fin n → ℝ}
    (hx : (program G edges w).IsFeasible x) : (program G edges w).objective x ≤ 0 := by
  rw [objective_eq]
  have hs : 0 ≤ ∑ v, (w v : ℝ)*x v := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (by exact_mod_cast hw v) (hx.1 v)
  linarith

/-- Invoke initialized SIMPLEX and retain its returned optimal vector. -/
def solve (hw : ∀ v, 0 ≤ w v) : {x : Fin n → ℝ // (program G edges w).IsOptimal x} :=
  match (program G edges w).initializedSimplex with
  | .infeasible h => False.elim (h ⟨_,feasible_one G edges w⟩)
  | .optimal x hx => ⟨x,hx⟩
  | .unbounded h => False.elim (by
    obtain ⟨x,hx,hpos⟩ := h 0
    exact (not_lt_of_ge (objective_nonpos G edges w hw hx)) hpos)

/-- Round the actual returned vector at one half. -/
def execute (hw : ∀ v, 0 ≤ w v) : Finset (Fin n) :=
  let x := solve G edges w hw
  Finset.univ.filter (fun v => (1:ℝ)/2 ≤ x.val v)

theorem execute_isVertexCover (hw : ∀ v, 0 ≤ w v) :
    G.IsVertexCoverOn edges (execute G edges w hw) := by
  intro e he
  have hx := (feasible_iff G edges w _).mp (solve G edges w hw).property.1
  have hedge := hx.2.2 e he
  simp only [execute, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : (1:ℝ)/2 ≤ (solve G edges w hw).val (G.src e)
  · exact Or.inl h
  · right
    push Not at h
    linarith

/-- Every integral comparator cover gives a feasible LP vector. -/
theorem indicator_feasible (C : Finset (Fin n)) (hC : G.IsVertexCoverOn edges C) :
    (program G edges w).IsFeasible (fun v => if v ∈ C then 1 else 0) := by
  rw [feasible_iff]
  refine ⟨?_,?_,?_⟩
  · intro v; split_ifs <;> norm_num
  · intro v; split_ifs <;> norm_num
  · intro e he
    rcases hC e he with hs | hd
    · simp only [hs, if_true]; split_ifs <;> norm_num
    · simp only [hd, if_true]; split_ifs <;> norm_num

/-- The bound against every integral cover follows from the returned optimum. -/
theorem solve_weight_le (hw : ∀ v, 0 ≤ w v)
    (C : Finset (Fin n)) (hC : G.IsVertexCoverOn edges C) :
    (∑ v, (w v : ℝ)*(solve G edges w hw).val v) ≤ ∑ v ∈ C, (w v : ℝ) := by
  have h := (solve G edges w hw).property.2 _ (indicator_feasible G edges w C hC)
  simp only [objective_eq] at h
  have hi : (∑ v, (w v : ℝ)*(if v ∈ C then 1 else 0)) = ∑ v ∈ C, (w v : ℝ) := by
    simp [mul_ite, Finset.sum_ite_mem]
  rw [hi] at h
  linarith

/-- Threshold rounding costs at most twice the returned fractional objective. -/
theorem execute_weight_le_fractional (hw : ∀ v, 0 ≤ w v) :
    (∑ v ∈ execute G edges w hw, (w v : ℝ)) ≤
      2 * ∑ v, (w v : ℝ)*(solve G edges w hw).val v := by
  have hx := (solve G edges w hw).property.1.1
  have hstep : ∀ v ∈ execute G edges w hw,
      (w v : ℝ) ≤ 2*((w v : ℝ)*(solve G edges w hw).val v) := by
    intro v hv
    have hv' : (1:ℝ)/2 ≤ (solve G edges w hw).val v := by
      simpa [execute] using hv
    have hw' : (0:ℝ) ≤ w v := by exact_mod_cast hw v
    nlinarith
  calc
    _ ≤ ∑ v ∈ execute G edges w hw, 2*((w v : ℝ)*(solve G edges w hw).val v) :=
      Finset.sum_le_sum hstep
    _ ≤ ∑ v, 2*((w v : ℝ)*(solve G edges w hw).val v) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro v _ _
      exact mul_nonneg (by norm_num) (mul_nonneg (by exact_mod_cast hw v) (hx v))
    _ = _ := by rw [Finset.mul_sum]

/-- Graph-to-solver-to-rounded-cover factor two, without a supplied LP bound. -/
theorem execute_two_approx (hw : ∀ v, 0 ≤ w v)
    (C : Finset (Fin n)) (hC : G.IsVertexCoverOn edges C) :
    vertexWeight w (execute G edges w hw) ≤ 2 * vertexWeight w C := by
  have hr := execute_weight_le_fractional G edges w hw
  have ho := solve_weight_le G edges w hw C hC
  have h : (∑ v ∈ execute G edges w hw, (w v : ℝ)) ≤ 2*∑ v ∈ C, (w v : ℝ) := by
    linarith
  unfold vertexWeight
  exact_mod_cast h

/-- The same returned set satisfies feasibility and the approximation guarantee. -/
theorem execute_correct (hw : ∀ v, 0 ≤ w v)
    (C : Finset (Fin n)) (hC : G.IsVertexCoverOn edges C) :
    G.IsVertexCoverOn edges (execute G edges w hw) ∧
      vertexWeight w (execute G edges w hw) ≤ 2*vertexWeight w C :=
  ⟨execute_isVertexCover G edges w hw,execute_two_approx G edges w hw C hC⟩

end CLRS.RandomizedLP.VertexCoverLP
