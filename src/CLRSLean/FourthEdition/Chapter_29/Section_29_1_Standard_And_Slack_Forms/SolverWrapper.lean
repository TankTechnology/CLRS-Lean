import CLRSLean.FourthEdition.Chapter_29.Section_29_1_Standard_And_Slack_Forms.Normalization
import CLRSLean.Chapter_29.Section_29_5_The_Initial_Basic_Feasible_Solution.InitializedSimplex

/-!
# 29.1 Canonical main-text solver wrapper

This module combines the general-form normalization of the previous module with
the initialized SIMPLEX solver (online material) to obtain a canonical
main-text solver for general-form programs.  The result type exposes exactly
the three textbook outcomes.

Main results:

- {lit}`GeneralLP.Result`: infeasible, optimal, or unbounded.
- {lit}`GeneralLP.solve`: normalize, solve, and translate back.
- {lit}`GeneralLP.solve_complete`: the wrapper always certifies one outcome.
-/

namespace CLRS
namespace Chapter29
namespace GeneralLP

variable (G : GeneralLP)

/-- Certified outcomes of the normalized solver, mapped back to the general
program. -/
inductive Result where
  | infeasible : (¬ ∃ x : Fin G.n → ℝ, G.IsFeasible x) → Result
  | optimal : (x : Fin G.n → ℝ) → G.IsOptimal x → Result
  | unbounded : G.IsUnbounded → Result

/-- A canonical main-text solver wrapper: normalize, run the initialized
SIMPLEX, and translate the outcome back to the general program. -/
noncomputable def solve : Result G := by
  classical
  match G.toStandardLP.initializedSimplex with
  | StandardLP.InitializedSimplexResult.infeasible h =>
      exact .infeasible (by
        intro hx
        exact h (G.feasible_iff_exists.mp hx))
  | StandardLP.InitializedSimplexResult.optimal x' hx' =>
      exact .optimal (G.proj x') (by
        refine ⟨G.feasible_of_normalized_feasible hx'.1, ?_⟩
        intro z hz
        have hz' : (G.toStandardLP).IsFeasible (G.lift z) := G.normalized_feasible_of_feasible hz
        have hbound := hx'.2 (G.lift z) hz'
        rw [G.objective_lift z, G.objective_eq_sign_objective_proj] at hbound
        exact hbound)
  | StandardLP.InitializedSimplexResult.unbounded h =>
      exact .unbounded (by
        intro M
        obtain ⟨x', hx', hM⟩ := h M
        refine ⟨G.proj x', G.feasible_of_normalized_feasible hx', ?_⟩
        rw [G.objective_eq_sign_objective_proj] at hM
        exact hM)

/-- The wrapper always certifies infeasibility, an optimum, or unboundedness. -/
theorem solve_complete :
    (¬ ∃ x : Fin G.n → ℝ, G.IsFeasible x) ∨
      (∃ x : Fin G.n → ℝ, G.IsOptimal x) ∨ G.IsUnbounded := by
  cases G.solve with
  | infeasible h => exact Or.inl h
  | optimal x hx => exact Or.inr (Or.inl ⟨x, hx⟩)
  | unbounded h => exact Or.inr (Or.inr h)

end GeneralLP
end Chapter29
end CLRS
