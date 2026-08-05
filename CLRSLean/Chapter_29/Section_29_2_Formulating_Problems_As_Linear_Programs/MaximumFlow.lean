import CLRSLean.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Maximum flow as a linear program

The variables are the gross directed flows {lit}`f u v`.  The constraints are
nonnegativity, capacity, and conservation at every vertex other than
{lit}`s,t`; the objective is total flow leaving {lit}`s`, exactly as in CLRS
§29.2.
-/

namespace CLRS
namespace Chapter29
namespace MaximumFlowLP

open Finset

variable {V : Type*} [Fintype V] (N : FlowNetwork V)

/-- The constraints of the maximum-flow LP. -/
def IsFeasible (f : V → V → ℝ) : Prop :=
  (∀ u v, 0 ≤ f u v) ∧
  (∀ u v, f u v ≤ N.capacity u v) ∧
  ∀ u, u ≠ N.source → u ≠ N.sink → FlowNetwork.ConservesAt f u

/-- The textbook maximum-flow objective. -/
def objective (f : V → V → ℝ) : ℝ := FlowNetwork.outflow f N.source

/-- A feasible flow maximizing the source outflow. -/
def IsOptimal (f : V → V → ℝ) : Prop :=
  IsFeasible N f ∧ ∀ g, IsFeasible N g → objective N g ≤ objective N f

/-- The displayed LP constraints are precisely the usual finite-network flow
constraints. -/
theorem isFeasible_iff (f : V → V → ℝ) : IsFeasible N f ↔ N.IsFlow f := by
  simp only [IsFeasible, FlowNetwork.IsFlow, FlowNetwork.IsCapacityFeasible]
  tauto

/-- The LP optimum is precisely a maximum flow under the same objective. -/
theorem isOptimal_iff (f : V → V → ℝ) :
    IsOptimal N f ↔
      N.IsFlow f ∧ ∀ g, N.IsFlow g →
        FlowNetwork.outflow g N.source ≤ FlowNetwork.outflow f N.source := by
  simp only [IsOptimal, objective, isFeasible_iff]

end MaximumFlowLP
end Chapter29
end CLRS
