import CLRSLean.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Minimum-cost flow as a linear program

In addition to capacities, a network assigns a unit cost to every directed
pair.  A demand-`d` flow has net source outflow `d`; minimizing the sum of unit
cost times flow gives the CLRS minimum-cost-flow formulation.
-/

namespace CLRS
namespace Chapter29

open Finset

/-- A capacitated network with a real unit cost on each directed pair. -/
structure CostedFlowNetwork (V : Type*) [Fintype V] extends FlowNetwork V where
  cost : V → V → ℝ

namespace MinimumCostFlowLP

variable {V : Type*} [Fintype V] (N : CostedFlowNetwork V) (demand : ℝ)

/-- The capacity, conservation, and exact-demand constraints. -/
def IsFeasible (f : V → V → ℝ) : Prop :=
  N.toFlowNetwork.IsFlow f ∧
    FlowNetwork.netOutflow f N.source = demand

/-- Total cost `Σ_u Σ_v a_uv f_uv`. -/
def objective (f : V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, N.cost u v * f u v

/-- A demand flow of minimum total cost. -/
def IsOptimal (f : V → V → ℝ) : Prop :=
  IsFeasible N demand f ∧
    ∀ g, IsFeasible N demand g → objective N f ≤ objective N g

/-- The LP constraints are exactly capacity-feasible flow plus the prescribed
source demand. -/
theorem isFeasible_iff (f : V → V → ℝ) :
    IsFeasible N demand f ↔
      N.toFlowNetwork.IsFlow f ∧
        FlowNetwork.netOutflow f N.source = demand := by
  rfl

/-- The minimization specification agrees exactly with minimum-cost demand
flow. -/
theorem isOptimal_iff (f : V → V → ℝ) :
    IsOptimal N demand f ↔
      (N.toFlowNetwork.IsFlow f ∧
        FlowNetwork.netOutflow f N.source = demand) ∧
      ∀ g, (N.toFlowNetwork.IsFlow g ∧
        FlowNetwork.netOutflow g N.source = demand) →
        (∑ u, ∑ v, N.cost u v * f u v) ≤
          ∑ u, ∑ v, N.cost u v * g u v := by
  rfl

end MinimumCostFlowLP
end Chapter29
end CLRS
