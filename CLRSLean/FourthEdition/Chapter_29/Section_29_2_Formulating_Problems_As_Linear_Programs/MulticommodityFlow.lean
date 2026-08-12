import CLRSLean.FourthEdition.Chapter_29.Section_29_2_Formulating_Problems_As_Linear_Programs.NetworkFlow

/-!
# 29.2: Multicommodity flow as a linear program

Each commodity has its own source, sink, demand, and nonnegative gross flow.
All commodities share the edge capacities.  The optional cost objective also
records Exercise 29.2-7's minimum-cost multicommodity formulation.
-/

namespace CLRS
namespace Chapter29

open Finset

/-- Source, sink, and nonnegative demand of one commodity. -/
structure Commodity (V : Type*) where
  source : V
  sink : V
  source_ne_sink : source ≠ sink
  demand : ℝ
  demand_nonnegative : 0 ≤ demand

namespace MulticommodityFlowLP

variable {V K : Type*} [Fintype V] [Fintype K]

/-- Total flow of all commodities on one directed pair. -/
def aggregate (f : K → V → V → ℝ) (u v : V) : ℝ := ∑ i, f i u v

/-- The CLRS multicommodity feasibility constraints. -/
def IsFeasible (N : FlowNetwork V) (commodity : K → Commodity V)
    (f : K → V → V → ℝ) : Prop :=
  (∀ i u v, 0 ≤ f i u v) ∧
  (∀ u v, aggregate f u v ≤ N.capacity u v) ∧
  (∀ i u, u ≠ (commodity i).source → u ≠ (commodity i).sink →
    FlowNetwork.ConservesAt (f i) u) ∧
  ∀ i, FlowNetwork.netOutflow (f i) (commodity i).source = (commodity i).demand

/-- An expanded statement of the displayed multicommodity LP. -/
theorem isFeasible_iff (N : FlowNetwork V) (commodity : K → Commodity V)
    (f : K → V → V → ℝ) :
    IsFeasible N commodity f ↔
      (∀ i u v, 0 ≤ f i u v) ∧
      (∀ u v, (∑ i, f i u v) ≤ N.capacity u v) ∧
      (∀ i u, u ≠ (commodity i).source → u ≠ (commodity i).sink →
        FlowNetwork.inflow (f i) u = FlowNetwork.outflow (f i) u) ∧
      ∀ i, FlowNetwork.outflow (f i) (commodity i).source -
          FlowNetwork.inflow (f i) (commodity i).source = (commodity i).demand := by
  rfl

/-- Total cost of the aggregate multicommodity flow. -/
def cost (unitCost : V → V → ℝ) (f : K → V → V → ℝ) : ℝ :=
  ∑ u, ∑ v, unitCost u v * aggregate f u v

/-- Minimum-cost feasible multicommodity routing. -/
def IsMinimumCost (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) : Prop :=
  IsFeasible N commodity f ∧
    ∀ g, IsFeasible N commodity g → cost unitCost f ≤ cost unitCost g

/-- Expanded optimality statement for minimum-cost multicommodity flow. -/
theorem isMinimumCost_iff (N : FlowNetwork V) (commodity : K → Commodity V)
    (unitCost : V → V → ℝ) (f : K → V → V → ℝ) :
    IsMinimumCost N commodity unitCost f ↔
      IsFeasible N commodity f ∧
      ∀ g, IsFeasible N commodity g →
        (∑ u, ∑ v, unitCost u v * (∑ i, f i u v)) ≤
          ∑ u, ∑ v, unitCost u v * (∑ i, g i u v) := by
  rfl

end MulticommodityFlowLP
end Chapter29
end CLRS
