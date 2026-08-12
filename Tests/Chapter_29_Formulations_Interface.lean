import CLRSLean.Chapter_29

/-!
# Chapter 29 formulation interface test

Verifies the public textbook formulations from Section 29.2 through the
Chapter 29 guide.
-/

namespace CLRS
namespace Chapter29

#check ShortestPathLP.IsFeasible
#check ShortestPathLP.IsOptimal
#check ShortestPathLP.feasible_le_walkWeight
#check ShortestPathLP.optimal_of_attained_walk

#check FlowNetwork
#check FlowNetwork.outflow
#check FlowNetwork.inflow
#check FlowNetwork.netOutflow
#check FlowNetwork.ConservesAt
#check FlowNetwork.IsCapacityFeasible

#check MaximumFlowLP.IsFeasible
#check MaximumFlowLP.objective
#check MaximumFlowLP.IsOptimal
#check MaximumFlowLP.isFeasible_iff
#check MaximumFlowLP.isOptimal_iff

example {V : Type*} [Fintype V] (N : FlowNetwork V) (f : V → V → ℝ) :
    MaximumFlowLP.objective N f =
      FlowNetwork.outflow f N.source - FlowNetwork.inflow f N.source := rfl

#check CostedFlowNetwork
#check MinimumCostFlowLP.IsFeasible
#check MinimumCostFlowLP.objective
#check MinimumCostFlowLP.IsOptimal
#check MinimumCostFlowLP.isFeasible_iff
#check MinimumCostFlowLP.isOptimal_iff

#check Commodity
#check MulticommodityFlowLP.IsFeasible
#check MulticommodityFlowLP.aggregate
#check MulticommodityFlowLP.isFeasible_iff
#check MulticommodityFlowLP.cost
#check MulticommodityFlowLP.IsMinimumCost
#check MulticommodityFlowLP.isMinimumCost_iff

#print axioms ShortestPathLP.feasible_le_walkWeight
#print axioms ShortestPathLP.optimal_of_attained_walk
#print axioms MaximumFlowLP.isOptimal_iff
#print axioms MinimumCostFlowLP.isOptimal_iff
#print axioms MulticommodityFlowLP.isMinimumCost_iff

end Chapter29
end CLRS
