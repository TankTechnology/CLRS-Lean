import CLRSLean.FourthEdition.Chapter_29

/-!
# Chapter 29 normalization interface test

Verifies the general-form normalization, the solver wrapper, and the canonical
ownership path for general strong duality.
-/

namespace CLRS
namespace Chapter29

-- §29.1: general-form program representation and normalization.
#check GeneralLP
#check ConstraintRel
#check GeneralLP.IsFeasible
#check GeneralLP.objective
#check GeneralLP.objectiveSign
#check GeneralLP.IsOptimal
#check GeneralLP.IsUnbounded
#check GeneralLP.toStandardLP
#check GeneralLP.lift
#check GeneralLP.proj
#check GeneralLP.normalized_feasible_of_feasible
#check GeneralLP.feasible_of_normalized_feasible
#check GeneralLP.feasible_iff_lift
#check GeneralLP.feasible_iff_exists
#check GeneralLP.objective_eq_sign_objective_proj
#check GeneralLP.objective_lift
#check GeneralLP.Result
#check GeneralLP.solve
#check GeneralLP.solve_complete

#print axioms GeneralLP.feasible_iff_lift
#print axioms GeneralLP.objective_lift
#print axioms GeneralLP.solve_complete

-- §29.3: canonical ownership of general strong duality.
#check StandardLP.strongDuality
#check StandardLP.complementarySlackness_iff_optimal

#print axioms StandardLP.strongDuality
#print axioms StandardLP.complementarySlackness_iff_optimal

-- §29.2: finite standard-form encodings (bidirectional bridge + objective).
#check ShortestPathLP.toStandardLP
#check ShortestPathLP.feasible_iff_toStandardLP
#check ShortestPathLP.objective_toStandardLP
#check MaximumFlowLP.toStandardLP
#check MaximumFlowLP.feasible_iff_toStandardLP
#check MaximumFlowLP.objective_toStandardLP
#check MinimumCostFlowLP.toStandardLP
#check MinimumCostFlowLP.feasible_iff_toStandardLP
#check MinimumCostFlowLP.objective_toStandardLP
#check MulticommodityFlowLP.toStandardLP
#check MulticommodityFlowLP.feasible_iff_toStandardLP
#check MulticommodityFlowLP.objective_toStandardLP

#print axioms ShortestPathLP.feasible_iff_toStandardLP
#print axioms MaximumFlowLP.feasible_iff_toStandardLP
#print axioms MinimumCostFlowLP.objective_toStandardLP
#print axioms MulticommodityFlowLP.feasible_iff_toStandardLP

end Chapter29
end CLRS
