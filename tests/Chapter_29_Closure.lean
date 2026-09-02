import CLRSLean.Chapter_29

/-!
# Chapter 29 closure contract

This aggregator-only test seals the main-text boundary for Sections 29.1--29.5.
-/

namespace CLRS
namespace Chapter29

-- 29.1: standard/slack equivalence.
#check StandardLP.existsUnique_slackExtension_iff

-- 29.2: textbook problem formulations.
#check ShortestPathLP.optimal_of_attained_walk
#check MaximumFlowLP.isOptimal_iff
#check MinimumCostFlowLP.isOptimal_iff
#check MulticommodityFlowLP.isMinimumCost_iff

-- 29.3: exact PIVOT, anti-cycling, and finite SIMPLEX.
#check Dictionary.pivot_satisfies_iff
#check Dictionary.bland_no_repeated_basis
#check Dictionary.simplex_optimal_or_unbounded

-- 29.4: weak/strong duality and complementary slackness.
#check StandardLP.weak_duality
#check Dictionary.dualCertificate_isDualFeasible
#check StandardLP.strongDuality
#check StandardLP.complementarySlackness_iff_optimal

-- 29.5: phase I and the complete initialized solver.
#check StandardLP.isFeasible_iff_phaseOneTerminal_v_eq_zero
#check StandardLP.phaseTwoStart_isBasicFeasible
#check StandardLP.initializedSimplex_complete

#print axioms ShortestPathLP.optimal_of_attained_walk
#print axioms Dictionary.simplex_optimal_or_unbounded
#print axioms StandardLP.initializedSimplex_complete
#print axioms StandardLP.strongDuality
#print axioms StandardLP.complementarySlackness_iff_optimal

end Chapter29
end CLRS
