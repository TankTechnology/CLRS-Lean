import CLRSLean.FourthEdition.Chapter_16

/-!
# Fourth-edition Chapter 16 interface checks

These checks pin the public theorem interface of the fourth-edition §16.4
dynamic-tables refinement, in particular the interleaved insert/delete trace
amortized analysis.
-/

namespace CLRS
namespace Chapter17

-- §16.4 sharper load-factor potential (Sub-issue B)
#check sharpPotentialZ
#check sharpPotential
#check sharpInsert_amortized_le_three
#check sharpDelete_amortized_le_three
#check sharpDelete_loadFactor_eq_half_of_contract
#check sharpDelete_loadFactor_ge_half_of_contract

-- §16.4 interleaved insert/delete trace amortization
#check TableOp
#check TableOp.insert
#check TableOp.delete
#check tableStep
#check tableOpCost
#check execTrace
#check traceCost
#check tableStep_valid
#check sharpDelete_amortized_le_three_of_empty
#check tableOp_amortized_le_three
#check trace_amortized_le
#check sharpPotential_empty
#check emptyState_valid
#check trace_totalCost_le_three_mul

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms tableOp_amortized_le_three
#print axioms trace_amortized_le
#print axioms trace_totalCost_le_three_mul

end Chapter17
end CLRS
