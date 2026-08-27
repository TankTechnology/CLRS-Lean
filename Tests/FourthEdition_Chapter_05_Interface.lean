import CLRSLean.FourthEdition.Chapter_05

/-!
# Fourth-edition Chapter 5 interface checks

These checks pin the public interface of the executable HIRE-ASSISTANT
pseudocode layer in the native fourth-edition §5.1 source.
-/

namespace CLRS
namespace Chapter05

-- §5.2 textbook indicator/probability boundary (Lemma 5.1)
#check eventProbability
#check indicator_expectation_eq_probability

-- §5.1 executable HIRE-ASSISTANT pseudocode
#check recordsFrom
#check hireAssistant
#check recordsFrom_step
#check hireAssistant_cons
#check recordsFrom_le_length
#check hireAssistant_le_length
#check hireAssistant_pos

-- §5.1/§5.3 expected-cost and randomized-hiring composition
#check expectedHiringCost
#check expectedHiringCost_eq_harmonic
#check expectedHiringCost_isBigO_log
#check permutationRanks
#check randomizedHireAssistant
#check randomizedExpectedHires_eq_uniform
#check HiringExpectationBridge
#check randomizedExpectedHiringCost
#check randomizedExpectedHiringCost_eq_uniform
#check randomizedExpectedHiringCost_eq
#check randomizedExpectedHiringCost_isBigO_log

-- §5.3 constructive RANDOMIZE-IN-PLACE / Fisher–Yates refinement
#check choiceVectorSuccEquiv
#check fisherYatesStep
#check fisherYates
#check fisherYates_succ_invariant
#check fisherYatesStep_map_finRange_perm
#check fisherYates_map_finRange_perm
#check fisherYates_first_uniform
#check fisherYates_uniform
#check randomizeInPlace_eq_fisherYates

example : fisherYates (zeroChoiceVector 4) 2 = 2 := by native_decide
example : fisherYates (lastChoiceVector 4) 0 = 3 := by native_decide

-- The executable loop counts left-to-right maxima (records).
example : hireAssistant [] = 0 := by native_decide
example : hireAssistant [7] = 1 := by native_decide
example : hireAssistant [3, 1, 4, 1, 5, 9, 2, 6] = 4 := by native_decide
example : recordsFrom 5 [1, 6, 3, 9, 8] = 2 := by native_decide

/-! The headline theorems must not carry `sorryAx` or any project axiom. -/
#print axioms recordsFrom_step
#print axioms hireAssistant_le_length

end Chapter05
end CLRS
