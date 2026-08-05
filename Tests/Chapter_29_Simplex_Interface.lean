import CLRSLean.Chapter_29

/-!
# Chapter 29 SIMPLEX Interface Test

Verifies the public dictionary and PIVOT declarations represented from
Section 29.3 through the Chapter 29 guide.
-/

namespace CLRS
namespace Chapter29

#check LPVar
#check Dictionary
#check Dictionary.basicVar
#check Dictionary.nonbasicVar
#check Dictionary.rowRhs
#check Dictionary.objectiveRhs
#check Dictionary.Satisfies
#check Dictionary.IsBasicFeasible
#check Dictionary.IsNonnegativeAssignment
#check Dictionary.basicAssignment
#check Dictionary.basicAssignment_basicVar
#check Dictionary.basicAssignment_nonbasicVar
#check Dictionary.basicAssignment_satisfies
#check Dictionary.basicAssignment_nonnegative_iff

example {m n : ℕ} (D : Dictionary m n) :
    D.Satisfies D.basicAssignment :=
  D.basicAssignment_satisfies

#check StandardLP.initialDictionary
#check StandardLP.combinedAssignment
#check StandardLP.combinedAssignment_nonnegative_iff
#check StandardLP.initialDictionary_satisfies_iff
#check StandardLP.initialDictionary_satisfies_of_slackExtension
#check StandardLP.initialDictionary_objectiveRhs
#check StandardLP.initialDictionary_isBasicFeasible_iff

end Chapter29
end CLRS
