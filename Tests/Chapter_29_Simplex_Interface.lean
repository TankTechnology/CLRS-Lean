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

#check Dictionary.pivotSwap
#check Dictionary.pivotRowB
#check Dictionary.pivotRowCoeff
#check Dictionary.pivot
#check Dictionary.pivot_basicVar_leaving
#check Dictionary.pivot_nonbasicVar_entering
#check Dictionary.pivot_basicVar_of_ne
#check Dictionary.pivot_nonbasicVar_of_ne
#check Dictionary.pivot_b_leaving
#check Dictionary.pivot_b_of_ne
#check Dictionary.pivot_a_leaving_entering
#check Dictionary.pivot_a_leaving_of_ne
#check Dictionary.pivot_a_of_ne_entering
#check Dictionary.pivot_a_of_ne
#check Dictionary.pivot_v_apply
#check Dictionary.pivot_c_entering
#check Dictionary.pivot_c_of_ne

noncomputable def pivotExample : Dictionary 1 1 where
  labels := Equiv.refl _
  b := fun _ => 6
  a := fun _ _ => 2
  v := 1
  c := fun _ => 3

example :
    let h : pivotExample.a 0 0 ≠ 0 := by norm_num [pivotExample]
    (pivotExample.pivot 0 0 h).b 0 = 3 ∧
      (pivotExample.pivot 0 0 h).v = 10 := by
  norm_num [pivotExample, Dictionary.pivot, Dictionary.pivotRowB]

#check Dictionary.pivot_satisfies_iff
#check Dictionary.pivot_objectiveRhs_eq
#check Dictionary.IsMinimumRatio
#check Dictionary.IsMinimumRatio.pivotCoefficient_pos
#check Dictionary.IsMinimumRatio.ratio_le
#check Dictionary.pivot_isBasicFeasible

example {m n : ℕ} (D : Dictionary m n) (x : LPVar m n → ℝ)
    (l : Fin m) (e : Fin n) (h : D.a l e ≠ 0) :
    D.Satisfies x ↔ (D.pivot l e h).Satisfies x :=
  D.pivot_satisfies_iff x l e h

#print axioms Dictionary.pivot_satisfies_iff
#print axioms Dictionary.pivot_objectiveRhs_eq
#print axioms Dictionary.pivot_isBasicFeasible

end Chapter29
end CLRS
