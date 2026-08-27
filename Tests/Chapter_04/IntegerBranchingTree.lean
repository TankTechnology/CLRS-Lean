import CLRSLean.FourthEdition.Chapter_04.Section_04_4_Recursion_Tree_Method.Branching.IntegerTree

/-! Focused public-interface checks for the unequal-depth integer tree. -/

#check CLRS.Chapter04.IntegerBranchingSpec.build_totalCost_eq
#check CLRS.Chapter04.balancedIntegerTree_totalCost_eq
#check CLRS.Chapter04.unbalancedIntegerTree_totalCost_eq
#check CLRS.Chapter04.unbalancedIntegerTree_has_unequal_depth
#check CLRS.Chapter04.balancedIntegerCost_floorRecurrence
#check CLRS.Chapter04.unbalancedInteger_akraBazziRoot

example : CLRS.Chapter04.twoThirdsCeil 4 = 3 := by native_decide

example :
    (CLRS.Chapter04.unbalancedIntegerSpec 1 1).childSize false 4 = 1 := by
  native_decide

example :
    (CLRS.Chapter04.unbalancedIntegerSpec 1 1).childSize true 4 = 3 := by
  native_decide

example :
    CLRS.Chapter04.IntegerBranchingTree.height
      ((CLRS.Chapter04.unbalancedIntegerSpec 1 1).build 1) = 0 := by
  native_decide
