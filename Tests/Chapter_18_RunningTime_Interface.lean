import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.RunningTime

namespace CLRS.Chapter18.BTree

#check (searchCost : Nat → BTree → Nat)
#check (insertCost : Nat → Nat → BTree → Nat)
#check (insertRootCost : Nat → Nat → BTree → Nat)
#check (deleteCost : Nat → Nat → BTree → Nat)
#check (diskAccessBound : Nat → Nat → Nat)

#check (searchCost_le_height : ∀ (x : Nat) (tr : BTree), searchCost x tr ≤ heightOf tr + 1)
#check (insertCost_le_height : ∀ (t x : Nat) (tr : BTree), insertCost t x tr ≤ heightOf tr + 1)
#check (insertRootCost_le_height :
  ∀ (t x : Nat), 2 ≤ t → ∀ {tr : BTree}, WellFormed t tr → insertRootCost t x tr ≤ heightOf tr + 3)
#check (deleteCost_le_height : ∀ (t x : Nat) (tr : BTree), deleteCost t x tr ≤ heightOf tr + 1)

#check (searchCost_le_diskAccessBound :
  ∀ (t : Nat), 2 ≤ t → ∀ {tr : BTree}, WellFormed t tr → ∀ (x : Nat),
    searchCost x tr ≤ diskAccessBound t (totalKeys tr))
#check (insertRootCost_le_diskAccessBound :
  ∀ (t : Nat), 2 ≤ t → ∀ {tr : BTree}, WellFormed t tr → ∀ (x : Nat),
    insertRootCost t x tr ≤ diskAccessBound t (totalKeys tr))
#check (deleteCost_le_diskAccessBound :
  ∀ (t : Nat), 2 ≤ t → ∀ {tr : BTree}, WellFormed t tr → ∀ (x : Nat),
    deleteCost t x tr ≤ diskAccessBound t (totalKeys tr))
#check (diskAccessBound_isBigO_log_t :
  ∀ (t : Nat), 2 ≤ t →
    CLRS.Chapter03.isBigO (fun n => (diskAccessBound t n : ℝ)) (fun n => (Nat.log t n : ℝ)))

example : searchCost 0 (node [] []) = 1 := by native_decide
example : insertCost 2 0 (node [] []) = 1 := by native_decide
example : deleteCost 2 0 (node [] []) = 1 := by native_decide
example : diskAccessBound 2 0 = 3 := by native_decide

end CLRS.Chapter18.BTree
