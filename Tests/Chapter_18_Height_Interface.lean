import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.HeightBound

namespace CLRS.Chapter18.BTree

#check (totalKeys : BTree → Nat)

#check (totalKeys_node :
  ∀ (ks : List Nat) (cs : List BTree),
    totalKeys (node ks cs) = ks.length + (cs.map totalKeys).sum)

#check (nonRoot_totalKeys_add_one_lower_bound :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, ChildBounded tr → Occupancy t false tr → SameDepth tr →
      t ^ (heightOf tr + 1) ≤ totalKeys tr + 1)

#check (wellFormed_empty_or_totalKeys_add_one_lower_bound :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      tr = node [] [] ∨
        2 * t ^ heightOf tr ≤ totalKeys tr + 1)

#check (wellFormed_empty_or_minKeys_le_totalKeys :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      tr = node [] [] ∨ minKeys t (heightOf tr) ≤ totalKeys tr)

#check (wellFormed_minKeys_le_totalKeys :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      tr ≠ node [] [] →
      minKeys t (heightOf tr) ≤ totalKeys tr)

#check (wellFormed_height_log_bound :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2))

example : totalKeys (node [] []) = 0 := by
  native_decide

example :
    heightOf (node [] []) ≤
      Nat.log 2 ((totalKeys (node [] []) + 1) / 2) := by
  native_decide

example :
    heightOf (node [1] []) ≤
      Nat.log 2 ((totalKeys (node [1] []) + 1) / 2) := by
  native_decide

example :
    heightOf (node [2] [node [1] [], node [3] []]) ≤
      Nat.log 2
        ((totalKeys (node [2] [node [1] [], node [3] []]) + 1) / 2) := by
  native_decide

end CLRS.Chapter18.BTree
