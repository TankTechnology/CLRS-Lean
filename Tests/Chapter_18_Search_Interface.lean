import CLRSLean.Chapter_18.Section_18_1_B_Tree_Search

namespace CLRS.Chapter18.BTree

#check findChild
#check findChild_localizes_mem
#check searchExec

#check (searchExec_sound :
  ∀ {x : Nat} {tr : BTree}, searchExec x tr = true → mem x tr)

#check (searchExec_complete :
  ∀ {x : Nat} {tr : BTree}, Sorted tr → ChildBounded tr →
    mem x tr → searchExec x tr = true)

#check (searchExec_true_iff :
  ∀ {x : Nat} {tr : BTree}, Sorted tr → ChildBounded tr →
    (searchExec x tr = true ↔ mem x tr))

#check (searchExec_eq_search :
  ∀ {x : Nat} {tr : BTree}, Sorted tr → ChildBounded tr →
    searchExec x tr = search x tr)

example : searchExec 10 (node [10] []) = true := by native_decide
example : searchExec 5 (node [10] [node [5] [], node [15] []]) = true := by native_decide
example : searchExec 15 (node [10] [node [5] [], node [15] []]) = true := by native_decide
example : searchExec 7 (node [10] [node [5] [], node [15] []]) = false := by native_decide
example : searchExec 1 (node [1, 1] []) = true := by native_decide

end CLRS.Chapter18.BTree
