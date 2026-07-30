import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.Search

namespace CLRS.Chapter18.BTree

#check findChild
#check findChild_localizes_mem

#check (UniqueKeys : BTree → Prop)
#check (WellFormedUnique : Nat → BTree → Prop)

#check (findChild_pos_and_pred_eq_of_mem :
  ∀ {ks : List Nat} {x : Nat},
    List.Pairwise (· ≤ ·) ks → x ∈ ks →
      0 < findChild ks x ∧
        ks[findChild ks x - 1]? = some x)

#check (findChild_not_mem_child_of_ne :
  ∀ {ks : List Nat} {cs : List BTree} {x j : Nat} {child : BTree},
    List.Pairwise (· ≤ ·) ks →
    ChildBounded (node ks cs) →
    x ∉ ks →
    cs[j]? = some child →
    j ≠ findChild ks x →
    x ∉ keysOf child)

#check (findChild_selected_child_mem :
  ∀ {ks : List Nat} {cs : List BTree} {x : Nat} {child : BTree},
    List.Pairwise (· ≤ ·) ks →
    ChildBounded (node ks cs) →
    x ∉ ks →
    cs[findChild ks x]? = some child →
    x ∈ keysOf (node ks cs) →
    x ∈ keysOf child)

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
