import CLRSLean.FourthEdition.Chapter_17
open CLRS.Chapter14.OSRBTree
#check rankOf_eq_card_lt
#check osRank_eq_card_lt

open CLRS.Chapter14
open CLRS.Chapter13
private def sample : OSRBTree :=
  .node .black (.node .red .empty 2 1 .empty) 5 3 (.node .red .empty 8 1 .empty)
private theorem sized : WellSized sample := by simp [sample, WellSized, realSize]
private theorem ordered : RBTree.BST (toRB sample) := by
  simp [sample, toRB, RBTree.BST, RBTree.InTree]
example : osRank sample 0 = 0 := by decide
example : osRank sample 2 = 0 := by decide
example : osRank sample 4 = 1 := by decide
example : osRank sample 5 = 1 := by decide
example : osRank sample 9 = 3 := by decide
example (x : Nat) : osRank sample x = ((keys sample).toFinset.filter (fun y => y < x)).card :=
  osRank_eq_card_lt sized ordered x
