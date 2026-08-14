import CLRSLean.FourthEdition.Chapter_13

namespace CLRS.Chapter13.RBTree

#check (WellFormed : RBTree → Prop)
#check WellFormed.redBlackShape
#check WellFormed.bst
#check wellFormed_empty
#check wellFormed_insert
#check wellFormed_delete
#check insert_correct
#check delete_correct

example : WellFormed empty := wellFormed_empty

example {t : RBTree} (h : WellFormed t) (x y : Nat) :
    WellFormed (delete y (insert x t)) :=
  wellFormed_delete (wellFormed_insert h)

example {t : RBTree} (h : WellFormed t) (x q : Nat) :
    InTree q (delete x t) ↔ InTree q t ∧ q ≠ x :=
  (delete_correct h).2 q

end CLRS.Chapter13.RBTree
