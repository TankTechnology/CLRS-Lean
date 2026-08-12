import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.KeyMultiset

namespace CLRS.Chapter18.BTree

#check (keyBag : BTree → Multiset Nat)

#check (keyBag_erase_of_balance :
  ∀ {after before old new : Multiset Nat} {x : Nat},
    after + old = before + new →
    new = old.erase x →
    (x ∈ before → x ∈ old) →
    after = before.erase x)

#check (sortedRemove_keyBag :
  ∀ (x : Nat) (ks : List Nat),
    (↑(sortedRemove x ks) : Multiset Nat) =
      (↑ks : Multiset Nat).erase x)

#check (mergeNodes_keyBag :
  ∀ (left : BTree) (sep : Nat) (right : BTree),
    keyBag (mergeNodes left sep right) =
      keyBag left + {sep} + keyBag right)

#check (rotateRight_keyBag :
  ∀ (left : BTree) (sep : Nat) (right : BTree),
    keyBag (rotateRight left sep right).1 +
        {(rotateRight left sep right).2.1} +
        keyBag (rotateRight left sep right).2.2 =
      keyBag left + {sep} + keyBag right)

#check (rotateLeft_keyBag :
  ∀ (left : BTree) (sep : Nat) (right : BTree),
    keyBag (rotateLeft left sep right).1 +
        {(rotateLeft left sep right).2.1} +
        keyBag (rotateLeft left sep right).2.2 =
      keyBag left + {sep} + keyBag right)

example :
    (↑(keysOf (composedDelete 2 1 (node [1, 1] []))) : Multiset Nat) =
      ({1} : Multiset Nat) := by native_decide

example :
    keysOf (delete 1 (node [1, 1] [])) = [] := by native_decide

end CLRS.Chapter18.BTree
