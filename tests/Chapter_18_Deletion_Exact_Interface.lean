import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact

namespace CLRS.Chapter18.BTree

#check (composedDelete_keyBag :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree} {b : Bool}, NodeWF t b tr →
      keyBag (composedDelete t x tr) = (keyBag tr).erase x)

#check (composedDelete_mem_iff_of_ne :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree} {b : Bool}, NodeWF t b tr →
      y ≠ x →
      (mem y (composedDelete t x tr) ↔ mem y tr))

#check (composedDelete_uniqueKeys :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree} {b : Bool}, NodeWF t b tr →
      UniqueKeys tr → UniqueKeys (composedDelete t x tr))

end CLRS.Chapter18.BTree
