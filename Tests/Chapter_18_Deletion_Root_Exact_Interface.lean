import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.WellFormed
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Exact

namespace CLRS.Chapter18.BTree

#check (composedDeleteRoot_keyBag :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      keyBag (composedDeleteRoot t x tr) = (keyBag tr).erase x)

#check (composedDeleteRoot_mem_iff_of_ne :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr → y ≠ x →
      (mem y (composedDeleteRoot t x tr) ↔ mem y tr))

#check (composedDeleteRoot_not_mem :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      ¬ mem x (composedDeleteRoot t x tr))

#check (composedDeleteRoot_mem_iff :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      (mem y (composedDeleteRoot t x tr) ↔ y ≠ x ∧ mem y tr))

#check (composedDeleteRoot_wellFormedUnique :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      WellFormedUnique t (composedDeleteRoot t x tr))

#check (composedDeleteRoot_mem_iff_delete :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      (mem y (composedDeleteRoot t x tr) ↔ mem y (delete x tr)))

#check (composedDeleteRoot_search_eq_delete :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      search y (composedDeleteRoot t x tr) = search y (delete x tr))

#check (composedDeleteRoot_correct :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      keyBag (composedDeleteRoot t x tr) = (keyBag tr).erase x ∧
      WellFormed t (composedDeleteRoot t x tr) ∧
      (heightOf (composedDeleteRoot t x tr) = heightOf tr ∨
        heightOf (composedDeleteRoot t x tr) + 1 = heightOf tr))

end CLRS.Chapter18.BTree
