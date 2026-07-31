import CLRSLean.Chapter_18.Section_18_2_B_Tree_Insertion

namespace CLRS.Chapter18.BTree

#check (splitRoot : Nat → BTree → BTree)
#check (insertRoot : Nat → Nat → BTree → BTree)

#check (splitRoot_keys_perm :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, rootKeyCount tr = 2 * t - 1 →
      (keysOf (splitRoot t tr)).Perm (keysOf tr))

#check (splitRoot_wellFormed :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      rootKeyCount tr = 2 * t - 1 →
      WellFormed t (splitRoot t tr))

#check (splitRoot_height :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      rootKeyCount tr = 2 * t - 1 →
      heightOf (splitRoot t tr) = heightOf tr + 1)

#check (splitRoot_rootKeyCount :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, rootKeyCount tr = 2 * t - 1 →
      rootKeyCount (splitRoot t tr) = 1)

#check (splitRoot_nonFull :
  ∀ (t : Nat), 2 ≤ t →
    ∀ {tr : BTree}, rootKeyCount tr = 2 * t - 1 →
      rootKeyCount (splitRoot t tr) < 2 * t - 1)

#check (insertRoot_keys_perm :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (keysOf (insertRoot t x tr)).Perm (keysOf tr ++ [x]))

#check (insertRoot_wellFormed :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      WellFormed t (insertRoot t x tr))

#check (insertRoot_height :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      heightOf (insertRoot t x tr) =
        if rootKeyCount tr = 2 * t - 1 then heightOf tr + 1
        else heightOf tr)

#check (insertRoot_mem_iff :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (mem y (insertRoot t x tr) ↔ y = x ∨ mem y tr))

#check (insertRoot_wellFormedUnique :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormedUnique t tr →
      ¬ mem x tr →
      WellFormedUnique t (insertRoot t x tr))

#check (insertRoot_mem_iff_insert :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (mem y (insertRoot t x tr) ↔ mem y (insert x tr)))

#check (insertRoot_search_eq_insert :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      search y (insertRoot t x tr) = search y (insert x tr))

#check (insertRoot_searchExec_true_iff :
  ∀ (t x y : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (searchExec y (insertRoot t x tr) = true ↔ y = x ∨ mem y tr))

#check (insertRoot_correct :
  ∀ (t x : Nat), 2 ≤ t →
    ∀ {tr : BTree}, WellFormed t tr →
      (keysOf (insertRoot t x tr)).Perm (keysOf tr ++ [x]) ∧
      WellFormed t (insertRoot t x tr) ∧
      (heightOf (insertRoot t x tr) = heightOf tr ∨
        heightOf (insertRoot t x tr) = heightOf tr + 1))

example :
    rootKeyCount (splitRoot 2 (node [1, 2, 3] [])) = 1 := by
  native_decide

example :
    heightOf (insertRoot 2 4 (node [1, 2, 3] [])) = 1 := by
  native_decide

example :
    searchExec 4 (insertRoot 2 4 (node [1, 2, 3] [])) = true := by
  native_decide

end CLRS.Chapter18.BTree
