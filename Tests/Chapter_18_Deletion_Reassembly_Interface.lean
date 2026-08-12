import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly

namespace CLRS.Chapter18.BTree

#check (replaceChild_keyBag_erase :
  ∀ {i x : Nat} {ks : List Nat} {cs : List BTree}
      {old new : BTree},
    cs[i]? = some old →
    (x ∈ keysOf (node ks cs) → x ∈ keysOf old) →
    keyBag new = (keyBag old).erase x →
    keyBag (node ks (cs.set i new)) =
      (keyBag (node ks cs)).erase x)

#check (replacePredecessor_keyBag_erase :
  ∀ {t i sep : Nat} {b : Bool}
      {ks : List Nat} {cs : List BTree}
      {left left' : BTree},
    2 ≤ t →
    NodeWF t b (node ks cs) →
    ks[i]? = some sep →
    cs[i]? = some left →
    keyBag left' = (keyBag left).erase (maxKey left) →
    keyBag (node (ks.set i (maxKey left)) (cs.set i left')) =
      (keyBag (node ks cs)).erase sep)

#check (replaceSuccessor_keyBag_erase :
  ∀ {t i sep : Nat} {b : Bool}
      {ks : List Nat} {cs : List BTree}
      {right right' : BTree},
    2 ≤ t →
    NodeWF t b (node ks cs) →
    ks[i]? = some sep →
    cs[i + 1]? = some right →
    keyBag right' = (keyBag right).erase (minKey right) →
    keyBag
        (node (ks.set i (minKey right))
          (cs.set (i + 1) right')) =
      (keyBag (node ks cs)).erase sep)

#check (spliceMerged_keyBag_erase :
  ∀ {j sep x : Nat} {ks : List Nat} {cs : List BTree}
      {left right newMerged : BTree},
    ks[j]? = some sep →
    cs[j]? = some left →
    cs[j + 1]? = some right →
    (x ∈ keysOf (node ks cs) →
      x ∈ keysOf (mergeNodes left sep right)) →
    keyBag newMerged =
      (keyBag (mergeNodes left sep right)).erase x →
    let out :=
      node (ks.take j ++ ks.drop (j + 1))
        (cs.take j ++ [newMerged] ++ cs.drop (j + 2))
    keyBag out = (keyBag (node ks cs)).erase x)

#check (rotateRight_reassembly_keyBag_erase :
  ∀ {j sep x : Nat} {ks : List Nat} {cs : List BTree}
      {left right left' : BTree},
    ks[j]? = some sep →
    cs[j]? = some left →
    cs[j + 1]? = some right →
    (x ∈ keysOf (node ks cs) → x ∈ keysOf left) →
    keyBag left' =
      (keyBag (rotateRight left sep right).1).erase x →
    let repaired := rotateRight left sep right
    keyBag
        (node (ks.set j repaired.2.1)
          ((cs.set j left').set (j + 1) repaired.2.2)) =
      (keyBag (node ks cs)).erase x)

#check (rotateLeft_reassembly_keyBag_erase :
  ∀ {j sep x : Nat} {ks : List Nat} {cs : List BTree}
      {left right right' : BTree},
    ks[j]? = some sep →
    cs[j]? = some left →
    cs[j + 1]? = some right →
    (x ∈ keysOf (node ks cs) → x ∈ keysOf right) →
    keyBag right' =
      (keyBag (rotateLeft left sep right).2.2).erase x →
    let repaired := rotateLeft left sep right
    keyBag
        (node (ks.set j repaired.2.1)
          ((cs.set j repaired.1).set (j + 1) right')) =
      (keyBag (node ks cs)).erase x)

end CLRS.Chapter18.BTree
