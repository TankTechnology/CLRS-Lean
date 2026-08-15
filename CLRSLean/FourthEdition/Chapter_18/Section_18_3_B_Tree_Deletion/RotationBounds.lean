import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Repair

/-!
# Separator bounds after B-tree deletion rotations

This module packages the two cross-node ordering facts needed when a repaired
sibling pair is reassembled into its parent.  The proofs use the original
sibling's {lit}`Sorted` and {lit}`ChildBounded` invariants to account for the child
subtree that crosses the separator during a rotation.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/--
After borrowing from the right sibling, every key in the repaired left node is
at most the new separator, and every key in the repaired right node is at least
the new separator.
-/
theorem rotateRight_separator_bounds {t : Nat}
    {left right : BTree} {sep : Nat}
    (hright : NodeWF t false right)
    (hleftLe : ∀ k ∈ keysOf left, k ≤ sep)
    (hrightGe : ∀ k ∈ keysOf right, sep ≤ k) :
    let repaired := rotateRight left sep right
    (∀ k ∈ keysOf repaired.1, k ≤ repaired.2.1) ∧
      ∀ k ∈ keysOf repaired.2.2, repaired.2.1 ≤ k := by
  rcases left with ⟨lKeys, lCh⟩
  rcases right with ⟨rKeys, rCh⟩
  cases rKeys with
  | nil =>
      simp only [rotateRight_nil]
      exact ⟨hleftLe, hrightGe⟩
  | cons rHead rTail =>
      have hsepHead : sep ≤ rHead :=
        hrightGe rHead (by simp [keysOf])
      have hhead : (rHead :: rTail)[0] = rHead := by
        rfl
      have hrightSorted := hright.sorted
      unfold Sorted at hrightSorted
      have hmovedUpper :
          ∀ k ∈ keysOf (node [] (rCh.take 1)), k ≤ rHead := by
        simpa [hhead] using
          (keysOf_take_le_pivot (m := 0) hrightSorted.1
            hright.childBounded (by simp))
      have hrightLower :
          ∀ k ∈ keysOf (node rTail (rCh.drop 1)), rHead ≤ k := by
        simpa [hhead] using
          (keysOf_drop_ge_pivot (m := 0) hrightSorted.1
            hright.childBounded (by simp))
      simp only [rotateRight_cons]
      constructor
      · intro k hk
        simp only [keysOf, List.mem_append, List.mem_singleton,
          List.flatMap_append] at hk
        rcases hk with (hkey | rfl) | hchildren
        · exact (hleftLe k (by
            simp only [keysOf, List.mem_append]
            exact Or.inl hkey)).trans hsepHead
        · exact hsepHead
        · rcases hchildren with hchild | hmoved
          · exact (hleftLe k (by
              simp only [keysOf, List.mem_append]
              exact Or.inr hchild)).trans hsepHead
          · exact hmovedUpper k (by
              simpa only [keysOf, List.nil_append] using hmoved)
      · exact hrightLower

/--
After borrowing from the left sibling, every key in the repaired left node is
at most the new separator, and every key in the repaired right node is at least
the new separator.
-/
theorem rotateLeft_separator_bounds {t : Nat}
    {left right : BTree} {sep : Nat}
    (hleft : NodeWF t false left)
    (hleftLe : ∀ k ∈ keysOf left, k ≤ sep)
    (hrightGe : ∀ k ∈ keysOf right, sep ≤ k) :
    let repaired := rotateLeft left sep right
    (∀ k ∈ keysOf repaired.1, k ≤ repaired.2.1) ∧
      ∀ k ∈ keysOf repaired.2.2, repaired.2.1 ≤ k := by
  rcases left with ⟨lKeys, lCh⟩
  rcases right with ⟨rKeys, rCh⟩
  cases lKeys with
  | nil =>
      simp only [rotateLeft_nil]
      exact ⟨hleftLe, hrightGe⟩
  | cons lHead lTail =>
      have hpivot :
          (lHead :: lTail).getLast (List.cons_ne_nil lHead lTail) =
            (lHead :: lTail)[lTail.length] := by
        simpa using
          (List.getLast_eq_getElem (List.cons_ne_nil lHead lTail))
      have hchildrenCut :
          lCh.take (lCh.length - 1) = lCh.take (lTail.length + 1) ∧
            lCh.drop (lCh.length - 1) =
              lCh.drop (lTail.length + 1) := by
        rcases childBounded_children_rel hleft.childBounded with
          hleaf | hinternal
        · subst lCh
          simp
        · have hcut : lCh.length - 1 = lTail.length + 1 := by
            simp only [List.length_cons] at hinternal
            omega
          rw [hcut]
          exact ⟨rfl, rfl⟩
      have hleftSorted := hleft.sorted
      unfold Sorted at hleftSorted
      have hleftUpper :
          ∀ k ∈
              keysOf
                (node (lHead :: lTail).dropLast
                  (lCh.take (lCh.length - 1))),
            k ≤
              (lHead :: lTail).getLast
                (List.cons_ne_nil lHead lTail) := by
        intro k hk
        rw [List.dropLast_eq_take] at hk
        simp only [List.length_cons, Nat.add_sub_cancel] at hk
        rw [hchildrenCut.1] at hk
        have hbound :=
          keysOf_take_le_pivot (m := lTail.length) hleftSorted.1
            hleft.childBounded (by simp) k hk
        rwa [← hpivot] at hbound
      have hmovedLower :
          ∀ k ∈ keysOf (node [] (lCh.drop (lCh.length - 1))),
            (lHead :: lTail).getLast
                (List.cons_ne_nil lHead lTail) ≤
              k := by
        intro k hk
        rw [hchildrenCut.2] at hk
        have hk' :
            k ∈
              keysOf
                (node ((lHead :: lTail).drop (lTail.length + 1))
                  (lCh.drop (lTail.length + 1))) := by
          simpa using hk
        have hbound :=
          keysOf_drop_ge_pivot (m := lTail.length) hleftSorted.1
            hleft.childBounded (by simp) k hk'
        rwa [← hpivot] at hbound
      have hpivotLeSep :
          (lHead :: lTail).getLast
              (List.cons_ne_nil lHead lTail) ≤
            sep :=
        hleftLe _ (by
          simp only [keysOf, List.mem_append]
          exact
            Or.inl
              (List.getLast_mem
                (List.cons_ne_nil lHead lTail)))
      simp only [rotateLeft_cons]
      constructor
      · exact hleftUpper
      · intro k hk
        simp only [keysOf, List.mem_append, List.mem_cons,
          List.flatMap_append] at hk
        rcases hk with (rfl | hkey) | hchildren
        · exact hpivotLeSep
        · exact hpivotLeSep.trans
            (hrightGe k (by
              simp only [keysOf, List.mem_append]
              exact Or.inl hkey))
        · rcases hchildren with hmoved | hchild
          · exact hmovedLower k (by
              simpa only [keysOf, List.nil_append] using hmoved)
          · exact hpivotLeSep.trans
              (hrightGe k (by
                simp only [keysOf, List.mem_append]
                exact Or.inr hchild))

end BTree
end Chapter18
end CLRS
