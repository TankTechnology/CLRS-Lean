import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ExactReassembly
import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.ComposedPreservation

/-!
# Exact semantics for raw B-tree deletion

This module proves that executable CLRS deletion removes exactly one occurrence
of the requested key.  The core theorem needs only the node invariant and the
minimum-degree bound; uniqueness and top-level descent readiness are not
required.
-/

namespace CLRS.Chapter18.BTree

private theorem NodeWF.node_keys_pairwise
    {t : Nat} {b : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t b (node ks cs)) :
    List.Pairwise (· ≤ ·) ks := by
  have hs := h.sorted
  unfold Sorted at hs
  exact hs.1

private theorem composedDelete_keyBag_aux
    (t : Nat) (ht : 2 ≤ t) (x : Nat) (tr : BTree) :
    ∀ b, NodeWF t b tr →
      keyBag (composedDelete t x tr) = (keyBag tr).erase x := by
  induction x, tr using composedDelete.induct (t := t) <;>
    intro b hparent
  case case1 =>
    rename_i x ks cs hleaf
    have hcs : cs = [] := List.isEmpty_iff.mp hleaf
    subst cs
    simpa [composedDelete, keyBag, keysOf] using
      (sortedRemove_keyBag x ks)
  case case2 =>
    rename_i ks cs hnonempty sep left right hleftReady i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hleftMem : left ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨findChild ks sep - 1, hleft⟩
    have hleftWF : NodeWF t false left :=
      hparent.child hleftMem
    have hrec := ih false hleftWF
    have hexact :=
      replacePredecessor_keyBag_erase ht hparent hsep hleft hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t sep (node ks cs) =
          node (ks.set (findChild ks sep - 1) (maxKey left))
            (cs.set (findChild ks sep - 1)
              (composedDelete t (maxKey left) left)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep]
      rw [hleft, hright]
      simp [hleftReady]
    rw [hdeleteEq]
    exact hexact
  case case3 =>
    rename_i ks cs hnonempty sep left right hleftNotReady hrightReady
      i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hrightMem : right ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨findChild ks sep - 1 + 1, hright⟩
    have hrightWF : NodeWF t false right :=
      hparent.child hrightMem
    have hrec := ih false hrightWF
    have hexact :=
      replaceSuccessor_keyBag_erase ht hparent hsep hright hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t sep (node ks cs) =
          node (ks.set (findChild ks sep - 1) (minKey right))
            (cs.set (findChild ks sep - 1 + 1)
              (composedDelete t (minKey right) right)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep]
      rw [hleft, hright]
      simp [hleftNotReady, hrightReady]
    rw [hdeleteEq]
    exact hexact
  case case4 =>
    rename_i ks cs hnonempty sep left right hleftNotReady hrightNotReady
      merged i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    obtain ⟨hleftWF, hrightWF, hsiblings, hleftLe, hrightGe⟩ :=
      hparent.adjacent_children hsep hleft hright
    have hleftMin : numKeys left = t - 1 :=
      numKeys_eq_t_sub_one_of_not_ready hleftWF.occupancy hleftNotReady
    have hrightMin : numKeys right = t - 1 :=
      numKeys_eq_t_sub_one_of_not_ready hrightWF.occupancy hrightNotReady
    have hmerged :=
      mergeNodes_nodeWF ht hleftWF hrightWF hleftMin hrightMin
        hsiblings hleftLe hrightGe
    have hmergedWF : NodeWF t false merged := by
      simpa [merged] using hmerged.1
    have hrec := ih false hmergedWF
    have hroute :
        sep ∈ keysOf (node ks cs) →
          sep ∈ keysOf (mergeNodes left sep right) := by
      intro _
      exact
        (mem_keysOf_mergeNodes left sep right sep).2
          (Or.inr (Or.inl rfl))
    have hexact :=
      spliceMerged_keyBag_erase hsep hleft hright hroute
        (by simpa [merged] using hrec)
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t sep (node ks cs) =
          node
            (ks.take (findChild ks sep - 1) ++
              ks.drop (findChild ks sep - 1 + 1))
            (cs.take (findChild ks sep - 1) ++
              [composedDelete t sep merged] ++
              cs.drop (findChild ks sep - 1 + 2)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep]
      rw [hleft, hright]
      simp [hleftNotReady, hrightNotReady, merged]
    rw [hdeleteEq]
    exact hexact
  case case7 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsep hne child hchild
      hchildReady ih
    simp only [i] at hpos
    simp only [ki, i] at hsep
    simp only [i] at hchild
    have hxkeys : x ∉ ks := by
      intro hx
      have hfound :=
        findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx
      have holdEq : oldSep = x :=
        Option.some.inj (hsep.symm.trans hfound.2)
      exact hne holdEq
    have hroute :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchild
    have hchildMem : child ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨findChild ks x, hchild⟩
    have hchildWF : NodeWF t false child :=
      hparent.child hchildMem
    have hrec := ih false hchildWF
    have hexact :=
      replaceChild_keyBag_erase hchild hroute hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node ks (cs.set (findChild ks x) (composedDelete t x child)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep]
      rw [hchild]
      simp [hchildReady]
      exact fun heq => (hne heq).elim
    rw [hdeleteEq]
    exact hexact
  case case8 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftReady sep hsep ih
    simp only [i] at hpos hchild hleft hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hxkeys : x ∉ ks := by
      intro hx
      have hfound :=
        findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx
      have hsepEq : sep = x :=
        Option.some.inj (hsep.symm.trans hfound.2)
      exact hne hsepEq
    have hroute :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchild
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    obtain ⟨hleftWF, hchildWF, hsiblings, hleftLe, hchildGe⟩ :=
      hparent.adjacent_children hsep hleft hchildAt
    have hchildMin : numKeys child = t - 1 :=
      numKeys_eq_t_sub_one_of_not_ready hchildWF.occupancy
        hchildNotReady
    have hrotated :=
      rotateLeft_nodeWF ht hleftWF hchildWF hleftReady hchildMin
        hsiblings hleftLe hchildGe
    have htargetWF :
        NodeWF t false (rotateLeft left sep child).2.2 :=
      hrotated.2.1
    have hrec := ih false htargetWF
    have hexactRaw :=
      rotateLeft_reassembly_keyBag_erase
        hsep hleft hchildAt hroute hrec
    have hexact :
        keyBag
            (node
              (ks.set (findChild ks x - 1)
                (rotateLeft left sep child).2.1)
              ((cs.set (findChild ks x - 1)
                (rotateLeft left sep child).1).set
                (findChild ks x)
                (composedDelete t x
                  (rotateLeft left sep child).2.2))) =
          (keyBag (node ks cs)).erase x := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hexactRaw
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.set (findChild ks x - 1)
              (rotateLeft left sep child).2.1)
            ((cs.set (findChild ks x - 1)
              (rotateLeft left sep child).1).set
              (findChild ks x)
              (composedDelete t x
                (rotateLeft left sep child).2.2)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld]
      rw [hchild]
      rw [hleft]
      simp [hne, hchildNotReady, hleftReady]
    rw [hdeleteEq]
    exact hexact
  case case10 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftNotReady right hright hrightReady
      sep hsep ih
    simp only [i] at hpos hchild hleft hright hsep
    simp only [ki, i] at hsepOld
    have hxkeys : x ∉ ks := by
      intro hx
      have hfound :=
        findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx
      have holdEq : oldSep = x :=
        Option.some.inj (hsepOld.symm.trans hfound.2)
      exact hne holdEq
    have hroute :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchild
    obtain ⟨hchildWF, hrightWF, hsiblings, hchildLe, hrightGe⟩ :=
      hparent.adjacent_children hsep hchild hright
    have hchildMin : numKeys child = t - 1 :=
      numKeys_eq_t_sub_one_of_not_ready hchildWF.occupancy
        hchildNotReady
    have hrotated :=
      rotateRight_nodeWF ht hchildWF hrightWF hchildMin hrightReady
        hsiblings hchildLe hrightGe
    have htargetWF :
        NodeWF t false (rotateRight child sep right).1 :=
      hrotated.1
    have hrec := ih false htargetWF
    have hexact :=
      rotateRight_reassembly_keyBag_erase
        hsep hchild hright hroute hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.set (findChild ks x)
              (rotateRight child sep right).2.1)
            ((cs.set (findChild ks x)
              (composedDelete t x
                (rotateRight child sep right).1)).set
              (findChild ks x + 1)
              (rotateRight child sep right).2.2) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld]
      rw [hchild]
      rw [hleft]
      rw [hright]
      rw [hsep]
      simp [hne, hchildNotReady, hleftNotReady, hrightReady]
    rw [hdeleteEq]
    exact hexact
  case case12 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftNotReady rightSib hrightSib
      hrightNotReady sep hsep ih
    simp only [i] at hpos hchild hleft hrightSib hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hxkeys : x ∉ ks := by
      intro hx
      have hfound :=
        findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx
      have hsepEq : sep = x :=
        Option.some.inj (hsep.symm.trans hfound.2)
      exact hne hsepEq
    have hrouteChild :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchild
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    obtain ⟨hleftWF, hchildWF, hsiblings, hleftLe, hchildGe⟩ :=
      hparent.adjacent_children hsep hleft hchildAt
    have htarget :=
      mergeNodes_recursiveTarget ht hleftWF hchildWF
        hleftNotReady hchildNotReady hsiblings hleftLe hchildGe
    have hrec := ih false htarget.1
    have hroute :
        x ∈ keysOf (node ks cs) →
          x ∈ keysOf (mergeNodes left sep child) := by
      intro hx
      exact
        (mem_keysOf_mergeNodes left sep child x).2
          (Or.inr (Or.inr (hrouteChild hx)))
    have hexactRaw :=
      spliceMerged_keyBag_erase hsep hleft hchildAt hroute hrec
    have hexact :
        keyBag
            (node
              (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
              (cs.take (findChild ks x - 1) ++
                [composedDelete t x (mergeNodes left sep child)] ++
                cs.drop (findChild ks x + 1))) =
          (keyBag (node ks cs)).erase x := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega,
        show findChild ks x - 1 + 2 = findChild ks x + 1 by omega]
        using hexactRaw
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
            (cs.take (findChild ks x - 1) ++
              [composedDelete t x (mergeNodes left sep child)] ++
              cs.drop (findChild ks x + 1)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld]
      rw [hchild]
      rw [hleft]
      rw [hrightSib]
      simp [hne, hchildNotReady, hleftNotReady, hrightNotReady]
    rw [hdeleteEq]
    exact hexact
  case case14 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftNotReady hrightNone sep hsep ih
    simp only [i] at hpos hchild hleft hrightNone hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hxkeys : x ∉ ks := by
      intro hx
      have hfound :=
        findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx
      have hsepEq : sep = x :=
        Option.some.inj (hsep.symm.trans hfound.2)
      exact hne hsepEq
    have hrouteChild :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchild
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    obtain ⟨hleftWF, hchildWF, hsiblings, hleftLe, hchildGe⟩ :=
      hparent.adjacent_children hsep hleft hchildAt
    have htarget :=
      mergeNodes_recursiveTarget ht hleftWF hchildWF
        hleftNotReady hchildNotReady hsiblings hleftLe hchildGe
    have hrec := ih false htarget.1
    have hroute :
        x ∈ keysOf (node ks cs) →
          x ∈ keysOf (mergeNodes left sep child) := by
      intro hx
      exact
        (mem_keysOf_mergeNodes left sep child x).2
          (Or.inr (Or.inr (hrouteChild hx)))
    have hexactRaw :=
      spliceMerged_keyBag_erase hsep hleft hchildAt hroute hrec
    have hexact :
        keyBag
            (node
              (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
              (cs.take (findChild ks x - 1) ++
                [composedDelete t x (mergeNodes left sep child)] ++
                cs.drop (findChild ks x + 1))) =
          (keyBag (node ks cs)).erase x := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega,
        show findChild ks x - 1 + 2 = findChild ks x + 1 by omega]
        using hexactRaw
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node
            (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
            (cs.take (findChild ks x - 1) ++
              [composedDelete t x (mergeNodes left sep child)] ++
              cs.drop (findChild ks x + 1)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepOld]
      rw [hchild]
      rw [hleft]
      rw [hrightNone]
      simp [hne, hchildNotReady, hleftNotReady]
    rw [hdeleteEq]
    exact hexact
  case case29 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildReady ih
    simp only [i] at hnotPos
    have hfindZero : findChild ks x = 0 :=
      Nat.eq_zero_of_not_pos hnotPos
    have hxkeys : x ∉ ks := by
      intro hx
      exact hnotPos
        (findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx).1
    have hchildSelected :
        cs[findChild ks x]? = some child := by
      simpa [hfindZero] using hchild
    have hroute :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchildSelected
    have hchildMem : child ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨0, hchild⟩
    have hchildWF : NodeWF t false child :=
      hparent.child hchildMem
    have hrec := ih false hchildWF
    have hexact :=
      replaceChild_keyBag_erase hchild hroute hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node ks (cs.set 0 (composedDelete t x child)) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [hchild]
      simp [hchildReady]
      exact fun hpos => (hnotPos hpos).elim
    rw [hdeleteEq]
    exact hexact
  case case30 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      right hright hrightReady sep hsep ih
    simp only [i] at hnotPos
    have hfindZero : findChild ks x = 0 :=
      Nat.eq_zero_of_not_pos hnotPos
    have hxkeys : x ∉ ks := by
      intro hx
      exact hnotPos
        (findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx).1
    have hchildSelected :
        cs[findChild ks x]? = some child := by
      simpa [hfindZero] using hchild
    have hroute :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchildSelected
    obtain ⟨hchildWF, hrightWF, hsiblings, hchildLe, hrightGe⟩ :=
      hparent.adjacent_children hsep hchild hright
    have hchildMin : numKeys child = t - 1 :=
      numKeys_eq_t_sub_one_of_not_ready hchildWF.occupancy
        hchildNotReady
    have hrotated :=
      rotateRight_nodeWF ht hchildWF hrightWF hchildMin hrightReady
        hsiblings hchildLe hrightGe
    have htargetWF :
        NodeWF t false (rotateRight child sep right).1 :=
      hrotated.1
    have hrec := ih false htargetWF
    have hexact :=
      rotateRight_reassembly_keyBag_erase hsep hchild hright hroute hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node (ks.set 0 (rotateRight child sep right).2.1)
            ((cs.set 0
              (composedDelete t x
                (rotateRight child sep right).1)).set 1
              (rotateRight child sep right).2.2) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild]
      simp only
      rw [dif_neg hchildNotReady]
      rw [hright]
      simp only
      rw [dif_pos hrightReady]
      rw [hsep]
    rw [hdeleteEq]
    exact hexact
  case case32 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      right hright hrightNotReady sep hsep ih
    simp only [i] at hnotPos
    have hfindZero : findChild ks x = 0 :=
      Nat.eq_zero_of_not_pos hnotPos
    have hxkeys : x ∉ ks := by
      intro hx
      exact hnotPos
        (findChild_pos_and_pred_eq_of_mem hparent.node_keys_pairwise hx).1
    have hchildSelected :
        cs[findChild ks x]? = some child := by
      simpa [hfindZero] using hchild
    have hrouteChild :
        x ∈ keysOf (node ks cs) → x ∈ keysOf child :=
      findChild_selected_child_mem hparent.node_keys_pairwise
        hparent.childBounded hxkeys hchildSelected
    obtain ⟨hchildWF, hrightWF, hsiblings, hchildLe, hrightGe⟩ :=
      hparent.adjacent_children hsep hchild hright
    have htarget :=
      mergeNodes_recursiveTarget ht hchildWF hrightWF
        hchildNotReady hrightNotReady hsiblings hchildLe hrightGe
    have hrec := ih false htarget.1
    have hroute :
        x ∈ keysOf (node ks cs) →
          x ∈ keysOf (mergeNodes child sep right) := by
      intro hx
      exact
        (mem_keysOf_mergeNodes child sep right x).2
          (Or.inl (hrouteChild hx))
    have hexact :=
      spliceMerged_keyBag_erase hsep hchild hright hroute hrec
    have hnotLeaf : cs.isEmpty = false :=
      Bool.eq_false_of_not_eq_true hnonempty
    have hdeleteEq :
        composedDelete t x (node ks cs) =
          node (ks.drop 1)
            ([composedDelete t x (mergeNodes child sep right)] ++
              cs.drop 2) := by
      rw [composedDelete]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild]
      simp only
      rw [dif_neg hchildNotReady]
      rw [hright]
      simp only
      rw [dif_neg hrightNotReady]
      rw [hsep]
    rw [hdeleteEq]
    simpa using hexact
  all_goals
    exfalso
    try dsimp only at *
    first
      | apply findChild_predecessor_none_absurd
        · assumption
        · assumption
      | apply hparent.findChild_leftSibling_none_absurd
        · assumption
      | apply hparent.findChild_none_absurd
        · assumption
      | have hrel := hparent.children_rel
        have htwo :=
          hparent.two_le_children_of_not_empty ht (by simp_all)
        simp_all [List.getElem?_eq_some_iff]
        all_goals
          obtain ⟨hindex, _⟩ := ‹∃ h : _ < _, _›
          omega

/--
Executable CLRS deletion removes exactly one occurrence of the requested key.
No uniqueness assumption and no top-level descent-readiness premise are needed.
-/
theorem composedDelete_keyBag
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree} {b : Bool}
    (hinv : NodeWF t b tr) :
    keyBag (composedDelete t x tr) =
      (keyBag tr).erase x := by
  exact composedDelete_keyBag_aux t ht x tr b hinv

/-- Deletion preserves membership of every key distinct from the request. -/
theorem composedDelete_mem_iff_of_ne
    (t x y : Nat) (ht : 2 ≤ t) {tr : BTree} {b : Bool}
    (hinv : NodeWF t b tr) (hyx : y ≠ x) :
    mem y (composedDelete t x tr) ↔ mem y tr := by
  have hbag := composedDelete_keyBag t x ht hinv
  have hmem :
      y ∈ (keyBag tr).erase x ↔ y ∈ keyBag tr :=
    Multiset.mem_erase_of_ne hyx
  rw [← hbag] at hmem
  simpa only [mem, keyBag, Multiset.mem_coe] using hmem

/--
Exact one-occurrence deletion preserves uniqueness of the flattened key list.
-/
theorem composedDelete_uniqueKeys
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree} {b : Bool}
    (hinv : NodeWF t b tr) (hunique : UniqueKeys tr) :
    UniqueKeys (composedDelete t x tr) := by
  unfold UniqueKeys at hunique ⊢
  have hbag := composedDelete_keyBag t x ht hinv
  have hcoe :
      (↑(keysOf (composedDelete t x tr)) : Multiset Nat) =
        ↑((keysOf tr).erase x) := by
    simpa only [keyBag, Multiset.coe_erase] using hbag
  have hperm :
      (keysOf (composedDelete t x tr)).Perm
        ((keysOf tr).erase x) :=
    Multiset.coe_eq_coe.mp hcoe
  exact hperm.nodup_iff.mpr (List.Nodup.erase x hunique)

end CLRS.Chapter18.BTree
