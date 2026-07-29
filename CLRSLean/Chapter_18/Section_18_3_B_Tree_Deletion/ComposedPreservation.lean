import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Preservation
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.MergeReassembly
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.RotationReassembly

/-!
# Complete structural preservation for composed B-tree deletion

The branch packets for leaf deletion, separator replacement, sibling
rotation, and sibling merge are assembled here into one induction over
{lit}`composedDelete`.  The bundled result simultaneously records key
containment, the root-sensitive structural postcondition, and raw height
preservation.
-/

namespace CLRS.Chapter18.BTree

/--
Raw composed deletion preserves the complete invariant packet under the CLRS
descent-readiness guard.  Root calls may return the one-child empty-root
transient described by {name}`RootDeleteResult`; non-root calls return an
ordinary {name}`NodeWF` packet.
-/
theorem composedDelete_packet
    (t : Nat) (ht : 2 ≤ t) (x : Nat) (tr : BTree) :
    ∀ b, NodeWF t b tr → DeleteReady t b tr →
      KeysSubset (composedDelete t x tr) tr ∧
        RawDeleteResult t b (composedDelete t x tr) ∧
        heightOf (composedDelete t x tr) = heightOf tr := by
  induction x, tr using composedDelete.induct (t := t) <;>
    intro b hparent hready
  case case1 =>
    rename_i x ks cs hleaf
    have hcs : cs = [] := List.isEmpty_iff.mp hleaf
    subst cs
    simpa [composedDelete] using
      (deleteLeaf_packet (x := x) hparent hready)
  case case2 =>
    rename_i ks cs hnonempty sep left right hleftReady i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hleftMem : left ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨findChild ks sep - 1, hleft⟩
    have hleftWF : NodeWF t false left :=
      hparent.child hleftMem
    have hleftReady' : DeleteReady t false left := by
      simpa [DeleteReady] using hleftReady
    have hrec := ih false hleftWF hleftReady'
    have hrecWF :
        NodeWF t false (composedDelete t (maxKey left) left) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      replacePredecessor_packet ht hparent hsep hleft hrecWF
        hrec.2.2 hrec.1
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case3 =>
    rename_i ks cs hnonempty sep left right hleftNotReady hrightReady
      i hpos ki hsep hleft hright ih
    simp only [i] at hpos
    simp only [ki, i] at hsep hleft hright
    have hrightMem : right ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨findChild ks sep - 1 + 1, hright⟩
    have hrightWF : NodeWF t false right :=
      hparent.child hrightMem
    have hrightReady' : DeleteReady t false right := by
      simpa [DeleteReady] using hrightReady
    have hrec := ih false hrightWF hrightReady'
    have hrecWF :
        NodeWF t false (composedDelete t (minKey right) right) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      replaceSuccessor_packet ht hparent hsep hright hrecWF
        hrec.2.2 hrec.1
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
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
    have hmergedReady : DeleteReady t false merged := by
      simpa [merged] using
        (mergeNodes_deleteReady ht (right := right) (sep := sep) hleftMin)
    have hrec := ih false hmergedWF hmergedReady
    have hrecWF :
        NodeWF t false (composedDelete t sep merged) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      spliceMerged_packet hparent hready hsep hleft hright hrecWF
        (by simpa [merged] using hrec.2.2) (by simpa [merged] using hrec.1)
    have hraw :
        RawDeleteResult t b
          (node
            (ks.take (findChild ks sep - 1) ++
              ks.drop (findChild ks sep - 1 + 1))
            (cs.take (findChild ks sep - 1) ++
              [composedDelete t sep merged] ++
              cs.drop (findChild ks sep - 1 + 2))) := by
      cases b <;> simpa [RawDeleteResult] using hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case7 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsep hne child hchild
      hchildReady ih
    simp only [i] at hpos
    simp only [ki, i] at hsep
    simp only [i] at hchild
    have hchildMem : child ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨findChild ks x, hchild⟩
    have hchildWF : NodeWF t false child :=
      hparent.child hchildMem
    have hchildReady' : DeleteReady t false child := by
      simpa [DeleteReady] using hchildReady
    have hrec := ih false hchildWF hchildReady'
    have hrecWF :
        NodeWF t false (composedDelete t x child) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      replaceChild_packet hparent hchild hrecWF hrec.2.2 hrec.1
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case8 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftReady sep hsep ih
    simp only [i] at hpos hchild hleft hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
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
    have htargetReady :
        DeleteReady t false (rotateLeft left sep child).2.2 :=
      rotateLeft_repaired_deleteReady ht hleftReady hchildMin
    have hrec := ih false htargetWF htargetReady
    have hrecWF :
        NodeWF t false
          (composedDelete t x (rotateLeft left sep child).2.2) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacketRaw :=
      rotateLeft_reassembly_packet ht hparent hsep hleft hchildAt
        hleftReady hchildMin hrecWF hrec.2.2 hrec.1
    have hpacket :
        NodeWF t b
            (node
              (ks.set (findChild ks x - 1)
                (rotateLeft left sep child).2.1)
              ((cs.set (findChild ks x - 1)
                (rotateLeft left sep child).1).set
                (findChild ks x)
                (composedDelete t x
                  (rotateLeft left sep child).2.2))) ∧
          heightOf
              (node
                (ks.set (findChild ks x - 1)
                  (rotateLeft left sep child).2.1)
                ((cs.set (findChild ks x - 1)
                  (rotateLeft left sep child).1).set
                  (findChild ks x)
                  (composedDelete t x
                    (rotateLeft left sep child).2.2))) =
            heightOf (node ks cs) ∧
          KeysSubset
            (node
              (ks.set (findChild ks x - 1)
                (rotateLeft left sep child).2.1)
              ((cs.set (findChild ks x - 1)
                (rotateLeft left sep child).1).set
                (findChild ks x)
                (composedDelete t x
                  (rotateLeft left sep child).2.2)))
            (node ks cs) := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hpacketRaw
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case10 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftNotReady right hright hrightReady
      sep hsep ih
    simp only [i] at hpos hchild hleft hright hsep
    simp only [ki, i] at hsepOld
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
    have htargetReady :
        DeleteReady t false (rotateRight child sep right).1 :=
      rotateRight_repaired_deleteReady ht hchildMin hrightReady
    have hrec := ih false htargetWF htargetReady
    have hrecWF :
        NodeWF t false
          (composedDelete t x (rotateRight child sep right).1) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      rotateRight_reassembly_packet ht hparent hsep hchild hright
        hchildMin hrightReady hrecWF hrec.2.2 hrec.1
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case12 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftNotReady rightSib hrightSib
      hrightNotReady sep hsep ih
    simp only [i] at hpos hchild hleft hrightSib hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    obtain ⟨hleftWF, hchildWF, hsiblings, hleftLe, hchildGe⟩ :=
      hparent.adjacent_children hsep hleft hchildAt
    have htarget :=
      mergeNodes_recursiveTarget ht hleftWF hchildWF
        hleftNotReady hchildNotReady hsiblings hleftLe hchildGe
    have hrec := ih false htarget.1 htarget.2.1
    have hrecWF :
        NodeWF t false
          (composedDelete t x (mergeNodes left sep child)) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      spliceMerged_left_packet hpos hparent hready hsep hleft hchild
        hrecWF hrec.2.2 hrec.1
    have hraw :
        RawDeleteResult t b
          (node
            (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
            (cs.take (findChild ks x - 1) ++
              [composedDelete t x (mergeNodes left sep child)] ++
              cs.drop (findChild ks x + 1))) := by
      simpa [RawDeleteResult] using hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case14 =>
    rename_i x ks cs hnonempty i hpos ki oldSep hsepOld hne child hchild
      hchildNotReady left hleft hleftNotReady hrightNone sep hsep ih
    simp only [i] at hpos hchild hleft hrightNone hsep
    simp only [ki, i] at hsepOld
    have holdSepEq : oldSep = sep :=
      Option.some.inj (hsepOld.symm.trans hsep)
    subst oldSep
    have hchildAt :
        cs[(findChild ks x - 1) + 1]? = some child := by
      simpa [show findChild ks x - 1 + 1 = findChild ks x by omega]
        using hchild
    obtain ⟨hleftWF, hchildWF, hsiblings, hleftLe, hchildGe⟩ :=
      hparent.adjacent_children hsep hleft hchildAt
    have htarget :=
      mergeNodes_recursiveTarget ht hleftWF hchildWF
        hleftNotReady hchildNotReady hsiblings hleftLe hchildGe
    have hrec := ih false htarget.1 htarget.2.1
    have hrecWF :
        NodeWF t false
          (composedDelete t x (mergeNodes left sep child)) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      spliceMerged_left_packet hpos hparent hready hsep hleft hchild
        hrecWF hrec.2.2 hrec.1
    have hraw :
        RawDeleteResult t b
          (node
            (ks.take (findChild ks x - 1) ++ ks.drop (findChild ks x))
            (cs.take (findChild ks x - 1) ++
              [composedDelete t x (mergeNodes left sep child)] ++
              cs.drop (findChild ks x + 1))) := by
      simpa [RawDeleteResult] using hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case29 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildReady ih
    simp only [i] at hnotPos
    have hchildMem : child ∈ cs :=
      List.mem_iff_getElem?.mpr ⟨0, hchild⟩
    have hchildWF : NodeWF t false child :=
      hparent.child hchildMem
    have hchildReady' : DeleteReady t false child := by
      simpa [DeleteReady] using hchildReady
    have hrec := ih false hchildWF hchildReady'
    have hrecWF :
        NodeWF t false (composedDelete t x child) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      replaceChild_packet hparent hchild hrecWF hrec.2.2 hrec.1
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case30 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      right hright hrightReady sep hsep ih
    simp only [i] at hnotPos
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
    have htargetReady :
        DeleteReady t false (rotateRight child sep right).1 :=
      rotateRight_repaired_deleteReady ht hchildMin hrightReady
    have hrec := ih false htargetWF htargetReady
    have hrecWF :
        NodeWF t false
          (composedDelete t x (rotateRight child sep right).1) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      rotateRight_reassembly_packet ht hparent hsep hchild hright
        hchildMin hrightReady hrecWF hrec.2.2 hrec.1
    have hraw :=
      rawDeleteResult_of_nodeWF hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
  case case32 =>
    rename_i x ks cs hnonempty i hnotPos child hchild hchildNotReady
      right hright hrightNotReady sep hsep ih
    simp only [i] at hnotPos
    obtain ⟨hchildWF, hrightWF, hsiblings, hchildLe, hrightGe⟩ :=
      hparent.adjacent_children hsep hchild hright
    have htarget :=
      mergeNodes_recursiveTarget ht hchildWF hrightWF
        hchildNotReady hrightNotReady hsiblings hchildLe hrightGe
    have hrec := ih false htarget.1 htarget.2.1
    have hrecWF :
        NodeWF t false
          (composedDelete t x (mergeNodes child sep right)) := by
      simpa [RawDeleteResult] using hrec.2.1
    have hpacket :=
      spliceMerged_zero_packet hparent hready hsep hchild hright
        hrecWF hrec.2.2 hrec.1
    have hraw :
        RawDeleteResult t b
          (node (ks.drop 1)
            ([composedDelete t x (mergeNodes child sep right)] ++
              cs.drop 2)) := by
      simpa [RawDeleteResult] using hpacket.1
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
    exact And.intro hpacket.2.2 (And.intro hraw hpacket.2.1)
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
Raw deletion at a non-root node preserves its invariant packet, represented
keys, and height when the CLRS descent guard holds.
-/
theorem composedDelete_nonRoot_preserves
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hinv : NodeWF t false tr)
    (hready : t ≤ numKeys tr) :
    let out := composedDelete t x tr
    KeysSubset out tr ∧
      NodeWF t false out ∧
      heightOf out = heightOf tr := by
  have hpacket :=
    composedDelete_packet t ht x tr false hinv
      (by simpa [DeleteReady] using hready)
  simpa [RawDeleteResult] using hpacket

/--
Raw deletion at the root preserves keys and height and returns either an
ordinary root or the single-child transient consumed by root normalization.
-/
theorem composedDelete_rootResult
    (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    let out := composedDelete t x tr
    KeysSubset out tr ∧
      RootDeleteResult t out ∧
      heightOf out = heightOf tr := by
  have hpacket :=
    composedDelete_packet t ht x tr true hwf (deleteReady_root t tr)
  simpa [RawDeleteResult] using hpacket

end CLRS.Chapter18.BTree
