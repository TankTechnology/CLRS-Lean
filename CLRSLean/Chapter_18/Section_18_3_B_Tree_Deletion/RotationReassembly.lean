import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Reassembly
import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.RotationBounds

/-!
# Parent reassembly after B-tree deletion rotations

These packets cover the two case-3a descent branches.  A sibling rotation
changes a separator and both adjacent children atomically; after the recursive
call returns, the repaired borrower is then replaced by its equal-height
key-subset result.
-/

namespace CLRS
namespace Chapter18
namespace BTree

private theorem replaceAdjacent_keysSubset
    {j sep newSep : Nat} {ks : List Nat} {cs : List BTree}
    {left right newLeft newRight : BTree}
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hrotation :
      ∀ k,
        (k ∈ keysOf newLeft ∨ k = newSep ∨ k ∈ keysOf newRight) ↔
          (k ∈ keysOf left ∨ k = sep ∨ k ∈ keysOf right)) :
    KeysSubset
      (node (ks.set j newSep)
        ((cs.set j newLeft).set (j + 1) newRight))
      (node ks cs) := by
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j, hleft⟩
  have hrightMem : right ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j + 1, hright⟩
  have hsepMem : sep ∈ ks :=
    List.mem_iff_getElem?.mpr ⟨j, hsep⟩
  have hsource :
      ∀ k, k ∈ keysOf left ∨ k = sep ∨ k ∈ keysOf right →
        k ∈ keysOf (node ks cs) := by
    intro k hk
    simp only [keysOf, List.mem_append, List.mem_flatMap]
    rcases hk with hkLeft | rfl | hkRight
    · exact Or.inr ⟨left, hleftMem, hkLeft⟩
    · exact Or.inl hsepMem
    · exact Or.inr ⟨right, hrightMem, hkRight⟩
  intro k hk
  simp only [keysOf, List.mem_append, List.mem_flatMap] at hk
  rcases hk with hkey | ⟨child, hchild, hkChild⟩
  · rcases List.mem_or_eq_of_mem_set hkey with hkeyOld | rfl
    · simp only [keysOf, List.mem_append]
      exact Or.inl hkeyOld
    · exact hsource k
        ((hrotation k).mp (Or.inr (Or.inl rfl)))
  · rcases List.mem_or_eq_of_mem_set hchild with hchildFirst | rfl
    · rcases List.mem_or_eq_of_mem_set hchildFirst with hchildOld | rfl
      · simp only [keysOf, List.mem_append, List.mem_flatMap]
        exact Or.inr ⟨child, hchildOld, hkChild⟩
      · exact hsource k
          ((hrotation k).mp (Or.inl hkChild))
    · exact hsource k
        ((hrotation k).mp (Or.inr (Or.inr hkChild)))

private theorem rotateRight_right_keysSubset
    (left : BTree) (sep : Nat) (right : BTree) :
    KeysSubset (rotateRight left sep right).2.2 right := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases rKeys with
  | nil =>
      simp only [rotateRight_nil]
      exact KeysSubset.refl _
  | cons rHead rTail =>
      intro k hk
      simp only [rotateRight_cons, keysOf, List.mem_append,
        List.mem_flatMap] at hk ⊢
      rcases hk with hkKey | ⟨child, hchild, hkChild⟩
      · exact Or.inl (List.mem_cons_of_mem rHead hkKey)
      · exact Or.inr
          ⟨child, List.mem_of_mem_drop hchild, hkChild⟩

private theorem rotateLeft_left_keysSubset
    (left : BTree) (sep : Nat) (right : BTree) :
    KeysSubset (rotateLeft left sep right).1 left := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases lKeys with
  | nil =>
      simp only [rotateLeft_nil]
      exact KeysSubset.refl _
  | cons lHead lTail =>
      intro k hk
      simp only [rotateLeft_cons, keysOf, List.mem_append,
        List.mem_flatMap] at hk ⊢
      rcases hk with hkKey | ⟨child, hchild, hkChild⟩
      · exact Or.inl (List.mem_of_mem_dropLast hkKey)
      · exact Or.inr
          ⟨child, List.mem_of_mem_take hchild, hkChild⟩

private lemma rotateRight_newSeparator_mem_right
    {t : Nat} (ht : 2 ≤ t)
    (left : BTree) (sep : Nat) (right : BTree)
    (hrightKeys : t ≤ numKeys right) :
    (rotateRight left sep right).2.1 ∈ keysOf right := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases rKeys with
  | nil =>
      simp only [numKeys, List.length_nil] at hrightKeys
      omega
  | cons rHead rTail =>
      simp [rotateRight_cons, keysOf]

private lemma rotateLeft_newSeparator_mem_left
    {t : Nat} (ht : 2 ≤ t)
    (left : BTree) (sep : Nat) (right : BTree)
    (hleftKeys : t ≤ numKeys left) :
    (rotateLeft left sep right).2.1 ∈ keysOf left := by
  rcases left with ⟨lKeys, lChildren⟩
  rcases right with ⟨rKeys, rChildren⟩
  cases lKeys with
  | nil =>
      simp only [numKeys, List.length_nil] at hleftKeys
      omega
  | cons lHead lTail =>
      simp only [rotateLeft_cons, keysOf, List.mem_append]
      exact Or.inl (List.getLast_mem (List.cons_ne_nil lHead lTail))

/-!
The public packets follow.  Each proof first installs the sibling that only
loses material, changes the separator, installs the sibling that gains
material with explicit outer bounds, and finally installs the recursive
borrower result.
-/

/--
Reassemble a parent after borrowing from its right sibling and recursively
deleting from the repaired left child.
-/
theorem rotateRight_reassembly_packet
    {t j sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree}
    {left right left' : BTree}
    (ht : 2 ≤ t)
    (hparent : NodeWF t b (node ks cs))
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hleftKeys : numKeys left = t - 1)
    (hrightKeys : t ≤ numKeys right)
    (hleft' : NodeWF t false left')
    (hheight :
      heightOf left' = heightOf (rotateRight left sep right).1)
    (hsubset :
      KeysSubset left' (rotateRight left sep right).1) :
    let repaired := rotateRight left sep right
    NodeWF t b
        (node (ks.set j repaired.2.1)
          ((cs.set j left').set (j + 1) repaired.2.2)) ∧
      heightOf
          (node (ks.set j repaired.2.1)
            ((cs.set j left').set (j + 1) repaired.2.2)) =
        heightOf (node ks cs) ∧
      KeysSubset
        (node (ks.set j repaired.2.1)
          ((cs.set j left').set (j + 1) repaired.2.2))
        (node ks cs) := by
  dsimp only
  obtain ⟨hjKey, hsepGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hsep
  obtain ⟨hjLeft, hleftGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hleft
  obtain ⟨hjRight, hrightGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hright
  have hleftGet : cs.get ⟨j, hjLeft⟩ = left := by
    rw [List.get_eq_getElem]
    exact hleftGetElem
  have hrightGet : cs.get ⟨j + 1, hjRight⟩ = right := by
    rw [List.get_eq_getElem]
    exact hrightGetElem
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j, hleft⟩
  have hrightMem : right ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j + 1, hright⟩
  have hleftWF : NodeWF t false left :=
    hparent.child hleftMem
  have hrightWF : NodeWF t false right :=
    hparent.child hrightMem
  have hsiblings : heightOf left = heightOf right :=
    hparent.siblings_height hleftMem hrightMem

  have hparentSorted := hparent.sorted
  unfold Sorted at hparentSorted
  have hparentBounded := hparent.childBounded
  unfold ChildBounded at hparentBounded
  obtain ⟨_, hbounds, _⟩ := hparentBounded
  have hleftBounds := hbounds j hjLeft
  rw [hleftGet] at hleftBounds
  have hrightBounds := hbounds (j + 1) hjRight
  rw [hrightGet] at hrightBounds
  have hleftLe : ∀ k ∈ keysOf left, k ≤ sep := by
    have hupper := hleftBounds.2
    rw [hsep] at hupper
    exact hupper
  have hrightGe : ∀ k ∈ keysOf right, sep ≤ k := by
    rcases hrightBounds.1 with hzero | hlower
    · omega
    · rw [show j + 1 - 1 = j by omega, hsep] at hlower
      exact hlower

  have hrepair :=
    rotateRight_nodeWF ht hleftWF hrightWF hleftKeys hrightKeys
      hsiblings hleftLe hrightGe
  dsimp only at hrepair
  have hcross :=
    rotateRight_separator_bounds hrightWF hleftLe hrightGe
  dsimp only at hcross
  have hnewSepMem :
      (rotateRight left sep right).2.1 ∈ keysOf right :=
    rotateRight_newSeparator_mem_right ht left sep right hrightKeys
  have hsepLeNew : sep ≤ (rotateRight left sep right).2.1 :=
    hrightGe _ hnewSepMem

  have htrimRight :=
    replaceChild_packet hparent hright hrepair.2.1 hrepair.2.2.2
      (rotateRight_right_keysSubset left sep right)

  have hprefix :
      ∀ k ∈ ks.take j, k ≤ (rotateRight left sep right).2.1 := by
    intro k hk
    have hkSep : k ≤ ks[j] :=
      ReassemblyInternal.pairwise_take_le_get
        hparentSorted.1 hjKey
        (by omega) k hk
    rw [hsepGetElem] at hkSep
    exact hkSep.trans hsepLeNew
  have hsuffix :
      ∀ k ∈ ks.drop (j + 1),
        (rotateRight left sep right).2.1 ≤ k := by
    intro k hk
    rcases List.mem_iff_get.mp hk with ⟨q, _⟩
    have hnextIndex : j + 1 < ks.length := by
      have hq' : q.val < ks.length - (j + 1) := by
        simpa only [List.length_drop] using q.isLt
      omega
    have hupper := hrightBounds.2
    rw [List.getElem?_eq_getElem hnextIndex] at hupper
    have hnewLeNext :
        (rotateRight left sep right).2.1 ≤ ks[j + 1] :=
      hupper _ hnewSepMem
    exact hnewLeNext.trans
      (ReassemblyInternal.pairwise_get_le_drop
        hparentSorted.1 hnextIndex
        (by omega) k hk)
  have hleftAfterTrim :
      (cs.set (j + 1) (rotateRight left sep right).2.2)[j]? =
        some left := by
    rw [List.getElem?_set_ne (by omega : j + 1 ≠ j)]
    exact hleft
  have hleftChild :
      ∀ child,
        (cs.set (j + 1) (rotateRight left sep right).2.2)[j]? =
            some child →
          ∀ k ∈ keysOf child,
            k ≤ (rotateRight left sep right).2.1 := by
    intro child hchild
    have hchildEq : child = left :=
      Option.some.inj (hchild.symm.trans hleftAfterTrim)
    subst child
    intro k hk
    exact (hleftLe k hk).trans hsepLeNew
  have hrightChild :
      ∀ child,
        (cs.set (j + 1) (rotateRight left sep right).2.2)[j + 1]? =
            some child →
          ∀ k ∈ keysOf child,
            (rotateRight left sep right).2.1 ≤ k := by
    intro child hchild
    have hset :
        (cs.set (j + 1) (rotateRight left sep right).2.2)[j + 1]? =
          some (rotateRight left sep right).2.2 :=
      List.getElem?_set_eq_of_lt _ hjRight
    have hchildEq : child = (rotateRight left sep right).2.2 :=
      Option.some.inj (hchild.symm.trans hset)
    subst child
    exact hcross.2
  have hseparator :=
    replaceSeparator_nodeWF htrimRight.1 hjKey hprefix hsuffix
      hleftChild hrightChild

  have hnewLeftLower :
      j = 0 ∨
        (match
            (ks.set j (rotateRight left sep right).2.1)[j - 1]?
        with
        | some lower =>
            ∀ k ∈ keysOf (rotateRight left sep right).1, lower ≤ k
        | none => True) := by
    by_cases hjZero : j = 0
    · exact Or.inl hjZero
    · right
      rw [List.getElem?_set_ne (by omega : j ≠ j - 1)]
      cases hprev : ks[j - 1]? with
      | none => trivial
      | some lower =>
          obtain ⟨hprevIndex, hprevGetElem⟩ :=
            List.getElem?_eq_some_iff.mp hprev
          have hprevLeSep : lower ≤ sep := by
            have hp :=
              pairwise_get_mono hparentSorted.1
                (by omega) hprevIndex hjKey
            simpa [hprevGetElem, hsepGetElem] using hp
          intro k hk
          have hsource :=
            (mem_keysOf_rotateRight left sep right k).mp
              (Or.inl hk)
          rcases hsource with hkLeft | rfl | hkRight
          · rcases hleftBounds.1 with hzero | hlower
            · exact absurd hzero hjZero
            · rw [hprev] at hlower
              exact hlower k hkLeft
          · exact hprevLeSep
          · exact hprevLeSep.trans (hrightGe k hkRight)
  have hnewLeftUpper :
      match (ks.set j (rotateRight left sep right).2.1)[j]? with
      | some upper =>
          ∀ k ∈ keysOf (rotateRight left sep right).1, k ≤ upper
      | none => True := by
    rw [List.getElem?_set_eq_of_lt _ hjKey]
    exact hcross.1

  have hrotatedReverse :=
    ReassemblyInternal.replaceChild_nodeWF_height_of_bounds
      hseparator.1 hleftAfterTrim hrepair.1 hrepair.2.2.1
      hnewLeftLower hnewLeftUpper
  have hcomm :
      (cs.set (j + 1) (rotateRight left sep right).2.2).set j
          (rotateRight left sep right).1 =
        (cs.set j (rotateRight left sep right).1).set (j + 1)
          (rotateRight left sep right).2.2 :=
    List.set_comm _ _ (by omega)
  rw [hcomm] at hrotatedReverse
  have hrotatedHeight :
      heightOf
          (node (ks.set j (rotateRight left sep right).2.1)
            ((cs.set j (rotateRight left sep right).1).set (j + 1)
              (rotateRight left sep right).2.2)) =
        heightOf (node ks cs) :=
    hrotatedReverse.2.trans
      (hseparator.2.trans htrimRight.2.1)
  have hrotatedSubset :
      KeysSubset
        (node (ks.set j (rotateRight left sep right).2.1)
          ((cs.set j (rotateRight left sep right).1).set (j + 1)
            (rotateRight left sep right).2.2))
        (node ks cs) :=
    replaceAdjacent_keysSubset hsep hleft hright
      (mem_keysOf_rotateRight left sep right)
  have hleftAtRotated :
      ((cs.set j (rotateRight left sep right).1).set (j + 1)
          (rotateRight left sep right).2.2)[j]? =
        some (rotateRight left sep right).1 := by
    rw [List.getElem?_set_ne (by omega : j + 1 ≠ j),
      List.getElem?_set_eq_of_lt _ hjLeft]

  have hfinal :=
    replaceChild_packet hrotatedReverse.1 hleftAtRotated hleft'
      hheight hsubset
  have hfinalChildren :
      (((cs.set j (rotateRight left sep right).1).set (j + 1)
            (rotateRight left sep right).2.2).set j left') =
        (cs.set j left').set (j + 1)
          (rotateRight left sep right).2.2 := by
    rw [List.set_comm _ _ (by omega : j + 1 ≠ j), List.set_set]
  rw [hfinalChildren] at hfinal
  exact
    ⟨hfinal.1,
      hfinal.2.1.trans hrotatedHeight,
      hfinal.2.2.trans hrotatedSubset⟩

/--
Reassemble a parent after borrowing from its left sibling and recursively
deleting from the repaired right child.
-/
theorem rotateLeft_reassembly_packet
    {t j sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree}
    {left right right' : BTree}
    (ht : 2 ≤ t)
    (hparent : NodeWF t b (node ks cs))
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hleftKeys : t ≤ numKeys left)
    (hrightKeys : numKeys right = t - 1)
    (hright' : NodeWF t false right')
    (hheight :
      heightOf right' = heightOf (rotateLeft left sep right).2.2)
    (hsubset :
      KeysSubset right' (rotateLeft left sep right).2.2) :
    let repaired := rotateLeft left sep right
    NodeWF t b
        (node (ks.set j repaired.2.1)
          ((cs.set j repaired.1).set (j + 1) right')) ∧
      heightOf
          (node (ks.set j repaired.2.1)
            ((cs.set j repaired.1).set (j + 1) right')) =
        heightOf (node ks cs) ∧
      KeysSubset
        (node (ks.set j repaired.2.1)
          ((cs.set j repaired.1).set (j + 1) right'))
        (node ks cs) := by
  dsimp only
  obtain ⟨hjKey, hsepGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hsep
  obtain ⟨hjLeft, hleftGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hleft
  obtain ⟨hjRight, hrightGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hright
  have hleftGet : cs.get ⟨j, hjLeft⟩ = left := by
    rw [List.get_eq_getElem]
    exact hleftGetElem
  have hrightGet : cs.get ⟨j + 1, hjRight⟩ = right := by
    rw [List.get_eq_getElem]
    exact hrightGetElem
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j, hleft⟩
  have hrightMem : right ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨j + 1, hright⟩
  have hleftWF : NodeWF t false left :=
    hparent.child hleftMem
  have hrightWF : NodeWF t false right :=
    hparent.child hrightMem
  have hsiblings : heightOf left = heightOf right :=
    hparent.siblings_height hleftMem hrightMem

  have hparentSorted := hparent.sorted
  unfold Sorted at hparentSorted
  have hparentBounded := hparent.childBounded
  unfold ChildBounded at hparentBounded
  obtain ⟨_, hbounds, _⟩ := hparentBounded
  have hleftBounds := hbounds j hjLeft
  rw [hleftGet] at hleftBounds
  have hrightBounds := hbounds (j + 1) hjRight
  rw [hrightGet] at hrightBounds
  have hleftLe : ∀ k ∈ keysOf left, k ≤ sep := by
    have hupper := hleftBounds.2
    rw [hsep] at hupper
    exact hupper
  have hrightGe : ∀ k ∈ keysOf right, sep ≤ k := by
    rcases hrightBounds.1 with hzero | hlower
    · omega
    · rw [show j + 1 - 1 = j by omega, hsep] at hlower
      exact hlower

  have hrepair :=
    rotateLeft_nodeWF ht hleftWF hrightWF hleftKeys hrightKeys
      hsiblings hleftLe hrightGe
  dsimp only at hrepair
  have hcross :=
    rotateLeft_separator_bounds hleftWF hleftLe hrightGe
  dsimp only at hcross
  have hnewSepMem :
      (rotateLeft left sep right).2.1 ∈ keysOf left :=
    rotateLeft_newSeparator_mem_left ht left sep right hleftKeys
  have hnewLeSep : (rotateLeft left sep right).2.1 ≤ sep :=
    hleftLe _ hnewSepMem

  have htrimLeft :=
    replaceChild_packet hparent hleft hrepair.1 hrepair.2.2.1
      (rotateLeft_left_keysSubset left sep right)

  have hprefix :
      ∀ k ∈ ks.take j, k ≤ (rotateLeft left sep right).2.1 := by
    by_cases hjZero : j = 0
    · subst j
      simp
    · have hprevIndex : j - 1 < ks.length := by omega
      have hleftLower := hleftBounds.1
      rcases hleftLower with hzero | hleftLower
      · exact absurd hzero hjZero
      · rw [List.getElem?_eq_getElem hprevIndex] at hleftLower
        have hprevLeNew :
            ks[j - 1] ≤ (rotateLeft left sep right).2.1 :=
          hleftLower _ hnewSepMem
        intro k hk
        exact
          (ReassemblyInternal.pairwise_take_le_get
            hparentSorted.1 hprevIndex
            (by omega) k hk).trans hprevLeNew
  have hsuffix :
      ∀ k ∈ ks.drop (j + 1),
        (rotateLeft left sep right).2.1 ≤ k := by
    intro k hk
    have hsepLe : ks[j] ≤ k :=
      ReassemblyInternal.pairwise_get_le_drop
        hparentSorted.1 hjKey
        (by omega) k hk
    rw [hsepGetElem] at hsepLe
    exact hnewLeSep.trans hsepLe
  have hleftChild :
      ∀ child,
        (cs.set j (rotateLeft left sep right).1)[j]? =
            some child →
          ∀ k ∈ keysOf child,
            k ≤ (rotateLeft left sep right).2.1 := by
    intro child hchild
    have hset :
        (cs.set j (rotateLeft left sep right).1)[j]? =
          some (rotateLeft left sep right).1 :=
      List.getElem?_set_eq_of_lt _ hjLeft
    have hchildEq : child = (rotateLeft left sep right).1 :=
      Option.some.inj (hchild.symm.trans hset)
    subst child
    exact hcross.1
  have hrightAfterTrim :
      (cs.set j (rotateLeft left sep right).1)[j + 1]? =
        some right := by
    rw [List.getElem?_set_ne (by omega : j ≠ j + 1)]
    exact hright
  have hrightChild :
      ∀ child,
        (cs.set j (rotateLeft left sep right).1)[j + 1]? =
            some child →
          ∀ k ∈ keysOf child,
            (rotateLeft left sep right).2.1 ≤ k := by
    intro child hchild
    have hchildEq : child = right :=
      Option.some.inj (hchild.symm.trans hrightAfterTrim)
    subst child
    intro k hk
    exact hnewLeSep.trans (hrightGe k hk)
  have hseparator :=
    replaceSeparator_nodeWF htrimLeft.1 hjKey hprefix hsuffix
      hleftChild hrightChild

  have hnewRightLower :
      j + 1 = 0 ∨
        (match
            (ks.set j (rotateLeft left sep right).2.1)[j + 1 - 1]?
        with
        | some lower =>
            ∀ k ∈ keysOf (rotateLeft left sep right).2.2, lower ≤ k
        | none => True) := by
    right
    rw [show j + 1 - 1 = j by omega,
      List.getElem?_set_eq_of_lt _ hjKey]
    exact hcross.2
  have hnewRightUpper :
      match (ks.set j (rotateLeft left sep right).2.1)[j + 1]? with
      | some upper =>
          ∀ k ∈ keysOf (rotateLeft left sep right).2.2, k ≤ upper
      | none => True := by
    rw [List.getElem?_set_ne (by omega : j ≠ j + 1)]
    cases hnext : ks[j + 1]? with
    | none => trivial
    | some upper =>
        obtain ⟨hnextIndex, hnextGetElem⟩ :=
          List.getElem?_eq_some_iff.mp hnext
        have hsepUpper : sep ≤ upper := by
          have hp :=
            pairwise_get_mono hparentSorted.1
              (by omega) hjKey hnextIndex
          simpa [hsepGetElem, hnextGetElem] using hp
        have hrightUpper := hrightBounds.2
        rw [hnext] at hrightUpper
        intro k hk
        have hsource :=
          (mem_keysOf_rotateLeft left sep right k).mp
            (Or.inr (Or.inr hk))
        rcases hsource with hkLeft | rfl | hkRight
        · exact (hleftLe k hkLeft).trans hsepUpper
        · exact hsepUpper
        · exact hrightUpper k hkRight

  have hrotated :=
    ReassemblyInternal.replaceChild_nodeWF_height_of_bounds
      hseparator.1 hrightAfterTrim hrepair.2.1 hrepair.2.2.2
      hnewRightLower hnewRightUpper
  have hrotatedHeight :
      heightOf
          (node (ks.set j (rotateLeft left sep right).2.1)
            ((cs.set j (rotateLeft left sep right).1).set (j + 1)
              (rotateLeft left sep right).2.2)) =
        heightOf (node ks cs) :=
    hrotated.2.trans
      (hseparator.2.trans htrimLeft.2.1)
  have hrotatedSubset :
      KeysSubset
        (node (ks.set j (rotateLeft left sep right).2.1)
          ((cs.set j (rotateLeft left sep right).1).set (j + 1)
            (rotateLeft left sep right).2.2))
        (node ks cs) :=
    replaceAdjacent_keysSubset hsep hleft hright
      (mem_keysOf_rotateLeft left sep right)
  have hrightAtRotated :
      ((cs.set j (rotateLeft left sep right).1).set (j + 1)
          (rotateLeft left sep right).2.2)[j + 1]? =
        some (rotateLeft left sep right).2.2 :=
    List.getElem?_set_eq_of_lt _ (by
      simpa using hjRight)

  have hfinal :=
    replaceChild_packet hrotated.1 hrightAtRotated hright'
      hheight hsubset
  simpa only [List.set_set] using
    And.intro hfinal.1
      (And.intro
        (hfinal.2.1.trans hrotatedHeight)
        (hfinal.2.2.trans hrotatedSubset))

end BTree
end Chapter18
end CLRS
