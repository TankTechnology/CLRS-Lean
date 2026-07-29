import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion.Repair

/-!
# Parent reassembly packets for B-tree deletion

This module packages the invariant bookkeeping needed after a recursive
deletion result is put back into its parent.
-/

namespace CLRS
namespace Chapter18
namespace BTree

namespace ReassemblyInternal

/--
Every key in a sufficiently short prefix of a pairwise ordered key list lies
below the key at a later in-range index.
-/
theorem pairwise_take_le_get
    {ks : List Nat} (hp : List.Pairwise (· ≤ ·) ks)
    {m j : Nat} (hj : j < ks.length) (hm : m ≤ j + 1) :
    ∀ k ∈ ks.take m, k ≤ ks[j] := by
  intro k hk
  rcases List.mem_iff_get.mp hk with ⟨q, hq⟩
  have hqm : q.val < m :=
    Nat.lt_of_lt_of_le q.isLt (List.length_take_le m ks)
  have hqks : q.val < ks.length := by omega
  have hkEq : k = ks.get ⟨q.val, hqks⟩ := by
    calc
      k = (ks.take m).get q := by rw [hq]
      _ = ks.get ⟨q.val, hqks⟩ := by simp
  rw [hkEq]
  exact pairwise_get_mono hp (by omega) hqks hj

/--
Every key in a suffix of a pairwise ordered key list lies above any earlier
in-range key.
-/
theorem pairwise_get_le_drop
    {ks : List Nat} (hp : List.Pairwise (· ≤ ·) ks)
    {j m : Nat} (hj : j < ks.length) (hjm : j ≤ m) :
    ∀ k ∈ ks.drop m, ks[j] ≤ k := by
  intro k hk
  rcases List.mem_iff_get.mp hk with ⟨q, hq⟩
  have hidx : m + q.val < ks.length := by
    have hq' : q.val < ks.length - m := by
      simpa only [List.length_drop] using q.isLt
    omega
  have hkEq : k = ks.get ⟨m + q.val, hidx⟩ := by
    calc
      k = (ks.drop m).get q := by rw [hq]
      _ = ks.get ⟨m + q.val, hidx⟩ := by simp
  rw [hkEq]
  exact pairwise_get_mono hp (by omega) hj hidx

/--
Replacing one child by an equally high well-formed child preserves the parent
structure and height when the replacement's two parent-side key bounds are
provided explicitly.
-/
theorem replaceChild_nodeWF_height_of_bounds
    {t i : Nat} {b : Bool} {ks : List Nat} {cs : List BTree}
    {old new : BTree}
    (hparent : NodeWF t b (node ks cs))
    (hold : cs[i]? = some old)
    (hnew : NodeWF t false new)
    (hheight : heightOf new = heightOf old)
    (hnewLower :
      i = 0 ∨
        (match ks[i - 1]? with
        | some lower => ∀ k ∈ keysOf new, lower ≤ k
        | none => True))
    (hnewUpper :
      match ks[i]? with
      | some upper => ∀ k ∈ keysOf new, k ≤ upper
      | none => True) :
    NodeWF t b (node ks (cs.set i new)) ∧
      heightOf (node ks (cs.set i new)) = heightOf (node ks cs) := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hold
  have holdMem : old ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hold⟩
  have hnewMem : new ∈ cs.set i new :=
    List.mem_set hi new

  have hsorted : Sorted (node ks (cs.set i new)) := by
    have hparentSorted := hparent.sorted
    unfold Sorted at hparentSorted ⊢
    refine ⟨hparentSorted.1, ?_⟩
    intro child hchild
    rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
    · exact hparentSorted.2 child hchildOld
    · exact hnew.sorted

  have hbounded : ChildBounded (node ks (cs.set i new)) :=
    childBounded_set hparent.childBounded hi hnew.childBounded
      hnewLower hnewUpper

  have hoccupancy : Occupancy t b (node ks (cs.set i new)) :=
    occupancy_set hparent.occupancy hi hnew.occupancy

  have hchildDepth :
      ∀ child ∈ cs.set i new, SameDepth child := by
    intro child hchild
    rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
    · exact (sameDepth_iff.mp hparent.sameDepth).1 child hchildOld
    · exact hnew.sameDepth
  have hchildHeight :
      ∀ child ∈ cs.set i new, heightOf child = heightOf old := by
    intro child hchild
    rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
    · exact hparent.siblings_height hchildOld holdMem
    · exact hheight
  have hdepth : SameDepth (node ks (cs.set i new)) := by
    apply sameDepth_iff.mpr
    refine ⟨hchildDepth, ?_⟩
    intro left hleft right hright
    exact (hchildHeight left hleft).trans
      (hchildHeight right hright).symm

  have hparentHeight :
      heightOf (node ks (cs.set i new)) = heightOf (node ks cs) := by
    calc
      heightOf (node ks (cs.set i new)) =
          1 + heightOf new :=
        heightOf_sameDepth_mem hdepth hnewMem
      _ = 1 + heightOf old := by rw [hheight]
      _ = heightOf (node ks cs) :=
        (heightOf_sameDepth_mem hparent.sameDepth holdMem).symm

  exact
    ⟨⟨hsorted, hbounded, hoccupancy, hdepth⟩,
      hparentHeight⟩

end ReassemblyInternal

/--
Replacing one child by an equally high, well-formed key-subset preserves the
complete parent invariant packet, the parent height, and the represented-key
subset relation.
-/
theorem replaceChild_packet
    {t i : Nat} {b : Bool} {ks : List Nat} {cs : List BTree}
    {old new : BTree}
    (hparent : NodeWF t b (node ks cs))
    (hold : cs[i]? = some old)
    (hnew : NodeWF t false new)
    (hheight : heightOf new = heightOf old)
    (hsubset : KeysSubset new old) :
    NodeWF t b (node ks (cs.set i new)) ∧
      heightOf (node ks (cs.set i new)) = heightOf (node ks cs) ∧
      KeysSubset (node ks (cs.set i new)) (node ks cs) := by
  obtain ⟨hi, hget⟩ := List.getElem?_eq_some_iff.mp hold
  have hget' : cs.get ⟨i, hi⟩ = old := by
    rw [List.get_eq_getElem]
    exact hget
  have holdMem : old ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hold⟩

  have hparentBounded := hparent.childBounded
  unfold ChildBounded at hparentBounded
  obtain ⟨_, hbounds, _⟩ := hparentBounded
  have hboundsOld := hbounds i hi
  rw [hget'] at hboundsOld
  have hnewLower :
      i = 0 ∨
        (match ks[i - 1]? with
        | some lower => ∀ k ∈ keysOf new, lower ≤ k
        | none => True) := by
    rcases hboundsOld.1 with hiZero | hlower
    · exact Or.inl hiZero
    · right
      cases hkey : ks[i - 1]? with
      | none => trivial
      | some lower =>
          intro k hk
          rw [hkey] at hlower
          exact hlower k (hsubset k hk)
  have hnewUpper :
      match ks[i]? with
      | some upper => ∀ k ∈ keysOf new, k ≤ upper
      | none => True := by
    cases hkey : ks[i]? with
    | none => trivial
    | some upper =>
        intro k hk
        rw [hkey] at hboundsOld
        exact hboundsOld.2 k (hsubset k hk)
  have hstruct :=
    ReassemblyInternal.replaceChild_nodeWF_height_of_bounds
      hparent hold hnew hheight hnewLower hnewUpper

  have hkeys :
      KeysSubset (node ks (cs.set i new)) (node ks cs) := by
    intro k hk
    simp only [keysOf, List.mem_append, List.mem_flatMap] at hk ⊢
    rcases hk with hparentKey | ⟨child, hchild, hk⟩
    · exact Or.inl hparentKey
    · rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
      · exact Or.inr ⟨child, hchildOld, hk⟩
      · exact Or.inr ⟨old, holdMem, hsubset k hk⟩

  exact
    ⟨hstruct.1,
      hstruct.2,
      hkeys⟩

/--
Replacing one separator preserves the structural invariant packet when the
new separator lies above the entire key prefix and left child, and below the
entire key suffix and right child.  This theorem deliberately separates
structural preservation from key provenance.
-/
theorem replaceSeparator_nodeWF
    {t i newSep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree}
    (hparent : NodeWF t b (node ks cs))
    (hi : i < ks.length)
    (hleftKeys : ∀ k ∈ ks.take i, k ≤ newSep)
    (hrightKeys : ∀ k ∈ ks.drop (i + 1), newSep ≤ k)
    (hleftChild :
      ∀ child, cs[i]? = some child →
        ∀ k ∈ keysOf child, k ≤ newSep)
    (hrightChild :
      ∀ child, cs[i + 1]? = some child →
        ∀ k ∈ keysOf child, newSep ≤ k) :
    NodeWF t b (node (ks.set i newSep) cs) ∧
      heightOf (node (ks.set i newSep) cs) =
        heightOf (node ks cs) := by
  have hsorted : Sorted (node (ks.set i newSep) cs) := by
    have hparentSorted := hparent.sorted
    unfold Sorted at hparentSorted ⊢
    refine ⟨?_, hparentSorted.2⟩
    rw [List.set_eq_take_cons_drop newSep hi]
    apply List.pairwise_append.mpr
    refine ⟨hparentSorted.1.take, ?_, ?_⟩
    · exact List.pairwise_cons.mpr
        ⟨hrightKeys, hparentSorted.1.drop⟩
    · intro left hleft right hright
      rcases List.mem_cons.mp hright with rfl | hright
      · exact hleftKeys left hleft
      · exact (hleftKeys left hleft).trans
          (hrightKeys right hright)

  have hbounded : ChildBounded (node (ks.set i newSep) cs) := by
    have hparentBounded := hparent.childBounded
    unfold ChildBounded at hparentBounded ⊢
    obtain ⟨hshape, hbounds, hchildren⟩ := hparentBounded
    refine ⟨?_, ?_, hchildren⟩
    · simpa using hshape
    intro q hq
    have hboundsOld := hbounds q hq
    let child := cs.get ⟨q, hq⟩
    show
      (q = 0 ∨
        (match (ks.set i newSep)[q - 1]? with
        | some lower => ∀ k ∈ keysOf child, lower ≤ k
        | none => True)) ∧
      (match (ks.set i newSep)[q]? with
      | some upper => ∀ k ∈ keysOf child, k ≤ upper
      | none => True)
    constructor
    · by_cases hqZero : q = 0
      · exact Or.inl hqZero
      · right
        by_cases hchanged : q - 1 = i
        · have hqSucc : q = i + 1 := by omega
          subst q
          rw [hchanged, List.getElem?_set_eq_of_lt newSep hi]
          exact hrightChild child
            (List.getElem?_eq_getElem hq)
        · rw [List.getElem?_set_ne (Ne.symm hchanged)]
          rcases hboundsOld.1 with hqZero' | hlower
          · exact absurd hqZero' hqZero
          · exact hlower
    · by_cases hchanged : q = i
      · subst q
        rw [List.getElem?_set_eq_of_lt newSep hi]
        exact hleftChild child
          (List.getElem?_eq_getElem hq)
      · rw [List.getElem?_set_ne (Ne.symm hchanged)]
        exact hboundsOld.2

  have hoccupancy : Occupancy t b (node (ks.set i newSep) cs) := by
    have hparentOccupancy := hparent.occupancy
    unfold Occupancy at hparentOccupancy ⊢
    simpa using hparentOccupancy

  have hdepth : SameDepth (node (ks.set i newSep) cs) :=
    sameDepth_keys_irrel hparent.sameDepth

  exact
    ⟨⟨hsorted, hbounded, hoccupancy, hdepth⟩,
      heightOf_keys_irrel _ _ _⟩

/--
Key provenance for separator replacement: if the new separator already
occurred somewhere in the old parent tree, replacement cannot introduce a
fresh represented key.
-/
theorem replaceSeparator_keysSubset
    {i newSep : Nat} {ks : List Nat} {cs : List BTree}
    (hnewSep : newSep ∈ keysOf (node ks cs)) :
    KeysSubset (node (ks.set i newSep) cs) (node ks cs) := by
  have hnewSep' : newSep ∈ ks ∨ ∃ child ∈ cs, newSep ∈ keysOf child := by
    simpa only [keysOf, List.mem_append, List.mem_flatMap] using hnewSep
  intro k hk
  simp only [keysOf, List.mem_append, List.mem_flatMap] at hk ⊢
  rcases hk with hkey | hchild
  · rcases List.mem_or_eq_of_mem_set hkey with hkeyOld | rfl
    · exact Or.inl hkeyOld
    · exact hnewSep'
  · exact Or.inr hchild

/-! ## Predecessor/successor parent packets -/

private theorem replaceSeparatorChild_keysSubset
    {separatorIndex childIndex newSep : Nat}
    {ks : List Nat} {cs : List BTree} {old new : BTree}
    (hold : cs[childIndex]? = some old)
    (hnewSep : newSep ∈ keysOf (node ks cs))
    (hsubset : KeysSubset new old) :
    KeysSubset
      (node (ks.set separatorIndex newSep) (cs.set childIndex new))
      (node ks cs) := by
  have holdMem : old ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨childIndex, hold⟩
  have hnewSep' :
      newSep ∈ ks ∨ ∃ child ∈ cs, newSep ∈ keysOf child := by
    simpa only [keysOf, List.mem_append, List.mem_flatMap] using hnewSep
  intro k hk
  simp only [keysOf, List.mem_append, List.mem_flatMap] at hk ⊢
  rcases hk with hkey | ⟨child, hchild, hk⟩
  · rcases List.mem_or_eq_of_mem_set hkey with hkeyOld | rfl
    · exact Or.inl hkeyOld
    · exact hnewSep'
  · rcases List.mem_or_eq_of_mem_set hchild with hchildOld | rfl
    · exact Or.inr ⟨child, hchildOld, hk⟩
    · exact Or.inr ⟨old, holdMem, hsubset k hk⟩

/--
Case 1a parent reassembly.  The predecessor from the original left child
replaces separator {lit}`i`, and an equally high recursive result replaces that
left child.  The predecessor's provenance is established in the original
child, independently of whether recursive deletion retained it.
-/
theorem replacePredecessor_packet
    {t i sep : Nat} {b : Bool} {ks : List Nat} {cs : List BTree}
    {left left' : BTree}
    (ht : 2 ≤ t)
    (hparent : NodeWF t b (node ks cs))
    (hsep : ks[i]? = some sep)
    (hleft : cs[i]? = some left)
    (hleft' : NodeWF t false left')
    (hheight : heightOf left' = heightOf left)
    (hsubset : KeysSubset left' left) :
    NodeWF t b
        (node (ks.set i (maxKey left)) (cs.set i left')) ∧
      heightOf (node (ks.set i (maxKey left)) (cs.set i left')) =
        heightOf (node ks cs) ∧
      KeysSubset
        (node (ks.set i (maxKey left)) (cs.set i left'))
        (node ks cs) := by
  obtain ⟨hiKey, hsepGet⟩ := List.getElem?_eq_some_iff.mp hsep
  obtain ⟨hiChild, hleftGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hleft
  have hleftGet : cs.get ⟨i, hiChild⟩ = left := by
    rw [List.get_eq_getElem]
    exact hleftGetElem
  have hleftMem : left ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i, hleft⟩
  have hleftWF : NodeWF t false left :=
    hparent.child hleftMem
  have hparentSorted := hparent.sorted
  unfold Sorted at hparentSorted
  have hleftPos : AllKeysPos left :=
    hleftWF.nonRoot_allKeysPos ht
  have hmaxMem : maxKey left ∈ keysOf left :=
    maxKey_mem left hleftPos
  have hmaxUpper : ∀ k ∈ keysOf left, k ≤ maxKey left :=
    maxKey_ge left hleftWF.sorted hleftWF.childBounded hleftPos

  have hparentBounded := hparent.childBounded
  unfold ChildBounded at hparentBounded
  obtain ⟨_, hbounds, _⟩ := hparentBounded
  have hleftBounds := hbounds i hiChild
  rw [hleftGet] at hleftBounds
  have hmaxLeSep : maxKey left ≤ sep := by
    have hupper := hleftBounds.2
    rw [hsep] at hupper
    exact hupper (maxKey left) hmaxMem

  have hprefix : ∀ k ∈ ks.take i, k ≤ maxKey left := by
    by_cases hiZero : i = 0
    · subst i
      simp
    · have hiPos : 0 < i := Nat.pos_of_ne_zero hiZero
      have hpredIndex : i - 1 < ks.length := by omega
      have hpredLe : ks[i - 1] ≤ maxKey left := by
        rcases hleftBounds.1 with hzero | hlower
        · exact absurd hzero hiZero
        · rw [List.getElem?_eq_getElem hpredIndex] at hlower
          exact hlower (maxKey left) hmaxMem
      intro k hk
      exact
        (ReassemblyInternal.pairwise_take_le_get
          hparentSorted.1 hpredIndex
          (by omega) k hk).trans hpredLe

  have hsuffix :
      ∀ k ∈ ks.drop (i + 1), maxKey left ≤ k := by
    intro k hk
    have hsepLe : ks[i] ≤ k :=
      ReassemblyInternal.pairwise_get_le_drop
        hparentSorted.1 hiKey
        (by omega) k hk
    rw [hsepGet] at hsepLe
    exact hmaxLeSep.trans hsepLe

  have hleftChild :
      ∀ child, cs[i]? = some child →
        ∀ k ∈ keysOf child, k ≤ maxKey left := by
    intro child hchild
    have hchildEq : child = left :=
      Option.some.inj (hchild.symm.trans hleft)
    subst child
    exact hmaxUpper

  have hrightChild :
      ∀ child, cs[i + 1]? = some child →
        ∀ k ∈ keysOf child, maxKey left ≤ k := by
    intro child hchild
    obtain ⟨hci, hchildGetElem⟩ :=
      List.getElem?_eq_some_iff.mp hchild
    have hchildGet : cs.get ⟨i + 1, hci⟩ = child := by
      rw [List.get_eq_getElem]
      exact hchildGetElem
    have hrightBounds := hbounds (i + 1) hci
    rw [hchildGet] at hrightBounds
    rcases hrightBounds.1 with hzero | hlower
    · omega
    · have hindex : i + 1 - 1 = i := by omega
      rw [hindex, hsep] at hlower
      intro k hk
      exact hmaxLeSep.trans (hlower k hk)

  have hseparator :=
    replaceSeparator_nodeWF hparent hiKey hprefix hsuffix
      hleftChild hrightChild
  have hchild :=
    replaceChild_packet hseparator.1 hleft hleft' hheight hsubset
  have hmaxParent : maxKey left ∈ keysOf (node ks cs) := by
    simp only [keysOf, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨left, hleftMem, hmaxMem⟩
  have hkeys :
      KeysSubset
        (node (ks.set i (maxKey left)) (cs.set i left'))
        (node ks cs) :=
    replaceSeparatorChild_keysSubset hleft hmaxParent hsubset
  exact
    ⟨hchild.1,
      hchild.2.1.trans hseparator.2,
      hkeys⟩

/--
Case 1b parent reassembly.  The successor from the original right child
replaces separator {lit}`i`, and an equally high recursive result replaces child
{lit}`i + 1`.  As in the predecessor packet, key provenance is tied to the
original child rather than to the recursive result.
-/
theorem replaceSuccessor_packet
    {t i sep : Nat} {b : Bool} {ks : List Nat} {cs : List BTree}
    {right right' : BTree}
    (ht : 2 ≤ t)
    (hparent : NodeWF t b (node ks cs))
    (hsep : ks[i]? = some sep)
    (hright : cs[i + 1]? = some right)
    (hright' : NodeWF t false right')
    (hheight : heightOf right' = heightOf right)
    (hsubset : KeysSubset right' right) :
    NodeWF t b
        (node (ks.set i (minKey right)) (cs.set (i + 1) right')) ∧
      heightOf
          (node (ks.set i (minKey right)) (cs.set (i + 1) right')) =
        heightOf (node ks cs) ∧
      KeysSubset
        (node (ks.set i (minKey right)) (cs.set (i + 1) right'))
        (node ks cs) := by
  obtain ⟨hiKey, hsepGet⟩ := List.getElem?_eq_some_iff.mp hsep
  obtain ⟨hiChild, hrightGetElem⟩ :=
    List.getElem?_eq_some_iff.mp hright
  have hrightGet : cs.get ⟨i + 1, hiChild⟩ = right := by
    rw [List.get_eq_getElem]
    exact hrightGetElem
  have hrightMem : right ∈ cs :=
    List.mem_iff_getElem?.mpr ⟨i + 1, hright⟩
  have hrightWF : NodeWF t false right :=
    hparent.child hrightMem
  have hparentSorted := hparent.sorted
  unfold Sorted at hparentSorted
  have hrightPos : AllKeysPos right :=
    hrightWF.nonRoot_allKeysPos ht
  have hminMem : minKey right ∈ keysOf right :=
    minKey_mem right hrightPos
  have hminLower : ∀ k ∈ keysOf right, minKey right ≤ k :=
    minKey_le right hrightWF.sorted hrightWF.childBounded hrightPos

  have hparentBounded := hparent.childBounded
  unfold ChildBounded at hparentBounded
  obtain ⟨_, hbounds, _⟩ := hparentBounded
  have hrightBounds := hbounds (i + 1) hiChild
  rw [hrightGet] at hrightBounds
  have hsepLeMin : sep ≤ minKey right := by
    rcases hrightBounds.1 with hzero | hlower
    · omega
    · have hindex : i + 1 - 1 = i := by omega
      rw [hindex, hsep] at hlower
      exact hlower (minKey right) hminMem

  have hprefix : ∀ k ∈ ks.take i, k ≤ minKey right := by
    intro k hk
    have hkSep : k ≤ ks[i] :=
      ReassemblyInternal.pairwise_take_le_get
        hparentSorted.1 hiKey
        (by omega) k hk
    rw [hsepGet] at hkSep
    exact hkSep.trans hsepLeMin

  have hsuffix :
      ∀ k ∈ ks.drop (i + 1), minKey right ≤ k := by
    intro k hk
    rcases List.mem_iff_get.mp hk with ⟨q, _⟩
    have hnextIndex : i + 1 < ks.length := by
      have hq' : q.val < ks.length - (i + 1) := by
        simpa only [List.length_drop] using q.isLt
      omega
    have hupper := hrightBounds.2
    rw [List.getElem?_eq_getElem hnextIndex] at hupper
    have hminLeNext : minKey right ≤ ks[i + 1] :=
      hupper (minKey right) hminMem
    exact hminLeNext.trans
      (ReassemblyInternal.pairwise_get_le_drop
        hparentSorted.1 hnextIndex
        (by omega) k hk)

  have hleftChild :
      ∀ child, cs[i]? = some child →
        ∀ k ∈ keysOf child, k ≤ minKey right := by
    intro child hchild
    obtain ⟨hci, hchildGetElem⟩ :=
      List.getElem?_eq_some_iff.mp hchild
    have hchildGet : cs.get ⟨i, hci⟩ = child := by
      rw [List.get_eq_getElem]
      exact hchildGetElem
    have hleftBounds := hbounds i hci
    rw [hchildGet] at hleftBounds
    have hupper := hleftBounds.2
    rw [hsep] at hupper
    intro k hk
    exact (hupper k hk).trans hsepLeMin

  have hrightChild :
      ∀ child, cs[i + 1]? = some child →
        ∀ k ∈ keysOf child, minKey right ≤ k := by
    intro child hchild
    have hchildEq : child = right :=
      Option.some.inj (hchild.symm.trans hright)
    subst child
    exact hminLower

  have hseparator :=
    replaceSeparator_nodeWF hparent hiKey hprefix hsuffix
      hleftChild hrightChild
  have hchild :=
    replaceChild_packet hseparator.1 hright hright' hheight hsubset
  have hminParent : minKey right ∈ keysOf (node ks cs) := by
    simp only [keysOf, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨right, hrightMem, hminMem⟩
  have hkeys :
      KeysSubset
        (node (ks.set i (minKey right)) (cs.set (i + 1) right'))
        (node ks cs) :=
    replaceSeparatorChild_keysSubset hright hminParent hsubset
  exact
    ⟨hchild.1,
      hchild.2.1.trans hseparator.2,
      hkeys⟩

end BTree
end Chapter18
end CLRS
