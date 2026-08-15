import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion.Reassembly

/-!
# Parent reassembly after merging adjacent B-tree children

The deletion algorithm has three syntactically different merge sites, but all
three remove separator {lit}`j`, replace children {lit}`j` and {lit}`j + 1` by one recursive
result, and retain the surrounding parent context.  This module packages that
single atomic reassembly step.
-/

namespace CLRS
namespace Chapter18
namespace BTree

private lemma spliceKeys_get_before {α : Type*}
    {xs : List α} {j q : Nat}
    (hj : j < xs.length) (hq : q < j) :
    (xs.take j ++ xs.drop (j + 1))[q]? = xs[q]? := by
  have htake : (xs.take j).length = j := by
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [List.getElem?_append_left (by omega)]
  simp [hq]

private lemma spliceKeys_get_after {α : Type*}
    {xs : List α} {j q : Nat}
    (hj : j < xs.length) (hq : j ≤ q) :
    (xs.take j ++ xs.drop (j + 1))[q]? = xs[q + 1]? := by
  have htake : (xs.take j).length = j := by
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [List.getElem?_append_right (by omega), List.getElem?_drop]
  rw [htake]
  congr 1
  omega

private lemma spliceChildren_get_before {α : Type*}
    {xs : List α} {new : α} {j q : Nat}
    (hj : j + 1 < xs.length) (hq : q < j) :
    (xs.take j ++ [new] ++ xs.drop (j + 2))[q]? = xs[q]? := by
  have htake : (xs.take j).length = j := by
    simp [Nat.min_eq_left (by omega : j ≤ xs.length)]
  rw [List.getElem?_append_left]
  · rw [List.getElem?_append_left (by omega)]
    simp [hq]
  · simp [htake]
    omega

private lemma spliceChildren_get_eq {α : Type*}
    {xs : List α} {new : α} {j : Nat}
    (hj : j + 1 < xs.length) :
    (xs.take j ++ [new] ++ xs.drop (j + 2))[j]? = some new := by
  have htake : (xs.take j).length = j := by
    simp [Nat.min_eq_left (by omega : j ≤ xs.length)]
  rw [List.getElem?_append_left]
  · rw [List.getElem?_append_right]
    · rw [htake]
      simp
    · omega
  · simp [htake]

private lemma spliceChildren_get_after {α : Type*}
    {xs : List α} {new : α} {j q : Nat}
    (hj : j + 1 < xs.length) (hq : j < q) :
    (xs.take j ++ [new] ++ xs.drop (j + 2))[q]? = xs[q + 1]? := by
  have htake : (xs.take j).length = j := by
    simp [Nat.min_eq_left (by omega : j ≤ xs.length)]
  rw [List.getElem?_append_right]
  · rw [List.getElem?_drop]
    simp [htake]
    congr 1
    omega
  · simp [htake]
    omega

private lemma mem_of_mem_spliceChildren {α : Type*}
    {xs : List α} {new child : α} {j : Nat}
    (hchild : child ∈ xs.take j ++ [new] ++ xs.drop (j + 2)) :
    child ∈ xs ∨ child = new := by
  rcases List.mem_append.mp hchild with hfront | hsuffix
  rcases List.mem_append.mp hfront with hprefix | hnew
  · exact Or.inl (List.mem_of_mem_take hprefix)
  · simp only [List.mem_singleton] at hnew
    exact Or.inr hnew
  · exact Or.inl (List.mem_of_mem_drop hsuffix)

/--
Atomic parent reassembly for every merge branch of {name}`composedDelete`.

Separator {lit}`j` and its adjacent children are replaced by one recursive result.
The result remains an ordinary well-formed non-root node, or (at a root) is
either an ordinary root or the single-child empty-root transient accepted by
{name}`RootDeleteResult`.
-/
theorem spliceMerged_packet
    {t j sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree}
    {left right newMerged : BTree}
    (hparent : NodeWF t b (node ks cs))
    (hready : DeleteReady t b (node ks cs))
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right)
    (hnew : NodeWF t false newMerged)
    (hheight :
      heightOf newMerged = heightOf (mergeNodes left sep right))
    (hsubset :
      KeysSubset newMerged (mergeNodes left sep right)) :
    let out :=
      node (ks.take j ++ ks.drop (j + 1))
        (cs.take j ++ [newMerged] ++ cs.drop (j + 2))
    (if b then RootDeleteResult t out else NodeWF t false out) ∧
      heightOf out = heightOf (node ks cs) ∧
      KeysSubset out (node ks cs) := by
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
  obtain ⟨hchildrenRel, hbounds, hchildrenBounded⟩ :=
    hparentBounded
  have hcsLen : cs.length = ks.length + 1 := by
    rcases hchildrenRel with hempty | hlength
    · have : cs = [] := List.isEmpty_iff.mp hempty
      subst cs
      simp at hright
    · exact hlength
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

  have hmergedHeight :
      heightOf (mergeNodes left sep right) = heightOf left :=
    mergeNodes_height hleftWF.sameDepth hrightWF.sameDepth hsiblings
  have hnewHeightLeft : heightOf newMerged = heightOf left :=
    hheight.trans hmergedHeight

  have hnewLower :
      j = 0 ∨
        (match ks[j - 1]? with
        | some lower =>
            ∀ k ∈ keysOf newMerged, lower ≤ k
        | none => True) := by
    by_cases hjZero : j = 0
    · exact Or.inl hjZero
    · right
      rcases hleftBounds.1 with hzero | hleftLower
      · exact absurd hzero hjZero
      · cases hprev : ks[j - 1]? with
        | none => trivial
        | some lower =>
            rw [hprev] at hleftLower
            have hjPred : j - 1 < ks.length := by omega
            obtain ⟨_, hprevGetElem⟩ :=
              List.getElem?_eq_some_iff.mp hprev
            have hp :=
              pairwise_get_mono hparentSorted.1
                (by omega) hjPred hjKey
            have hlowerSep : lower ≤ sep := by
              simpa [hprevGetElem, hsepGetElem] using hp
            intro k hk
            have hkMerged := hsubset k hk
            rw [mem_keysOf_mergeNodes] at hkMerged
            rcases hkMerged with hkLeft | rfl | hkRight
            · exact hleftLower k hkLeft
            · exact hlowerSep
            · exact hlowerSep.trans (hrightGe k hkRight)

  have hnewUpper :
      (match ks[j + 1]? with
      | some upper =>
          ∀ k ∈ keysOf newMerged, k ≤ upper
      | none => True) := by
    cases hnext : ks[j + 1]? with
    | none => trivial
    | some upper =>
        obtain ⟨hjNext, hnextGetElem⟩ :=
          List.getElem?_eq_some_iff.mp hnext
        have hp :=
          pairwise_get_mono hparentSorted.1
            (by omega) hjKey hjNext
        have hsepUpper : sep ≤ upper := by
          simpa [hsepGetElem, hnextGetElem] using hp
        have hrightUpper := hrightBounds.2
        rw [hnext] at hrightUpper
        intro k hk
        have hkMerged := hsubset k hk
        rw [mem_keysOf_mergeNodes] at hkMerged
        rcases hkMerged with hkLeft | rfl | hkRight
        · exact (hleftLe k hkLeft).trans hsepUpper
        · exact hsepUpper
        · exact hrightUpper k hkRight

  have hsorted :
      Sorted
        (node (ks.take j ++ ks.drop (j + 1))
          (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) := by
    unfold Sorted
    constructor
    · rw [← List.eraseIdx_eq_take_drop_succ ks j]
      exact hparentSorted.1.sublist (List.eraseIdx_sublist ks j)
    · intro child hchild
      rcases mem_of_mem_spliceChildren hchild with hchildOld | rfl
      · exact hparentSorted.2 child hchildOld
      · exact hnew.sorted

  have hbounded :
      ChildBounded
        (node (ks.take j ++ ks.drop (j + 1))
          (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) := by
    unfold ChildBounded
    refine ⟨?_, ?_, ?_⟩
    · right
      simp only [List.length_append, List.length_take, List.length_drop,
        List.length_cons, List.length_nil]
      have hjLeKs : j ≤ ks.length := Nat.le_of_lt hjKey
      have hjLeCs : j ≤ cs.length := by omega
      omega
    · intro q hq
      let child :=
        (cs.take j ++ [newMerged] ++ cs.drop (j + 2)).get ⟨q, hq⟩
      have hchildGet :
          (cs.take j ++ [newMerged] ++ cs.drop (j + 2))[q]? =
            some child :=
        List.getElem?_eq_getElem hq
      change
        (q = 0 ∨
          (match
              (ks.take j ++ ks.drop (j + 1))[q - 1]? with
          | some lower => ∀ k ∈ keysOf child, lower ≤ k
          | none => True)) ∧
        (match (ks.take j ++ ks.drop (j + 1))[q]? with
        | some upper => ∀ k ∈ keysOf child, k ≤ upper
        | none => True)
      by_cases hqBefore : q < j
      · have hchildOldGet : cs[q]? = some child := by
          rw [← spliceChildren_get_before hjRight hqBefore]
          exact hchildGet
        obtain ⟨hqOld, hchildOldGetElem⟩ :=
          List.getElem?_eq_some_iff.mp hchildOldGet
        have hold := hbounds q hqOld
        have hchildEq : cs.get ⟨q, hqOld⟩ = child := by
          rw [List.get_eq_getElem]
          exact hchildOldGetElem
        rw [hchildEq] at hold
        constructor
        · rcases hold.1 with hzero | hlower
          · exact Or.inl hzero
          · right
            rw [spliceKeys_get_before hjKey (by omega)]
            exact hlower
        · rw [spliceKeys_get_before hjKey hqBefore]
          exact hold.2
      · by_cases hqEq : q = j
        · subst q
          have hchildEq : child = newMerged := by
            rw [spliceChildren_get_eq hjRight] at hchildGet
            exact Option.some.inj hchildGet.symm
          rw [hchildEq]
          constructor
          · by_cases hjZero : j = 0
            · exact Or.inl hjZero
            · right
              rw [spliceKeys_get_before hjKey (by omega)]
              exact hnewLower.resolve_left hjZero
          · rw [spliceKeys_get_after hjKey (Nat.le_refl j)]
            exact hnewUpper
        · have hqAfter : j < q := by omega
          have hchildOldGet : cs[q + 1]? = some child := by
            rw [← spliceChildren_get_after hjRight hqAfter]
            exact hchildGet
          obtain ⟨hqOld, hchildOldGetElem⟩ :=
            List.getElem?_eq_some_iff.mp hchildOldGet
          have hold := hbounds (q + 1) hqOld
          have hchildEq : cs.get ⟨q + 1, hqOld⟩ = child := by
            rw [List.get_eq_getElem]
            exact hchildOldGetElem
          rw [hchildEq] at hold
          constructor
          · right
            rcases hold.1 with hzero | hlower
            · omega
            · rw [show q + 1 - 1 = q by omega] at hlower
              rw [spliceKeys_get_after hjKey (by omega)]
              have hqSuccPred : q - 1 + 1 = q := by omega
              rw [hqSuccPred]
              exact hlower
          · rw [spliceKeys_get_after hjKey (Nat.le_of_lt hqAfter)]
            exact hold.2
    · intro child hchild
      rcases mem_of_mem_spliceChildren hchild with hchildOld | rfl
      · exact hchildrenBounded child hchildOld
      · exact hnew.childBounded

  have hdepth :
      SameDepth
        (node (ks.take j ++ ks.drop (j + 1))
          (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) := by
    apply sameDepth_iff.mpr
    constructor
    · intro child hchild
      rcases mem_of_mem_spliceChildren hchild with hchildOld | rfl
      · exact sameDepth_children_sd hparent.sameDepth child hchildOld
      · exact hnew.sameDepth
    · intro child hchild other hother
      have hchildHeight : heightOf child = heightOf left := by
        rcases mem_of_mem_spliceChildren hchild with hchildOld | rfl
        · exact hparent.siblings_height hchildOld hleftMem
        · exact hnewHeightLeft
      have hotherHeight : heightOf other = heightOf left := by
        rcases mem_of_mem_spliceChildren hother with hotherOld | rfl
        · exact hparent.siblings_height hotherOld hleftMem
        · exact hnewHeightLeft
      exact hchildHeight.trans hotherHeight.symm

  have hnewMem :
      newMerged ∈ cs.take j ++ [newMerged] ++ cs.drop (j + 2) := by
    simp
  have hparentHeight :
      heightOf
          (node (ks.take j ++ ks.drop (j + 1))
            (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) =
        heightOf (node ks cs) := by
    calc
      heightOf
          (node (ks.take j ++ ks.drop (j + 1))
            (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) =
          1 + heightOf newMerged :=
        heightOf_sameDepth_mem hdepth hnewMem
      _ = 1 + heightOf left := by rw [hnewHeightLeft]
      _ = heightOf (node ks cs) :=
        (heightOf_sameDepth_mem hparent.sameDepth hleftMem).symm

  have hkeys :
      KeysSubset
        (node (ks.take j ++ ks.drop (j + 1))
          (cs.take j ++ [newMerged] ++ cs.drop (j + 2)))
        (node ks cs) := by
    intro k hk
    simp only [keysOf, List.mem_append, List.mem_flatMap] at hk ⊢
    rcases hk with hkey | ⟨child, hchild, hk⟩
    · rcases hkey with hprefix | hsuffix
      · exact Or.inl (List.mem_of_mem_take hprefix)
      · exact Or.inl (List.mem_of_mem_drop hsuffix)
    · rcases hchild with (hprefix | hnewChild) | hsuffix
      · exact Or.inr
          ⟨child, List.mem_of_mem_take hprefix, hk⟩
      · have hchildEq : child = newMerged := by simpa using hnewChild
        subst child
        have hkMerged := hsubset k hk
        rw [mem_keysOf_mergeNodes] at hkMerged
        rcases hkMerged with hkLeft | rfl | hkRight
        · exact Or.inr ⟨left, hleftMem, hkLeft⟩
        · exact Or.inl
            (List.mem_iff_getElem?.mpr ⟨j, hsep⟩)
        · exact Or.inr ⟨right, hrightMem, hkRight⟩
      · exact Or.inr
          ⟨child, List.mem_of_mem_drop hsuffix, hk⟩

  have hchildrenOcc :
      ∀ child ∈ cs.take j ++ [newMerged] ++ cs.drop (j + 2),
        Occupancy t false child := by
    intro child hchild
    rcases mem_of_mem_spliceChildren hchild with hchildOld | rfl
    · have hparentOcc := hparent.occupancy
      unfold Occupancy at hparentOcc
      exact hparentOcc.2.2.2 child hchildOld
    · exact hnew.occupancy

  cases b with
  | false =>
      have hreadyKeys : t ≤ ks.length := by
        simpa [DeleteReady, numKeys] using hready
      have hparentOcc := occupancy_false_dest hparent.occupancy
      have hoccupancy :
          Occupancy t false
            (node (ks.take j ++ ks.drop (j + 1))
              (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) := by
        apply occupancy_false_intro
        · simp only [List.length_append, List.length_take, List.length_drop]
          omega
        · simp only [List.length_append, List.length_take, List.length_drop]
          omega
        · right
          constructor
          · simp only [List.length_append, List.length_take,
              List.length_drop, List.length_cons, List.length_nil]
            omega
          · simp only [List.length_append, List.length_take,
              List.length_drop, List.length_cons, List.length_nil]
            rcases hparentOcc.2.2.1 with hempty | hinternal
            · subst cs
              simp at hright
            · omega
        · exact hchildrenOcc
      exact
        ⟨⟨hsorted, hbounded, hoccupancy, hdepth⟩,
          hparentHeight,
          hkeys⟩
  | true =>
      have hparentOcc := hparent.occupancy
      unfold Occupancy at hparentOcc
      by_cases hsingle : ks.length = 1
      · have hjZero : j = 0 := by omega
        have hdropKeys : ks.drop 1 = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [hsingle]
        have hdropChildren : cs.drop 2 = [] := by
          apply List.eq_nil_of_length_eq_zero
          simp [hcsLen, hsingle]
        refine
          ⟨⟨hsorted, hbounded, hdepth, ?_⟩,
            hparentHeight,
            hkeys⟩
        refine Or.inr ⟨newMerged, ?_, hnew.occupancy⟩
        simp [hjZero, hdropKeys, hdropChildren]
      · have hkeysAtLeastTwo : 2 ≤ ks.length := by omega
        have hoccupancy :
            Occupancy t true
              (node (ks.take j ++ ks.drop (j + 1))
                (cs.take j ++ [newMerged] ++ cs.drop (j + 2))) := by
          unfold Occupancy
          simp only [↓reduceIte]
          have hnewKeysPos :
              1 ≤ (ks.take j ++ ks.drop (j + 1)).length := by
            simp only [List.length_append, List.length_take,
              List.length_drop]
            omega
          have hnewKeysNotEmpty :
              ¬ ((ks.take j ++ ks.drop (j + 1)).length = 0 ∧
                (cs.take j ++ [newMerged] ++ cs.drop (j + 2)).isEmpty) := by
            omega
          rw [if_neg hnewKeysNotEmpty]
          refine ⟨hnewKeysPos, ?_, ?_, hchildrenOcc⟩
          · simp only [List.length_append, List.length_take,
              List.length_drop]
            omega
          · right
            constructor
            · simp only [List.length_append, List.length_take,
                List.length_drop, List.length_cons, List.length_nil]
              omega
            · simp only [List.length_append, List.length_take,
                List.length_drop, List.length_cons, List.length_nil]
              rcases hparentOcc.2.2.1 with hempty | hinternal
              · have : cs = [] := List.isEmpty_iff.mp hempty
                subst cs
                simp at hright
              · omega
        exact
          ⟨⟨hsorted, hbounded, hdepth, Or.inl hoccupancy⟩,
            hparentHeight,
            hkeys⟩

/--
The positive-index merge-left branches use child index {lit}`i` and therefore
spell the separator index as {lit}`i - 1`.  This is the exact output shape in
{name}`composedDelete`.
-/
theorem spliceMerged_left_packet
    {t i sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree}
    {left right newMerged : BTree}
    (hi : 0 < i)
    (hparent : NodeWF t b (node ks cs))
    (hready : DeleteReady t b (node ks cs))
    (hsep : ks[i - 1]? = some sep)
    (hleft : cs[i - 1]? = some left)
    (hright : cs[i]? = some right)
    (hnew : NodeWF t false newMerged)
    (hheight :
      heightOf newMerged = heightOf (mergeNodes left sep right))
    (hsubset :
      KeysSubset newMerged (mergeNodes left sep right)) :
    let out :=
      node (ks.take (i - 1) ++ ks.drop i)
        (cs.take (i - 1) ++ [newMerged] ++ cs.drop (i + 1))
    (if b then RootDeleteResult t out else NodeWF t false out) ∧
      heightOf out = heightOf (node ks cs) ∧
      KeysSubset out (node ks cs) := by
  have hpacket :=
    spliceMerged_packet hparent hready hsep hleft
      (j := i - 1) (by simpa [show i - 1 + 1 = i by omega] using hright)
      hnew hheight hsubset
  simpa [show i - 1 + 1 = i by omega,
    show i - 1 + 2 = i + 1 by omega] using hpacket

/--
The no-left-sibling merge-right branch is the {lit}`j = 0` specialization of the
atomic packet, in exactly the syntax returned by {name}`composedDelete`.
-/
theorem spliceMerged_zero_packet
    {t sep : Nat} {b : Bool}
    {ks : List Nat} {cs : List BTree}
    {left right newMerged : BTree}
    (hparent : NodeWF t b (node ks cs))
    (hready : DeleteReady t b (node ks cs))
    (hsep : ks[0]? = some sep)
    (hleft : cs[0]? = some left)
    (hright : cs[1]? = some right)
    (hnew : NodeWF t false newMerged)
    (hheight :
      heightOf newMerged = heightOf (mergeNodes left sep right))
    (hsubset :
      KeysSubset newMerged (mergeNodes left sep right)) :
    let out :=
      node (ks.drop 1) ([newMerged] ++ cs.drop 2)
    (if b then RootDeleteResult t out else NodeWF t false out) ∧
      heightOf out = heightOf (node ks cs) ∧
      KeysSubset out (node ks cs) := by
  simpa using
    (spliceMerged_packet hparent hready hsep hleft hright
      hnew hheight hsubset)

end BTree
end Chapter18
end CLRS
