import CLRSLean.Chapter_18.Section_18_3_B_Tree_Deletion
import CLRSLean.Chapter_18.Section_18_1_B_Tree_Model.HeightBound
import CLRSLean.Chapter_03.Section_03_1_Asymptotic_Notation

/-!
# CLRS Chapter 18 - B-tree running time

This module adds the running-time / cost layer for the executable B-tree
operations.  Each cost function mirrors one real recursive construction from
Sections 18.1-18.3 and counts the number of B-tree nodes (disk pages) the
operation reads and writes:

- {lit}`searchCost` mirrors {lit}`searchExec` (Section 18.1),
- {lit}`insertCost` mirrors {lit}`insertNonFull` and {lit}`insertRootCost`
  charges the full-root split of {lit}`insertRoot` (Section 18.2),
- {lit}`deleteCost` mirrors {lit}`composedDelete` (Section 18.3).

Every descent performs {lit}`O(1)` node work (a split, a borrow, or a merge
touches a constant number of pages), so the number of disk accesses is
bounded by the number of levels visited.  The height bounds compose with the
existing {lit}`wellFormed_height_log_bound` to give the CLRS running time:

Main results:

- Theorem {lit}`searchCost_le_height`: search costs at most `height + 1`.
- Theorem {lit}`insertCost_le_height`: non-full insertion costs at most
  `height + 1`.
- Theorem {lit}`insertRootCost_le_height`: top-level insertion costs at most
  `height + 3` (the extra levels come from the full-root split).
- Theorem {lit}`deleteCost_le_height`: deletion costs at most `height + 1`.
- Theorem {lit}`searchCost_le_diskAccessBound`,
  {lit}`insertRootCost_le_diskAccessBound`,
  {lit}`deleteCost_le_diskAccessBound`: on every well-formed tree
  (`2 ≤ t`) the three operations perform at most
  {lit}`diskAccessBound t (totalKeys tr)` disk accesses, where
  {lit}`diskAccessBound t n = log_t ((n+1)/2) + 3`.
- Theorem {lit}`diskAccessBound_isBigO_log_t`: that bound is `O(log_t n)`, so
  search, insertion, and deletion each run in `O(log_t n)` disk accesses.

Notation conventions used in this section:

- `t` : B-tree minimum degree (`2 ≤ t` for every cost theorem)
- `tr` : a {lit}`BTree`
- `totalKeys tr` : the number of represented key slots (the `n` of CLRS)
-/

namespace CLRS
namespace Chapter18
namespace BTree

open List

/-! ## Disk-access cost functions -/

/--
Number of nodes visited by {lit}`searchExec` for key {lit}`x`: one per level
on the separator-selected descent path.
-/
def searchCost (x : Nat) : BTree → Nat
  | node ks cs =>
      if x ∈ ks then 1
      else
        match _hc : cs[findChild ks x]? with
        | some child => 1 + searchCost x child
        | none => 1
termination_by tr => heightOf tr
decreasing_by
  exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨findChild ks x, _hc⟩)

/--
Number of nodes read and written by {lit}`insertNonFull` for key {lit}`x`
(minimum degree {lit}`t`).  Each recursion step descends one level; the split
of a full child touches only that child and its two halves, which is constant
per level.
-/
def insertCost (t x : Nat) : BTree → Nat
  | node ks cs =>
    if cs.isEmpty then 1
    else
      let i := findChild ks x
      match _hc : cs[i]? with
      | none => 1
      | some c =>
        match _hcc : c with
        | node cKeys cChildren =>
          if cKeys.length = 2 * t - 1 then
            let median := cKeys.getD (t - 1) 0
            if x < median then
              1 + insertCost t x (node (cKeys.take (t - 1)) (cChildren.take t))
            else
              1 + insertCost t x (node (cKeys.drop t) (cChildren.drop t))
          else
            1 + insertCost t x c
termination_by tr => heightOf tr
decreasing_by
  all_goals
    have hmem : node cKeys cChildren ∈ cs := List.mem_iff_getElem?.mpr ⟨i, _hc⟩
    refine lt_of_le_of_lt ?_ (heightOf_mem_lt hmem)
    first
      | exact le_of_eq (congrArg heightOf _hcc)
      | exact heightOf_le_of_children_subset (List.take_subset _ _)
      | exact heightOf_le_of_children_subset (List.drop_subset _ _)

/--
Number of nodes read and written by {lit}`composedDelete` for key {lit}`x`
(minimum degree {lit}`t`).  Each recursion step descends one level; a borrow
or merge touches only the two adjacent children and their parent, which is
constant per level.
-/
def deleteCost (t : Nat) (x : Nat) : BTree → Nat
  | node ks cs =>
    if cs.isEmpty then 1
    else
      let i := findChild ks x
      if hiPos : 0 < i then
        let ki := i - 1
        match hk : ks[ki]? with
        | some k =>
          if hkeq : k = x then
            match hcl : cs[ki]? with
            | some leftChild =>
              match hcr : cs[ki + 1]? with
              | some rightChild =>
                if hla : t ≤ numKeys leftChild then
                  1 + deleteCost t (maxKey leftChild) leftChild
                else if hlb : t ≤ numKeys rightChild then
                  1 + deleteCost t (minKey rightChild) rightChild
                else
                  1 + deleteCost t x (mergeNodes leftChild k rightChild)
              | none => 1
            | none => 1
          else
            match hc : cs[i]? with
            | some child =>
              if hcg : t ≤ numKeys child then
                1 + deleteCost t x child
              else
                match hls : cs[i - 1]? with
                | some leftSib =>
                  if hlg : t ≤ numKeys leftSib then
                    match hsep : ks[i - 1]? with
                    | some sep =>
                      1 + deleteCost t x (rotateLeft leftSib sep child).2.2
                    | none => 1 + deleteCost t x child
                  else
                    match hrs : cs[i + 1]? with
                    | some rightSib =>
                      if hrg : t ≤ numKeys rightSib then
                        match hsep : ks[i]? with
                        | some sep =>
                          1 + deleteCost t x (rotateRight child sep rightSib).1
                        | none => 1 + deleteCost t x child
                      else
                        match hsep : ks[i - 1]? with
                        | some sep =>
                          1 + deleteCost t x (mergeNodes leftSib sep child)
                        | none => 1 + deleteCost t x child
                    | none =>
                      match hsep : ks[i - 1]? with
                      | some sep =>
                        1 + deleteCost t x (mergeNodes leftSib sep child)
                      | none => 1 + deleteCost t x child
                | none => 1 + deleteCost t x child
            | none => 1
        | none =>
          match hc : cs[i]? with
          | some child =>
            if hcg : t ≤ numKeys child then
              1 + deleteCost t x child
            else
              match hls : cs[i - 1]? with
              | some leftSib =>
                if hlg : t ≤ numKeys leftSib then
                  match hsep : ks[i - 1]? with
                  | some sep =>
                    1 + deleteCost t x (rotateLeft leftSib sep child).2.2
                  | none => 1 + deleteCost t x child
                else
                  match hrs : cs[i + 1]? with
                  | some rightSib =>
                    if hrg : t ≤ numKeys rightSib then
                      match hsep : ks[i]? with
                      | some sep =>
                        1 + deleteCost t x (rotateRight child sep rightSib).1
                      | none => 1 + deleteCost t x child
                    else
                      match hsep : ks[i - 1]? with
                      | some sep =>
                        1 + deleteCost t x (mergeNodes leftSib sep child)
                      | none => 1 + deleteCost t x child
                  | none =>
                    match hsep : ks[i - 1]? with
                    | some sep =>
                      1 + deleteCost t x (mergeNodes leftSib sep child)
                    | none => 1 + deleteCost t x child
              | none => 1 + deleteCost t x child
          | none => 1
      else
        match hc : cs[0]? with
        | some child =>
          if hcg : t ≤ numKeys child then
            1 + deleteCost t x child
          else
            match hrs : cs[1]? with
            | some rightSib =>
              if hrg : t ≤ numKeys rightSib then
                match hsep : ks[0]? with
                | some sep =>
                  1 + deleteCost t x (rotateRight child sep rightSib).1
                | none => 1 + deleteCost t x child
              else
                match hsep : ks[0]? with
                | some sep =>
                  1 + deleteCost t x (mergeNodes child sep rightSib)
                | none => 1 + deleteCost t x child
            | none => 1 + deleteCost t x child
        | none => 1
termination_by tr => heightOf tr
decreasing_by
  · exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki, hcl⟩)
  · exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki + 1, hcr⟩)
  · rw [heightOf_mergeNodes_eq_max]
    have ha : heightOf leftChild < heightOf (node ks cs) :=
      heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki, hcl⟩)
    have hb : heightOf rightChild < heightOf (node ks cs) :=
      heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨ki + 1, hcr⟩)
    omega
  all_goals
    first
      | (rw [heightOf_mergeNodes_eq_max]
         first
           | (have ha : heightOf leftSib < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hls⟩)
              have hb : heightOf child < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
              omega)
           | (have ha : heightOf child < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
              have hb : heightOf rightSib < heightOf (node ks cs) :=
                heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hrs⟩)
              omega))
      | exact heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
      | (have hle := heightOf_rotateLeft_right_le leftSib sep child
         have ha : heightOf leftSib < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hls⟩)
         have hb : heightOf child < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
         omega)
      | (have hle := heightOf_rotateRight_left_le child sep rightSib
         have ha : heightOf child < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hc⟩)
         have hb : heightOf rightSib < heightOf (node ks cs) :=
           heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨_, hrs⟩)
         omega)

/-! ## Height bounds -/

/-- **O(h) search.**  {lit}`searchExec` descends at most one path, so its
number of disk accesses is bounded by the tree height plus one. -/
theorem searchCost_le_height (x : Nat) (tr : BTree) :
    searchCost x tr ≤ heightOf tr + 1 := by
  induction tr using searchCost.induct x with
  | case1 ks cs hxkeys =>
      rw [searchCost, if_pos hxkeys]
      omega
  | case2 ks cs hxkeys child hchild ih =>
      rw [searchCost, if_neg hxkeys]
      split
      · rename_i child' hchild'
        rw [hchild] at hchild'
        cases hchild'
        have hlt : heightOf child < heightOf (node ks cs) :=
          heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨findChild ks x, hchild⟩)
        omega
      · rename_i hnone
        rw [hchild] at hnone
        contradiction
  | case3 ks cs hxkeys hchild =>
      rw [searchCost, if_neg hxkeys]
      split
      · rename_i child hchild'
        rw [hchild] at hchild'
        contradiction
      · omega

/-- **O(h) insertion.**  {lit}`insertNonFull` descends at most one path, so
its number of disk accesses is bounded by the tree height plus one. -/
theorem insertCost_le_height (t x : Nat) (tr : BTree) :
    insertCost t x tr ≤ heightOf tr + 1 := by
  induction tr using insertCost.induct (t := t) (x := x) with
  | case1 ks cs hempty =>
      rw [insertCost, if_pos hempty]
      omega
  | case2 ks cs hne i hnone =>
      have hval : insertCost t x (node ks cs) = 1 := by
        rw [insertCost, if_neg hne]
        dsimp only
        split
        · omega
        · rename_i c hc
          rw [hnone] at hc
          simp at hc
      rw [hval]
      omega
  | case3 ks cs hne i cKeys cChildren hsome hfull median hlt hsome2 ih =>
      have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
      have hval : insertCost t x (node ks cs)
          = 1 + insertCost t x (node (cKeys.take (t - 1)) (cChildren.take t)) := by
        rw [insertCost, if_neg hne]
        dsimp only
        split
        · rename_i hcnone
          rw [hsome'] at hcnone
          simp at hcnone
        · rename_i c hcsome
          obtain rfl : c = node cKeys cChildren := by
            rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
          dsimp only
          rw [if_pos hfull, if_pos hlt]
      rw [hval]
      have hmem : node cKeys cChildren ∈ cs :=
        List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩
      have hltH : heightOf (node (cKeys.take (t - 1)) (cChildren.take t)) <
          heightOf (node ks cs) :=
        lt_of_le_of_lt (heightOf_le_of_children_subset (List.take_subset _ _))
          (heightOf_mem_lt hmem)
      omega
  | case4 ks cs hne i cKeys cChildren hsome hfull median hnlt hsome2 ih =>
      have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
      have hval : insertCost t x (node ks cs)
          = 1 + insertCost t x (node (cKeys.drop t) (cChildren.drop t)) := by
        rw [insertCost, if_neg hne]
        dsimp only
        split
        · rename_i hcnone
          rw [hsome'] at hcnone
          simp at hcnone
        · rename_i c hcsome
          obtain rfl : c = node cKeys cChildren := by
            rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
          dsimp only
          rw [if_pos hfull, if_neg hnlt]
      rw [hval]
      have hmem : node cKeys cChildren ∈ cs :=
        List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩
      have hltH : heightOf (node (cKeys.drop t) (cChildren.drop t)) <
          heightOf (node ks cs) :=
        lt_of_le_of_lt (heightOf_le_of_children_subset (List.drop_subset _ _))
          (heightOf_mem_lt hmem)
      omega
  | case5 ks cs hne i cKeys cChildren hsome hnfull hsome2 ih =>
      have hsome' : cs[findChild ks x]? = some (node cKeys cChildren) := hsome
      have hval : insertCost t x (node ks cs)
          = 1 + insertCost t x (node cKeys cChildren) := by
        rw [insertCost, if_neg hne]
        dsimp only
        split
        · rename_i hcnone
          rw [hsome'] at hcnone
          simp at hcnone
        · rename_i c hcsome
          obtain rfl : c = node cKeys cChildren := by
            rw [hsome'] at hcsome; injection hcsome with h; exact h.symm
          dsimp only
          rw [if_neg hnfull]
      rw [hval]
      have hmem : node cKeys cChildren ∈ cs :=
        List.mem_iff_getElem?.mpr ⟨findChild ks x, hsome'⟩
      have hltH : heightOf (node cKeys cChildren) < heightOf (node ks cs) :=
        heightOf_mem_lt hmem
      omega

/-! ## Deletion height bound -/

private lemma child_lt_node (ks : List Nat) {cs : List BTree} {j : Nat} {c : BTree}
    (hc : cs[j]? = some c) : heightOf c < heightOf (node ks cs) :=
  heightOf_mem_lt (List.mem_iff_getElem?.mpr ⟨j, hc⟩)

private lemma merge_lt_node (ks : List Nat) {cs : List BTree} {a b : BTree} (s : Nat)
    (ha : a ∈ cs) (hb : b ∈ cs) :
    heightOf (mergeNodes a s b) < heightOf (node ks cs) := by
  rw [heightOf_mergeNodes_eq_max]
  have hha : heightOf a < heightOf (node ks cs) := heightOf_mem_lt ha
  have hhb : heightOf b < heightOf (node ks cs) := heightOf_mem_lt hb
  omega

private lemma rotateLeft_target_lt_node (ks : List Nat) {cs : List BTree} {a b : BTree} (s : Nat)
    (ha : a ∈ cs) (hb : b ∈ cs) :
    heightOf (rotateLeft a s b).2.2 < heightOf (node ks cs) := by
  have hle : heightOf (rotateLeft a s b).2.2 ≤ max (heightOf a) (heightOf b) :=
    heightOf_rotateLeft_right_le a s b
  have hha : heightOf a < heightOf (node ks cs) := heightOf_mem_lt ha
  have hhb : heightOf b < heightOf (node ks cs) := heightOf_mem_lt hb
  omega

private lemma rotateRight_target_lt_node (ks : List Nat) {cs : List BTree} {a b : BTree} (s : Nat)
    (ha : a ∈ cs) (hb : b ∈ cs) :
    heightOf (rotateRight a s b).1 < heightOf (node ks cs) := by
  have hle : heightOf (rotateRight a s b).1 ≤ max (heightOf a) (heightOf b) :=
    heightOf_rotateRight_left_le a s b
  have hha : heightOf a < heightOf (node ks cs) := heightOf_mem_lt ha
  have hhb : heightOf b < heightOf (node ks cs) := heightOf_mem_lt hb
  omega

/-- **O(h) deletion.**  {lit}`composedDelete` descends at most one path, so its
number of disk accesses is bounded by the tree height plus one. -/
theorem deleteCost_le_height (t x : Nat) (tr : BTree) :
    deleteCost t x tr ≤ heightOf tr + 1 := by
  induction x, tr using deleteCost.induct (t := t) with
  | case1 x ks cs hleaf =>
      rw [deleteCost, if_pos hleaf]
      omega
  | case2 ks cs hnonempty sep leftChild rightChild hleftReady i hpos ki hsep hleft hright ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hleft hright
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hright]
      simp [hleftReady]
      have hlt := child_lt_node ks hleft
      omega
  | case3 ks cs hnonempty sep leftChild rightChild hleftNotReady hrightReady i hpos ki hsep hleft hright ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hleft hright
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hright]
      simp [hleftNotReady, hrightReady]
      have hlt := child_lt_node ks hright
      omega
  | case4 ks cs hnonempty sep leftChild rightChild hleftNotReady hrightNotReady i hpos ki hsep hleft hright ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hleft hright
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hright]
      simp [hleftNotReady, hrightNotReady]
      have hlt := merge_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨ki, hleft⟩)
        (List.mem_iff_getElem?.mpr ⟨ki + 1, hright⟩)
      omega
  | case5 ks cs hnonempty sep leftChild i hpos ki hsep hleft hrightNone =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hleft hrightNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleft, hrightNone]
      simp
  | case6 ks cs hnonempty sep i hpos ki hsep hleftNone =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hleftNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hleftNone]
      simp
  | case7 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildReady ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hchild
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild]
      simp [hne, hchildReady]
      have hlt := child_lt_node ks hchild
      omega
  | case8 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibReady sep2 hsep2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hsep2
      simp only [ki, i] at hsep
      have hsepEq : sep = sep2 := Option.some.inj (hsep.symm.trans hsep2)
      subst sep2
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild, hleftSib]
      simp [hne, hchildNotReady, hleftSibReady]
      have hlt := rotateLeft_target_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨i - 1, hleftSib⟩)
        (List.mem_iff_getElem?.mpr ⟨i, hchild⟩)
      omega
  | case9 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibReady hsepNone ih =>
      simp only [ki, i] at hsep hsepNone
      rw [hsep] at hsepNone
      cases hsepNone
  | case10 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibReady sep2 hsep2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightSib hsep2
      simp only [ki, i] at hsep
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild, hleftSib, hrightSib, hsep2]
      simp [hne, hchildNotReady, hleftSibNotReady, hrightSibReady]
      have hlt := rotateRight_target_lt_node ks sep2 (List.mem_iff_getElem?.mpr ⟨i, hchild⟩)
        (List.mem_iff_getElem?.mpr ⟨i + 1, hrightSib⟩)
      omega
  | case11 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibReady hsepNone ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightSib hsepNone
      simp only [ki, i] at hsep
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild, hleftSib, hrightSib, hsepNone]
      simp [hne, hchildNotReady, hleftSibNotReady, hrightSibReady]
      have hlt := child_lt_node ks hchild
      omega
  | case12 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibNotReady sep2 hsep2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightSib hsep2
      simp only [ki, i] at hsep
      have hsepEq : sep = sep2 := Option.some.inj (hsep.symm.trans hsep2)
      subst sep2
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild, hleftSib, hrightSib]
      simp [hne, hchildNotReady, hleftSibNotReady, hrightSibNotReady]
      have hlt := merge_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨i - 1, hleftSib⟩)
        (List.mem_iff_getElem?.mpr ⟨i, hchild⟩)
      omega
  | case13 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibNotReady hsepNone ih =>
      simp only [ki, i] at hsep hsepNone
      rw [hsep] at hsepNone
      cases hsepNone
  | case14 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibNotReady hrightNone sep2 hsep2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightNone hsep2
      simp only [ki, i] at hsep
      have hsepEq : sep = sep2 := Option.some.inj (hsep.symm.trans hsep2)
      subst sep2
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild, hleftSib, hrightNone]
      simp [hne, hchildNotReady, hleftSibNotReady]
      have hlt := merge_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨i - 1, hleftSib⟩)
        (List.mem_iff_getElem?.mpr ⟨i, hchild⟩)
      omega
  | case15 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady leftSib hleftSib hleftSibNotReady hrightNone hsepNone ih =>
      simp only [ki, i] at hsep hsepNone
      rw [hsep] at hsepNone
      cases hsepNone
  | case16 x ks cs hnonempty i hpos ki sep hsep hne child hchild hchildNotReady hleftNone ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hchild hleftNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchild, hleftNone]
      simp [hne, hchildNotReady]
      have hlt := child_lt_node ks hchild
      omega
  | case17 x ks cs hnonempty i hpos ki sep hsep hne hchildNone =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsep hchildNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsep, hchildNone]
      simp [hne]
  | case18 x ks cs hnonempty i hpos ki hsepNone child hchild hchildReady ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsepNone hchild
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild]
      simp [hchildReady]
      have hlt := child_lt_node ks hchild
      omega
  | case19 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibReady sep hsep ih =>
      simp only [i] at hsep
      simp only [ki, i] at hsepNone
      rw [hsepNone] at hsep
      cases hsep
  | case20 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibReady hsepNone2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib
      simp only [ki, i] at hsepNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild, hleftSib]
      simp [hchildNotReady, hleftSibReady]
      have hlt := child_lt_node ks hchild
      omega
  | case21 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibReady sep hsep ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightSib hsep
      simp only [ki, i] at hsepNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild, hleftSib, hrightSib, hsep]
      simp [hchildNotReady, hleftSibNotReady, hrightSibReady]
      have hlt := rotateRight_target_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨i, hchild⟩)
        (List.mem_iff_getElem?.mpr ⟨i + 1, hrightSib⟩)
      omega
  | case22 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibReady hsepNone2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightSib hsepNone2
      simp only [ki, i] at hsepNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild, hleftSib, hrightSib, hsepNone2]
      simp [hchildNotReady, hleftSibNotReady, hrightSibReady]
      have hlt := child_lt_node ks hchild
      omega
  | case23 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibNotReady sep hsep ih =>
      simp only [i] at hsep
      simp only [ki, i] at hsepNone
      rw [hsepNone] at hsep
      cases hsep
  | case24 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibNotReady rightSib hrightSib hrightSibNotReady hsepNone2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightSib
      simp only [ki, i] at hsepNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild, hleftSib, hrightSib]
      simp [hchildNotReady, hleftSibNotReady, hrightSibNotReady]
      have hlt := child_lt_node ks hchild
      omega
  | case25 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibNotReady hrightNone sep hsep ih =>
      simp only [i] at hsep
      simp only [ki, i] at hsepNone
      rw [hsepNone] at hsep
      cases hsep
  | case26 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady leftSib hleftSib hleftSibNotReady hrightNone hsepNone2 ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftSib hrightNone
      simp only [ki, i] at hsepNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild, hleftSib, hrightNone]
      simp [hchildNotReady, hleftSibNotReady]
      have hlt := child_lt_node ks hchild
      omega
  | case27 x ks cs hnonempty i hpos ki hsepNone child hchild hchildNotReady hleftNone ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos hchild hleftNone
      simp only [ki, i] at hsepNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchild, hleftNone]
      simp [hchildNotReady]
      have hlt := child_lt_node ks hchild
      omega
  | case28 x ks cs hnonempty i hpos ki hsepNone hchildNone =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hpos
      simp only [ki, i] at hsepNone hchildNone
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte, hpos]
      rw [hsepNone, hchildNone]
      simp
  | case29 x ks cs hnonempty i hnotPos child hchild hchildReady ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild]
      simp [hchildReady]
      have hlt := child_lt_node ks hchild
      omega
  | case30 x ks cs hnonempty i hnotPos child hchild hchildNotReady rightSib hrightSib hrightSibReady sep hsep ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild, hrightSib, hsep]
      simp [hchildNotReady, hrightSibReady]
      have hlt := rotateRight_target_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨0, hchild⟩)
        (List.mem_iff_getElem?.mpr ⟨1, hrightSib⟩)
      omega
  | case31 x ks cs hnonempty i hnotPos child hchild hchildNotReady rightSib hrightSib hrightSibReady hsepNone ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild, hrightSib, hsepNone]
      simp [hchildNotReady, hrightSibReady]
      have hlt := child_lt_node ks hchild
      omega
  | case32 x ks cs hnonempty i hnotPos child hchild hchildNotReady rightSib hrightSib hrightSibNotReady sep hsep ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild, hrightSib, hsep]
      simp [hchildNotReady, hrightSibNotReady]
      have hlt := merge_lt_node ks sep (List.mem_iff_getElem?.mpr ⟨0, hchild⟩)
        (List.mem_iff_getElem?.mpr ⟨1, hrightSib⟩)
      omega
  | case33 x ks cs hnonempty i hnotPos child hchild hchildNotReady rightSib hrightSib hrightSibNotReady hsepNone ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild, hrightSib, hsepNone]
      simp [hchildNotReady, hrightSibNotReady]
      have hlt := child_lt_node ks hchild
      omega
  | case34 x ks cs hnonempty i hnotPos child hchild hchildNotReady hrightNone ih =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchild, hrightNone]
      simp [hchildNotReady]
      have hlt := child_lt_node ks hchild
      omega
  | case35 x ks cs hnonempty i hnotPos hchildNone =>
      have hnotLeaf : cs.isEmpty = false := Bool.eq_false_of_not_eq_true hnonempty
      simp only [i] at hnotPos
      rw [deleteCost]
      simp only [hnotLeaf, Bool.false_eq_true, ↓reduceIte]
      rw [dif_neg hnotPos]
      rw [hchildNone]
      simp

/-! ## Top-level insertion cost -/

/--
Number of nodes read and written by the top-level {lit}`insertRoot`: the
{lit}`insertNonFull` descent, plus one extra node for the full-root split.
-/
def insertRootCost (t x : Nat) (tr : BTree) : Nat :=
  if rootKeyCount tr = 2 * t - 1 then insertCost t x (splitRoot t tr) + 1
  else insertCost t x tr

/-- **O(h) top-level insertion.**  Splitting a full root adds exactly one
level and then {lit}`insertNonFull` descends at most one path, so the cost is
bounded by the tree height plus three. -/
theorem insertRootCost_le_height (t x : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) :
    insertRootCost t x tr ≤ heightOf tr + 3 := by
  unfold insertRootCost
  by_cases hfull : rootKeyCount tr = 2 * t - 1
  · rw [if_pos hfull]
    have hsplit : heightOf (splitRoot t tr) = heightOf tr + 1 :=
      splitRoot_height t ht hwf hfull
    have hins := insertCost_le_height t x (splitRoot t tr)
    omega
  · rw [if_neg hfull]
    have hins := insertCost_le_height t x tr
    omega

/-! ## `O(log_t n)` disk-access bounds -/

/--
The CLRS `O(log_t n)` disk-access bound: the height of a well-formed tree is
at most `log_t ((n+1)/2)`, and every operation adds a constant number of
levels.
-/
def diskAccessBound (t : Nat) (n : Nat) : Nat := Nat.log t ((n + 1) / 2) + 3

/-- Search performs at most `log_t n + O(1)` disk accesses on a well-formed
tree. -/
theorem searchCost_le_diskAccessBound (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) (x : Nat) :
    searchCost x tr ≤ diskAccessBound t (totalKeys tr) := by
  have hh : heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2) :=
    wellFormed_height_log_bound t ht hwf
  have hc := searchCost_le_height x tr
  unfold diskAccessBound
  omega

/-- Top-level insertion performs at most `log_t n + O(1)` disk accesses on a
well-formed tree. -/
theorem insertRootCost_le_diskAccessBound (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) (x : Nat) :
    insertRootCost t x tr ≤ diskAccessBound t (totalKeys tr) := by
  have hh : heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2) :=
    wellFormed_height_log_bound t ht hwf
  have hc := insertRootCost_le_height t x ht hwf
  unfold diskAccessBound
  omega

/-- Deletion performs at most `log_t n + O(1)` disk accesses on a well-formed
tree. -/
theorem deleteCost_le_diskAccessBound (t : Nat) (ht : 2 ≤ t) {tr : BTree}
    (hwf : WellFormed t tr) (x : Nat) :
    deleteCost t x tr ≤ diskAccessBound t (totalKeys tr) := by
  have hh : heightOf tr ≤ Nat.log t ((totalKeys tr + 1) / 2) :=
    wellFormed_height_log_bound t ht hwf
  have hc := deleteCost_le_height t x tr
  unfold diskAccessBound
  omega

/--
**`O(log_t n)` disk accesses.**  The common bound
{lit}`diskAccessBound t n = log_t ((n+1)/2) + 3` is `O(log_t n)`, so search,
insertion, and deletion each run in `O(log_t n)` disk accesses on a
well-formed tree.
-/
theorem diskAccessBound_isBigO_log_t (t : Nat) (ht : 2 ≤ t) :
    CLRS.Chapter03.isBigO (fun n => (diskAccessBound t n : ℝ))
      (fun n => (Nat.log t n : ℝ)) := by
  rw [CLRS.Chapter03.isBigO_iff]
  refine ⟨4, by norm_num, t, ?_⟩
  intro n hn
  have hmono : Nat.log t ((n + 1) / 2) ≤ Nat.log t n := by
    apply Nat.log_mono_right
    omega
  have hlogpos : 0 < Nat.log t n := Nat.log_pos (by omega : 1 < t) (by omega : t ≤ n)
  unfold diskAccessBound
  have h1 : (Nat.log t ((n + 1) / 2) + 3 : ℝ) ≤ 4 * (Nat.log t n : ℝ) := by
    have h2 : (Nat.log t ((n + 1) / 2) : ℝ) ≤ (Nat.log t n : ℝ) := by
      exact_mod_cast hmono
    have h3 : (3 : ℝ) ≤ 3 * (Nat.log t n : ℝ) := by
      have h4 : (1 : ℝ) ≤ (Nat.log t n : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hlogpos)
      nlinarith
    nlinarith
  have h_nonneg_left : 0 ≤ ((Nat.log t ((n + 1) / 2) + 3 : Nat) : ℝ) := by positivity
  have h_nonneg_right : 0 ≤ (Nat.log t n : ℝ) := by positivity
  rw [abs_of_nonneg h_nonneg_left, abs_of_nonneg h_nonneg_right]
  push_cast
  exact h1

end BTree
end Chapter18
end CLRS
