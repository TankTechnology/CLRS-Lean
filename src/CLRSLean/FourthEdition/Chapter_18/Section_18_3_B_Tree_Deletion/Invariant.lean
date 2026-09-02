import CLRSLean.FourthEdition.Chapter_18.Section_18_3_B_Tree_Deletion

/-!
# Invariant contracts for composed B-tree deletion

This module records the invariant packet required by recursive deletion and
the one-step normalization used after deleting from the root.  The raw
{lit}`composedDelete` operation may temporarily produce an empty root with one
child; {lit}`normalizeRoot` contracts exactly that shape.
-/

namespace CLRS
namespace Chapter18
namespace BTree

/-! ## Bundled deletion contracts -/

/-- The four structural invariants required at a node during deletion. -/
def NodeWF (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  Sorted tr ∧ ChildBounded tr ∧ Occupancy t isRoot tr ∧ SameDepth tr

/--
The entry guard for deletion: roots are always ready, while non-root nodes
must contain at least {lit}`t` keys before recursive descent.
-/
def DeleteReady (t : Nat) (isRoot : Bool) (tr : BTree) : Prop :=
  isRoot = true ∨ t ≤ numKeys tr

/-- Every key represented after an operation was represented before it. -/
def KeysSubset (after before : BTree) : Prop :=
  ∀ k, k ∈ keysOf after → k ∈ keysOf before

/--
The structural result permitted from raw root deletion.  It is either an
ordinary occupied root or the single-child empty-root transient contracted by
{lit}`normalizeRoot`.
-/
def RootDeleteResult (t : Nat) (tr : BTree) : Prop :=
  Sorted tr ∧ ChildBounded tr ∧ SameDepth tr ∧
    (Occupancy t true tr ∨
      ∃ child, tr = node [] [child] ∧ Occupancy t false child)

namespace NodeWF

/-- Project sortedness from the deletion invariant packet. -/
theorem sorted {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) : Sorted tr :=
  h.1

/-- Project child bounds from the deletion invariant packet. -/
theorem childBounded {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) : ChildBounded tr :=
  h.2.1

/-- Project occupancy from the deletion invariant packet. -/
theorem occupancy {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) : Occupancy t isRoot tr :=
  h.2.2.1

/-- Project equal leaf depth from the deletion invariant packet. -/
theorem sameDepth {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) : SameDepth tr :=
  h.2.2.2

end NodeWF

namespace WellFormed

/-- A well-formed tree is the root-specialized deletion invariant packet. -/
theorem nodeWF {t : Nat} {tr : BTree}
    (h : WellFormed t tr) : NodeWF t true tr :=
  h

end WellFormed

/-- Root calls always satisfy the deletion-entry guard. -/
theorem deleteReady_root (t : Nat) (tr : BTree) :
    DeleteReady t true tr := by
  simp [DeleteReady]

/-- At a non-root node, readiness is exactly the CLRS {lit}`t`-key guard. -/
theorem deleteReady_nonRoot_iff (t : Nat) (tr : BTree) :
    DeleteReady t false tr ↔ t ≤ numKeys tr := by
  simp [DeleteReady]

/--
Non-root occupancy implies root occupancy when the minimum degree is at least
two.
-/
theorem occupancy_true_of_false {t : Nat} {tr : BTree}
    (ht : 2 ≤ t) (h : Occupancy t false tr) :
    Occupancy t true tr := by
  rcases tr with ⟨ks, cs⟩
  unfold Occupancy at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨hlower, hupper, hchildren, hrec⟩ := h
  have hkeys : 1 ≤ ks.length := by omega
  have hchildrenRoot :
      cs.isEmpty ∨ (2 ≤ cs.length ∧ cs.length ≤ 2 * t) := by
    rcases hchildren with hleaf | ⟨hlowerChildren, hupperChildren⟩
    · exact Or.inl hleaf
    · exact Or.inr ⟨by omega, hupperChildren⟩
  simp only [↓reduceIte]
  refine ⟨?_, hupper, hchildrenRoot, hrec⟩
  by_cases hempty : ks = [] ∧ cs = []
  · simp [hempty]
  · simpa [hempty] using hkeys

/--
Every bundled invariant packet can be viewed through the weaker root
occupancy contract when the minimum degree is at least two.
-/
theorem NodeWF.asRoot {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) (ht : 2 ≤ t) :
    NodeWF t true tr := by
  cases isRoot with
  | false =>
      exact
        ⟨h.sorted, h.childBounded,
          occupancy_true_of_false ht h.occupancy, h.sameDepth⟩
  | true =>
      simpa using h

/-! ## Root normalization -/

/--
Contract an empty root with exactly one child; leave every other tree
unchanged.
-/
def normalizeRoot : BTree → BTree
  | node [] [child] => child
  | tr => tr

/-- Run raw composed deletion and then contract its possible empty root. -/
def composedDeleteRoot (t x : Nat) (tr : BTree) : BTree :=
  normalizeRoot (composedDelete t x tr)

/-- Root normalization preserves the represented key list exactly. -/
theorem keysOf_normalizeRoot (tr : BTree) :
    keysOf (normalizeRoot tr) = keysOf tr := by
  rcases tr with ⟨ks, cs⟩
  cases ks with
  | nil =>
      cases cs with
      | nil => rfl
      | cons child rest =>
          cases rest with
          | nil => simp [normalizeRoot, keysOf]
          | cons child₂ rest => rfl
  | cons k ks => rfl

/--
Root normalization either preserves height or removes exactly the old root
level.
-/
theorem heightOf_normalizeRoot (tr : BTree) :
    heightOf (normalizeRoot tr) = heightOf tr ∨
      heightOf (normalizeRoot tr) + 1 = heightOf tr := by
  rcases tr with ⟨ks, cs⟩
  cases ks with
  | nil =>
      cases cs with
      | nil => exact Or.inl rfl
      | cons child rest =>
          cases rest with
          | nil =>
              right
              simp [normalizeRoot, heightOf, Nat.add_comm]
          | cons child₂ rest => exact Or.inl rfl
  | cons k ks => exact Or.inl rfl

private theorem normalizeRoot_eq_self_of_occupancy_true
    {t : Nat} {tr : BTree} (h : Occupancy t true tr) :
    normalizeRoot tr = tr := by
  rcases tr with ⟨ks, cs⟩
  cases ks with
  | nil =>
      cases cs with
      | nil => rfl
      | cons child rest =>
          cases rest with
          | nil => simp [Occupancy] at h
          | cons child₂ rest => rfl
  | cons k ks => rfl

/--
Normalizing either allowed raw-root result produces a genuinely well-formed
B-tree root.
-/
theorem normalizeRoot_wellFormed {t : Nat} {tr : BTree}
    (ht : 2 ≤ t) (h : RootDeleteResult t tr) :
    WellFormed t (normalizeRoot tr) := by
  obtain ⟨hsorted, hbounded, hdepth, hroot⟩ := h
  rcases hroot with hoccupancy | ⟨child, htr, hchildOccupancy⟩
  · rw [normalizeRoot_eq_self_of_occupancy_true hoccupancy]
    exact ⟨hsorted, hbounded, hoccupancy, hdepth⟩
  · subst tr
    unfold Sorted at hsorted
    unfold ChildBounded at hbounded
    have hchildSorted : Sorted child :=
      hsorted.2 child (by simp)
    have hchildBounded : ChildBounded child :=
      hbounded.2.2 child (by simp)
    have hchildDepth : SameDepth child :=
      sameDepth_children_sd hdepth child (by simp)
    change WellFormed t child
    exact ⟨hchildSorted, hchildBounded,
      occupancy_true_of_false ht hchildOccupancy, hchildDepth⟩

/-! ## Recursive-descent lookup and guard helpers -/

/--
Every strict in-range list index has a concrete `getElem?` witness.
-/
theorem getElem?_exists_of_lt {α : Type*} {xs : List α} {i : Nat}
    (hi : i < xs.length) :
    ∃ a, xs[i]? = some a :=
  ⟨xs[i], List.getElem?_eq_getElem hi⟩

/--
A positive index bounded by the list length has an in-range predecessor.
-/
theorem getElem?_pred_exists {α : Type*} {xs : List α} {i : Nat}
    (hpos : 0 < i) (hi : i ≤ xs.length) :
    ∃ a, xs[i - 1]? = some a :=
  getElem?_exists_of_lt (by omega)

/--
If an indexed list element exists and its index is positive, its immediate
left sibling exists.
-/
theorem getElem?_leftSibling_exists {α : Type*} {xs : List α} {i : Nat} {a : α}
    (hcurrent : xs[i]? = some a) (hpos : 0 < i) :
    ∃ left, xs[i - 1]? = some left := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp hcurrent).1
  exact getElem?_pred_exists hpos (Nat.le_of_lt hi)

/--
If index plus one is below the list length, the immediate right sibling
exists.
-/
theorem getElem?_rightSibling_exists {α : Type*} {xs : List α} {i : Nat}
    (hi : i + 1 < xs.length) :
    ∃ right, xs[i + 1]? = some right :=
  getElem?_exists_of_lt hi

/--
A positive child-search index always has a concrete separator immediately
before it.
-/
theorem findChild_predecessor_exists {ks : List Nat} {x : Nat}
    (hpos : 0 < findChild ks x) :
    ∃ sep, ks[findChild ks x - 1]? = some sep :=
  getElem?_pred_exists hpos (findChild_le ks x)

/--
The predecessor-separator fallback of {name}`composedDelete` is unreachable
at a positive child-search index.
-/
theorem findChild_predecessor_none_absurd {ks : List Nat} {x : Nat}
    (hpos : 0 < findChild ks x)
    (hnone : ks[findChild ks x - 1]? = none) :
    False := by
  obtain ⟨sep, hsep⟩ := findChild_predecessor_exists hpos
  rw [hnone] at hsep
  simp at hsep

namespace NodeWF

/--
Every child of a node satisfying the bundled invariant packet satisfies the
same packet as a non-root node.
-/
theorem child {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    {child : BTree} (h : NodeWF t isRoot (node ks cs)) (hchild : child ∈ cs) :
    NodeWF t false child := by
  have hsorted := h.sorted
  have hbounded := h.childBounded
  have hoccupancy := h.occupancy
  unfold Sorted at hsorted
  unfold ChildBounded at hbounded
  unfold Occupancy at hoccupancy
  refine ⟨hsorted.2 child hchild, hbounded.2.2 child hchild,
    hoccupancy.2.2.2 child hchild, ?_⟩
  exact sameDepth_children_sd h.sameDepth child hchild

/--
An occupied, nonempty bundled node has at least one key at every descendant
when the minimum degree is at least two.
-/
theorem allKeysPos {t : Nat} {isRoot : Bool} {tr : BTree}
    (h : NodeWF t isRoot tr) (ht : 2 ≤ t) (hne : 0 < numKeys tr) :
    AllKeysPos tr :=
  allKeysPos_of_occupancy t ht tr isRoot h.occupancy hne

/--
A non-root bundled node automatically has at least one key at every descendant
when the minimum degree is at least two.
-/
theorem nonRoot_allKeysPos {t : Nat} {tr : BTree}
    (h : NodeWF t false tr) (ht : 2 ≤ t) : AllKeysPos tr := by
  apply h.allKeysPos ht
  rcases tr with ⟨ks, cs⟩
  have hlower : t - 1 ≤ ks.length := (occupancy_false_dest h.occupancy).1
  show 0 < ks.length
  omega

/--
The children of a bundled node are either absent or number exactly one more
than its keys.
-/
theorem children_rel {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) :
    cs = [] ∨ cs.length = ks.length + 1 :=
  childBounded_children_rel h.childBounded

/--
On an internal bundled node, `findChild` always selects an in-range child.
-/
theorem findChild_lt {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ []) (x : Nat) :
    findChild ks x < cs.length := by
  have hlength : cs.length = ks.length + 1 :=
    h.children_rel.resolve_left hchildren
  have hfind : findChild ks x ≤ ks.length := findChild_le ks x
  omega

/--
On an internal bundled node, the child selected by {name}`findChild` has a
concrete {name}`getElem?` witness.
-/
theorem findChild_exists
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ []) (x : Nat) :
    ∃ child, cs[findChild ks x]? = some child :=
  getElem?_exists_of_lt (h.findChild_lt hchildren x)

/--
The missing-current-child fallback is unreachable in an internal bundled
node.
-/
theorem findChild_none_absurd
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ [])
    {x : Nat} (hnone : cs[findChild ks x]? = none) :
    False := by
  obtain ⟨child, hchild⟩ := h.findChild_exists hchildren x
  rw [hnone] at hchild
  simp at hchild

/--
At a positive child-search index, the missing-left-sibling fallback is
unreachable in an internal bundled node.
-/
theorem findChild_leftSibling_none_absurd
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ [])
    {x : Nat} (hpos : 0 < findChild ks x)
    (hnone : cs[findChild ks x - 1]? = none) :
    False := by
  have hcurrentLt := h.findChild_lt hchildren x
  obtain ⟨left, hleft⟩ :=
    getElem?_pred_exists hpos (Nat.le_of_lt hcurrentLt)
  rw [hnone] at hleft
  simp at hleft

/--
Every nonempty child list in a bundled node has at least two entries when the
minimum degree is at least two.  This is the root/non-root common form needed
by the right-sibling branch at child index zero.
-/
theorem two_le_children_of_not_empty
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (ht : 2 ≤ t)
    (hchildren : cs ≠ []) :
    2 ≤ cs.length := by
  have hoccupancy := h.occupancy
  unfold Occupancy at hoccupancy
  cases isRoot with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hoccupancy
      rcases hoccupancy.2.2.1 with hempty | hbounds
      · exact absurd (List.isEmpty_iff.mp hempty) hchildren
      · omega
  | true =>
      simp only [↓reduceIte] at hoccupancy
      rcases hoccupancy.2.2.1 with hempty | hbounds
      · exact absurd (List.isEmpty_iff.mp hempty) hchildren
      · exact hbounds.1

/--
The right sibling of child zero exists in every internal bundled node.
-/
theorem rightSibling_zero_exists
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (ht : 2 ≤ t)
    (hchildren : cs ≠ []) :
    ∃ right, cs[1]? = some right :=
  getElem?_exists_of_lt (h.two_le_children_of_not_empty ht hchildren)

/--
Whenever child {lit}`i + 1` exists, the separator immediately before it is
present in the parent key list.
-/
theorem separator_before_rightSibling_exists
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ [])
    {i : Nat} {right : BTree} (hright : cs[i + 1]? = some right) :
    ∃ sep, ks[i]? = some sep := by
  have hrightIndex : i + 1 < cs.length :=
    (List.getElem?_eq_some_iff.mp hright).1
  have hlength : cs.length = ks.length + 1 :=
    h.children_rel.resolve_left hchildren
  exact getElem?_exists_of_lt (by omega)

/--
The child to the left of a present separator key exists in every internal
bundled node.
-/
theorem leftChild_exists_of_key
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    {ki sep : Nat} (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ [])
    (hkey : ks[ki]? = some sep) :
    ∃ child, cs[ki]? = some child := by
  have hki : ki < ks.length := (List.getElem?_eq_some_iff.mp hkey).1
  have hlength : cs.length = ks.length + 1 :=
    h.children_rel.resolve_left hchildren
  exact getElem?_exists_of_lt (by omega)

/--
The child to the right of a present separator key exists in every internal
bundled node; the right child is at separator index plus one.
-/
theorem rightChild_exists_of_key
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    {ki sep : Nat} (h : NodeWF t isRoot (node ks cs)) (hchildren : cs ≠ [])
    (hkey : ks[ki]? = some sep) :
    ∃ child, cs[ki + 1]? = some child := by
  have hki : ki < ks.length := (List.getElem?_eq_some_iff.mp hkey).1
  have hlength : cs.length = ks.length + 1 :=
    h.children_rel.resolve_left hchildren
  exact getElem?_exists_of_lt (by omega)

/--
Any two children of a bundled node have the same height.
-/
theorem siblings_height
    {t : Nat} {isRoot : Bool} {ks : List Nat} {cs : List BTree}
    (h : NodeWF t isRoot (node ks cs)) {left right : BTree}
    (hleft : left ∈ cs) (hright : right ∈ cs) :
    heightOf left = heightOf right :=
  (sameDepth_iff.mp h.sameDepth).2 left hleft right hright

/--
Project the complete local facts for two children adjacent to a present
separator: both child packets, equal height, and the two separator key bounds.
-/
theorem adjacent_children
    {t j sep : Nat} {isRoot : Bool}
    {ks : List Nat} {cs : List BTree} {left right : BTree}
    (h : NodeWF t isRoot (node ks cs))
    (hsep : ks[j]? = some sep)
    (hleft : cs[j]? = some left)
    (hright : cs[j + 1]? = some right) :
    NodeWF t false left ∧ NodeWF t false right ∧
      heightOf left = heightOf right ∧
      (∀ k ∈ keysOf left, k ≤ sep) ∧
      (∀ k ∈ keysOf right, sep ≤ k) := by
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
  have hbounds := h.childBounded
  unfold ChildBounded at hbounds
  have hleftBounds := hbounds.2.1 j hjLeft
  rw [hleftGet, hsep] at hleftBounds
  have hrightBounds := hbounds.2.1 (j + 1) hjRight
  rw [hrightGet] at hrightBounds
  have hrightLower : ∀ k ∈ keysOf right, sep ≤ k := by
    rcases hrightBounds.1 with hzero | hlower
    · omega
    · rw [show j + 1 - 1 = j by omega, hsep] at hlower
      exact hlower
  exact
    ⟨h.child hleftMem, h.child hrightMem,
      h.siblings_height hleftMem hrightMem,
      hleftBounds.2, hrightLower⟩

end NodeWF

/--
A non-ready occupied non-root node has exactly the minimum `t - 1` keys.
-/
theorem numKeys_eq_t_sub_one_of_not_ready
    {t : Nat} {tr : BTree} (hoccupancy : Occupancy t false tr)
    (hnotReady : ¬ t ≤ numKeys tr) :
    numKeys tr = t - 1 := by
  rcases tr with ⟨ks, cs⟩
  have hlower : t - 1 ≤ ks.length := (occupancy_false_dest hoccupancy).1
  change ¬ t ≤ ks.length at hnotReady
  change ks.length = t - 1
  omega

namespace KeysSubset

/-- Every tree's represented keys are a subset of themselves. -/
theorem refl (tr : BTree) : KeysSubset tr tr := by
  intro k hk
  exact hk

/-- Key containment composes through an intermediate tree. -/
theorem trans {after middle before : BTree}
    (h₁ : KeysSubset after middle) (h₂ : KeysSubset middle before) :
    KeysSubset after before := by
  intro k hk
  exact h₂ k (h₁ k hk)

end KeysSubset

end BTree
end Chapter18
end CLRS
