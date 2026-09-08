import CLRSLean.FourthEdition.Chapter_13.Section_13_2_Rotations.Basic

/-!
# Owned pointer-tree representation

Each represented nonempty node is allocated away from NIL, has the expected
parent, and owns a footprint disjoint from both children. The expected parent
is outside the subtree. The public wrappers additionally require an absent
sentinel, and whole-store representation fixes the root parent to NIL.
-/

namespace CLRS.Chapter13
open RBStore (nil)

/-- A finite, uniquely owned subtree with consistent parent links. -/
inductive StoreReprAt (s : RBStore) : Nat → Nat → RBTree → Finset Nat → Prop where
  | empty (p : Nat) : StoreReprAt s p nil .empty ∅
  | node {p i : Nat} {n : RBNode} {l r : RBTree} {L R : Finset Nat}
      (nonzero : i ≠ nil) (read : s.get i = some n) (parent : n.parent = p)
      (left : StoreReprAt s i n.left l L) (right : StoreReprAt s i n.right r R)
      (not_left : i ∉ L) (not_right : i ∉ R) (disjoint : Disjoint L R)
      (parent_out : p ∉ insert i (L ∪ R)) :
      StoreReprAt s p i (.node n.color l n.key r) (insert i (L ∪ R))

/-- Public subtree representation retains its historical three arguments.
The expected parent and owned footprint are existential witnesses. -/
def StoreRepr (s : RBStore) (i : Nat) (t : RBTree) : Prop :=
  s.get nil = none ∧ ∃ p F, StoreReprAt s p i t F

/-- Whole-store representation requires the root's parent to be NIL. -/
def Represents (s : RBStore) (t : RBTree) : Prop :=
  s.get nil = none ∧ ∃ F, StoreReprAt s nil s.root t F

namespace StoreReprAt

/-- NIL cannot occur in an owned footprint. -/
theorem nil_not_mem {s p i t F} (h : StoreReprAt s p i t F) : nil ∉ F := by
  induction h with
  | empty => simp
  | node hn _ _ _ _ _ _ _ _ ihL ihR =>
      simp only [Finset.mem_insert, Finset.mem_union, not_or]
      exact ⟨Ne.symm hn, ihL, ihR⟩

/-- Every represented nonempty root belongs to its footprint. -/
theorem root_mem {s p i t F} (h : StoreReprAt s p i t F) (hi : i ≠ nil) : i ∈ F := by
  cases h with
  | empty => exact (hi rfl).elim
  | node => simp

/-- The external parent does not belong to the represented subtree. -/
theorem parent_not_mem {s p i t F} (h : StoreReprAt s p i t F) : p ∉ F := by
  cases h with
  | empty => simp
  | node _ _ _ _ _ _ _ _ hp => exact hp

/-- A represented node cannot point to itself as either child. -/
theorem no_self_child {s p i t F n} (h : StoreReprAt s p i t F)
    (hi : i ≠ nil) (hg : s.get i = some n) : n.left ≠ i ∧ n.right ≠ i := by
  cases h with
  | empty => exact (hi rfl).elim
  | node hn hg' hp hL hR hnL hnR hd hpo =>
    have he := Option.some.inj (hg.symm.trans hg')
    cases he
    constructor
    · intro he
      apply hnL
      simpa [he] using hL.root_mem (by simpa [he] using hi)
    · intro he
      apply hnR
      simpa [he] using hR.root_mem (by simpa [he] using hi)

/-- Non-NIL children cannot share the same owned root. -/
theorem children_distinct {s p i t F n} (h : StoreReprAt s p i t F)
    (hi : i ≠ nil) (hg : s.get i = some n) (hl : n.left ≠ nil) : n.left ≠ n.right := by
  cases h with
  | empty => exact (hi rfl).elim
  | node hn hg' hp hL hR hnL hnR hd hpo =>
    have he := Option.some.inj (hg.symm.trans hg')
    cases he
    intro he
    exact Finset.disjoint_left.mp hd (hL.root_mem hl)
      (by simpa [he] using hR.root_mem (by simpa [← he] using hl))

/-- Every occupied address has a stored record. -/
theorem mem_allocated {s p i t F} (h : StoreReprAt s p i t F)
    {j : Nat} (hj : j ∈ F) : ∃ n, s.get j = some n := by
  induction h with
  | empty => simp at hj
  | @node p i n l r L R hn hg hp hL hR hnL hnR hd hpo ihL ihR =>
      simp only [Finset.mem_insert, Finset.mem_union] at hj
      rcases hj with rfl | hj | hj
      · exact ⟨n, hg⟩
      · exact ihL hj
      · exact ihR hj

/-- Agreement on the owned nodes transports a representation to another store. -/
theorem of_agree {s s' p i t F} (h : StoreReprAt s p i t F)
    (heq : ∀ j ∈ F, s'.get j = s.get j) : StoreReprAt s' p i t F := by
  induction h with
  | empty => exact .empty _
  | @node p i n l r L R hn hg hp hL hR hnL hnR hd hpo ihL ihR =>
      apply StoreReprAt.node hn ((heq i (by simp)).trans hg) hp
      · apply ihL
        intro j hj
        exact heq j (by simp [hj])
      · apply ihR
        intro j hj
        exact heq j (by simp [hj])
      · exact hnL
      · exact hnR
      · exact hd
      · exact hpo

/-- Writes outside a subtree leave its representation unchanged. -/
theorem set_frame {s p i t F j n} (h : StoreReprAt s p i t F) (hj : j ∉ F) :
    StoreReprAt (s.set j n) p i t F := by
  apply h.of_agree
  intro k hk
  exact RBStore.get_set_ne (by rintro rfl; exact hj hk)

/-- A root address represents at most one finite tree and one footprint. -/
theorem unique {s p i t F} (h : StoreReprAt s p i t F) :
    ∀ {p' t' F'}, StoreReprAt s p' i t' F' → t = t' ∧ F = F' := by
  induction h with
  | empty p =>
      intro p' t' F' h'
      cases h' with
      | empty => exact ⟨rfl, rfl⟩
      | node hn => exact (hn rfl).elim
  | @node p i n l r L R hn hg hp hL hR hnL hnR hd hpo ihL ihR =>
      intro p' t' F' h'
      cases h' with
      | empty => exact (hn rfl).elim
      | @node _ _ n' l' r' L' R' hn' hg' hp' hL' hR' hnL' hnR' hd' hpo' =>
          have he : n = n' := Option.some.inj (hg.symm.trans hg')
          cases he
          obtain ⟨rfl, rfl⟩ := ihL hL'
          obtain ⟨rfl, rfl⟩ := ihR hR'
          exact ⟨rfl, rfl⟩

end StoreReprAt

/-- The strengthened public representation is functional. -/
theorem StoreRepr.tree_unique {s i t u} (ht : StoreRepr s i t) (hu : StoreRepr s i u) : t = u := by
  obtain ⟨_, p, F, ht⟩ := ht
  obtain ⟨_, q, G, hu⟩ := hu
  exact (ht.unique hu).1

/-- The root of a store represents at most one tree. -/
theorem Represents.tree_unique {s t u} (ht : Represents s t) (hu : Represents s u) : t = u := by
  obtain ⟨_, F, ht⟩ := ht
  obtain ⟨_, G, hu⟩ := hu
  exact (ht.unique hu).1

end CLRS.Chapter13
