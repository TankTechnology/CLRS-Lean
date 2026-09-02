import CLRSLean.FourthEdition.Chapter_12.Section_12_1_Binary_Search_Trees
import CLRSLean.Extensions.TreapHeight

/-!
# Section 12.4 - Random BST construction and height bridge

This module identifies the tree built from an insertion permutation with the
canonical random-priority tree already analyzed by the treap probability
library.  Earlier insertion positions become larger priorities by reversing
the position permutation.  Consequently both models have exactly the same
ancestor relation, pointwise depths, and height for every sample—not merely the
same distribution.
-/

namespace CLRS
namespace Chapter12
namespace BSTree

open CLRS.Probability

/-- Convert an insertion-order permutation into the corresponding priority
permutation: earlier insertion positions receive larger priorities. -/
noncomputable def priorityPermOfInsertion {n : Nat}
    (π : Equiv.Perm (Fin n)) : Extensions.Treap.PrioPerm n :=
  Extensions.Treap.revBijection.symm π

/-- Converting insertion order to priorities and back recovers the original
insertion permutation. -/
@[simp] theorem revBijection_priorityPermOfInsertion {n : Nat}
    (π : Equiv.Perm (Fin n)) :
    Extensions.Treap.revBijection (priorityPermOfInsertion π) = π := by
  exact Extensions.Treap.revBijection.apply_symm_apply π

/-- A key belongs to the list of keys induced by every permutation. -/
theorem mem_permKeys_self {n : Nat} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    (j : Nat) ∈ permKeys π := by
  unfold permKeys
  rw [List.mem_map]
  refine ⟨π.symm j, by simp, ?_⟩
  simp

/-- Every key of {lit}`Fin n` occurs in the BST built from a permutation. -/
theorem InTree_buildFromPerm {n : Nat} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    InTree (j : Nat) (buildFromPerm π) := by
  rw [buildFromPerm, InTree_buildFromList_iff]
  exact mem_permKeys_self π j

/-- The insertion-order BST and its reversed-priority treap have the same
ancestor relation, sample by sample. -/
theorem isAncestorOf_buildFromPerm_iff_treapAncestor {n : Nat}
    (π : Equiv.Perm (Fin n)) (a b : Fin n) :
    isAncestorOf (a : Nat) (b : Nat) (buildFromPerm π) ↔
      Extensions.Treap.Ancestor (priorityPermOfInsertion π) a b := by
  rw [isAncestorOf_buildFromPerm_iff_firstInInterval]
  rw [firstInInterval_iff_isFirstOf]
  let S : Finset (Fin n) := Finset.Icc (min a b) (max a b)
  let σ : Extensions.Treap.PrioPerm n := priorityPermOfInsertion π
  change isFirstOf π S a ↔ Extensions.Treap.Ancestor σ a b
  by_cases hab : a = b
  · subst b
    simp [isFirstOf, S, Extensions.Treap.Ancestor]
  · have haS : a ∈ S := by
      dsimp [S]
      exact Finset.mem_Icc.mpr ⟨min_le_left _ _, le_max_left _ _⟩
    have hfirst :
        Extensions.Treap.MaxOver σ S a ↔ isFirstOf π S a := by
      have h := Extensions.Treap.maxOver_iff_firstIn S a σ
      simpa [CLRS.Chapter07.IsFirstIn, CLRS.Chapter07.pos, isFirstOf, σ] using h
    constructor
    · intro h
      have hmax := hfirst.mpr h
      exact Or.inr hmax.2
    · intro h
      rcases h with heq | hmax
      · exact (hab heq).elim
      · exact hfirst.mp ⟨haS, hmax⟩

/-- For a present key in an ordered BST, its one-based depth is at most the
tree height. -/
theorem depth_add_one_le_height_of_inTree {y : Nat} {t : BSTree}
    (ht : Ordered t) (hy : InTree y t) :
    depth y t + 1 ≤ height t := by
  induction t with
  | empty => simp [InTree] at hy
  | node left key right ihLeft ihRight =>
      simp only [Ordered] at ht
      rcases ht with ⟨hleft, hright, hlt, hgt⟩
      simp only [InTree] at hy
      rcases hy with hykey | hyleft | hyright
      · subst y
        simp [depth, height]
      · have hylt : y < key := hlt y hyleft
        have hyne : y ≠ key := ne_of_lt hylt
        have hIH := ihLeft hleft hyleft
        simp [depth, height, hyne, hylt]
        omega
      · have hygt : key < y := hgt y hyright
        have hyne : y ≠ key := ne_of_gt hygt
        have hynlt : ¬ y < key := Nat.not_lt.mpr (le_of_lt hygt)
        have hIH := ihRight hright hyright
        simp [depth, height, hyne, hynlt]
        omega

/-- Every nonempty ordered BST contains a key whose one-based depth realizes
the tree height. -/
theorem exists_depth_add_one_eq_height :
    ∀ t : BSTree, Ordered t → t ≠ empty →
      ∃ y : Nat, InTree y t ∧ depth y t + 1 = height t
  | empty, _ht, hne => (hne rfl).elim
  | node left key right, ht, _hne => by
      simp only [Ordered] at ht
      rcases ht with ⟨hleft, hright, hlt, hgt⟩
      by_cases hmax : height right ≤ height left
      · cases left with
        | empty =>
            cases right with
            | empty =>
                exact ⟨key, by simp [InTree], by simp [depth, height]⟩
            | node rl rk rr =>
                simp [height] at hmax
        | node ll lk lr =>
            obtain ⟨y, hyTree, hyDepth⟩ :=
              exists_depth_add_one_eq_height (node ll lk lr) hleft (by simp)
            have hylt : y < key := hlt y hyTree
            refine ⟨y, Or.inr (Or.inl hyTree), ?_⟩
            have hdepth :
                depth y ((node ll lk lr).node key right) =
                  1 + depth y (node ll lk lr) := by
              simp [depth, ne_of_lt hylt, hylt]
            rw [hdepth, height, max_eq_left hmax]
            omega
      · have hmax' : height left ≤ height right := le_of_not_ge hmax
        cases right with
        | empty =>
            exact (hmax (Nat.zero_le _)).elim
        | node rl rk rr =>
            obtain ⟨y, hyTree, hyDepth⟩ :=
              exists_depth_add_one_eq_height (node rl rk rr) hright (by simp)
            have hygt : key < y := hgt y hyTree
            have hynlt : ¬ y < key := Nat.not_lt.mpr (le_of_lt hygt)
            refine ⟨y, Or.inr (Or.inr hyTree), ?_⟩
            have hdepth :
                depth y (left.node key (node rl rk rr)) =
                  1 + depth y (node rl rk rr) := by
              simp [depth, ne_of_gt hygt, hynlt]
            rw [hdepth, height, max_eq_right hmax']
            omega

/-- Pointwise one-based depth agrees between the insertion-order BST and the
corresponding reversed-priority treap. -/
theorem depth_buildFromPerm_add_one_eq_treapDepth {n : Nat}
    (π : Equiv.Perm (Fin n)) (b : Fin n) :
    depth (b : Nat) (buildFromPerm π) + 1 =
      Extensions.Treap.depth (priorityPermOfInsertion π) b := by
  classical
  let t := buildFromPerm π
  let σ := priorityPermOfInsertion π
  have hself : isAncestorOf (b : Nat) (b : Nat) t := by
    simpa [t] using isAncestorOf_self_buildFromPerm π b
  have hordered : Ordered t := by
    simpa [t, buildFromPerm] using buildFromList_ordered (permKeys π)
  have hbounded : ∀ z, InTree z t → z < n := by
    intro z hz
    exact InTree_buildFromPerm_lt π (by simpa [t] using hz)
  have hfilter :
      Finset.univ.filter (fun a : Fin n => isAncestorOf (a : Nat) (b : Nat) t) =
        Finset.univ.filter (fun a : Fin n => Extensions.Treap.Ancestor σ a b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [t, σ] using isAncestorOf_buildFromPerm_iff_treapAncestor π a b
  calc
    depth (b : Nat) t + 1 = ancestorCount (b : Nat) t :=
      (ancestorCount_eq_depth_add_one (b : Nat) t hself).symm
    _ = (Finset.univ.filter
          (fun a : Fin n => isAncestorOf (a : Nat) (b : Nat) t)).card :=
      ancestorCount_eq_sum (b : Nat) t hordered hbounded
    _ = (Finset.univ.filter
          (fun a : Fin n => Extensions.Treap.Ancestor σ a b)).card := by
      rw [hfilter]
    _ = Extensions.Treap.depth σ b := by
      rfl

/-- **Deterministic random-BST/treap height bridge.**  For every insertion
permutation, the BST height equals the canonical treap height associated with
the reversed position priorities. -/
theorem height_buildFromPerm_eq_treapHeight {n : Nat}
    (π : Equiv.Perm (Fin n)) :
    height (buildFromPerm π) =
      Extensions.Treap.treapHeight (priorityPermOfInsertion π) := by
  classical
  let t := buildFromPerm π
  let σ := priorityPermOfInsertion π
  have hordered : Ordered t := by
    simpa [t, buildFromPerm] using buildFromList_ordered (permKeys π)
  unfold Extensions.Treap.treapHeight
  apply Nat.le_antisymm
  · by_cases hn : n = 0
    · subst n
      simp [buildFromPerm, permKeys, buildFromList, insertAll, height]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hne : t ≠ empty := by
        intro hempty
        have hmember := InTree_buildFromPerm π (⟨0, hnpos⟩ : Fin n)
        rw [show buildFromPerm π = t from rfl, hempty] at hmember
        simp [InTree] at hmember
      obtain ⟨y, hyTree, hyDepth⟩ :=
        exists_depth_add_one_eq_height t hordered hne
      have hylt : y < n := InTree_buildFromPerm_lt π (by simpa [t] using hyTree)
      let b : Fin n := ⟨y, hylt⟩
      have hsup : Extensions.Treap.depth σ b ≤
          (Finset.univ : Finset (Fin n)).sup
            (fun c => Extensions.Treap.depth σ c) :=
        Finset.le_sup (Finset.mem_univ b)
      have hbridge := depth_buildFromPerm_add_one_eq_treapDepth π b
      have hbridge' : depth y t + 1 = Extensions.Treap.depth σ b := by
        simpa [t, σ, b] using hbridge
      change height t ≤ (Finset.univ : Finset (Fin n)).sup
        (fun c => Extensions.Treap.depth σ c)
      rw [← hbridge', hyDepth] at hsup
      exact hsup
  · apply Finset.sup_le
    intro b _hb
    have hmember : InTree (b : Nat) t := by
      simpa [t] using InTree_buildFromPerm π b
    have hle := depth_add_one_le_height_of_inTree hordered hmember
    have hbridge := depth_buildFromPerm_add_one_eq_treapDepth π b
    have hbridge' : depth (b : Nat) t + 1 = Extensions.Treap.depth σ b := by
      simpa [t, σ] using hbridge
    rw [← hbridge']
    exact hle

end BSTree
end Chapter12
end CLRS
