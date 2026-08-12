import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.Trace.A1_LegalTrace

/-!
# Chapter 15.4 development: exact one-page cache difference

The exchange proof needs a precise relation for two equal-size caches that
differ in exactly one resident page on each side.
-/

namespace CLRS

open Finset

namespace Caching

/-- `A` contains only `a`, `B` contains only `b`, and their common cores agree. -/
def OnePageDiff (A B : Finset Page) (a b : Page) : Prop :=
  a ∈ A ∧ a ∉ B ∧ b ∉ A ∧ b ∈ B ∧ A.erase a = B.erase b

namespace OnePageDiff

lemma left_mem (h : OnePageDiff A B a b) : a ∈ A := h.1

lemma left_not_mem_right (h : OnePageDiff A B a b) : a ∉ B := h.2.1

lemma right_not_mem_left (h : OnePageDiff A B a b) : b ∉ A := h.2.2.1

lemma right_mem (h : OnePageDiff A B a b) : b ∈ B := h.2.2.2.1

lemma erase_eq (h : OnePageDiff A B a b) : A.erase a = B.erase b := h.2.2.2.2

/-- The two distinguished pages of an exact one-page difference are distinct. -/
lemma ne (h : OnePageDiff A B a b) : a ≠ b := by
  intro hab
  subst b
  exact h.right_not_mem_left h.left_mem

/-- Exact one-page-different caches are not equal. -/
lemma cache_ne (h : OnePageDiff A B a b) : A ≠ B := by
  intro hAB
  subst B
  exact h.left_not_mem_right h.left_mem

/-- Reversing the caches reverses the two distinguished pages. -/
lemma symm (h : OnePageDiff A B a b) : OnePageDiff B A b a := by
  exact ⟨h.right_mem, h.right_not_mem_left, h.left_not_mem_right,
    h.left_mem, h.erase_eq.symm⟩

/-- Membership agrees away from the two distinguished pages. -/
lemma mem_iff (h : OnePageDiff A B a b)
    (hxa : x ≠ a) (hxb : x ≠ b) : x ∈ A ↔ x ∈ B := by
  constructor
  · intro hx
    have hxe : x ∈ A.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
    rw [h.erase_eq] at hxe
    exact (Finset.mem_erase.mp hxe).2
  · intro hx
    have hxe : x ∈ B.erase b := Finset.mem_erase.mpr ⟨hxb, hx⟩
    rw [← h.erase_eq] at hxe
    exact (Finset.mem_erase.mp hxe).2

/-- Exact one-page-different caches have equal cardinality. -/
lemma card_eq (h : OnePageDiff A B a b) : A.card = B.card := by
  calc
    A.card = (A.erase a).card + 1 := (Finset.card_erase_add_one h.left_mem).symm
    _ = (B.erase b).card + 1 :=
      congrArg (fun S : Finset Page => S.card + 1) h.erase_eq
    _ = B.card := Finset.card_erase_add_one h.right_mem

/-- Removing the unique page on each side and loading the same request merges caches. -/
lemma merge (h : OnePageDiff A B a b) (r : Page) :
    insert r (A.erase a) = insert r (B.erase b) := by
  rw [h.erase_eq]

/-- Loading A's unique page after removing B's unique page recovers A. -/
lemma insert_left_erase_right (h : OnePageDiff A B a b) :
    insert a (B.erase b) = A := by
  rw [← h.erase_eq, Finset.insert_erase h.left_mem]

/-- Loading B's unique page after removing A's unique page recovers B. -/
lemma insert_right_erase_left (h : OnePageDiff A B a b) :
    insert b (A.erase a) = B := by
  rw [h.erase_eq, Finset.insert_erase h.right_mem]

/--
If A hits its unique page while B faults and evicts a common page `y`, the
new exact difference is `y` on A's side and the old `b` on B's side.
-/
lemma hit_left_fault (h : OnePageDiff A B a b) (y : Page)
    (hyB : y ∈ B) (hyb : y ≠ b) :
    OnePageDiff A (insert a (B.erase y)) y b := by
  have hya : y ≠ a := by
    intro hya
    subst y
    exact h.left_not_mem_right hyB
  have hyA : y ∈ A := (h.mem_iff hya hyb).2 hyB
  refine ⟨hyA, ?_, h.right_not_mem_left, ?_, ?_⟩
  · simp [hya]
  · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hyb.symm, h.right_mem⟩)
  · calc
      A.erase y = (insert a (A.erase a)).erase y := by
        rw [Finset.insert_erase h.left_mem]
      _ = insert a ((A.erase a).erase y) := by
        rw [Finset.erase_insert_of_ne hya.symm]
      _ = insert a ((B.erase b).erase y) := by rw [h.erase_eq]
      _ = insert a ((B.erase y).erase b) := by rw [Finset.erase_right_comm]
      _ = (insert a (B.erase y)).erase b := by
        rw [Finset.erase_insert_of_ne h.ne]

/-- Erasing the same non-distinguished page preserves the exact difference. -/
lemma erase_common (h : OnePageDiff A B a b) (x : Page)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    OnePageDiff (A.erase x) (B.erase x) a b := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_erase.mpr ⟨hxa.symm, h.left_mem⟩
  · intro ha
    exact h.left_not_mem_right (Finset.mem_erase.mp ha).2
  · intro hb
    exact h.right_not_mem_left (Finset.mem_erase.mp hb).2
  · exact Finset.mem_erase.mpr ⟨hxb.symm, h.right_mem⟩
  · rw [Finset.erase_right_comm, h.erase_eq, Finset.erase_right_comm]

/-- Inserting a page absent from both caches preserves their exact difference. -/
lemma insert_common (h : OnePageDiff A B a b) (r : Page)
    (hrA : r ∉ A) (hrB : r ∉ B) :
    OnePageDiff (insert r A) (insert r B) a b := by
  have hra : r ≠ a := by
    intro hra
    subst a
    exact hrA h.left_mem
  have hrb : r ≠ b := by
    intro hrb
    subst b
    exact hrB h.right_mem
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_insert_of_mem h.left_mem
  · simpa [hra.symm] using h.left_not_mem_right
  · simpa [hrb.symm] using h.right_not_mem_left
  · exact Finset.mem_insert_of_mem h.right_mem
  · rw [Finset.erase_insert_of_ne hra, Finset.erase_insert_of_ne hrb, h.erase_eq]

/-- Mirroring a common fault preserves the exact one-page difference. -/
lemma fault_common (h : OnePageDiff A B a b) (x r : Page)
    (hxa : x ≠ a) (hxb : x ≠ b) (hrA : r ∉ A) (hrB : r ∉ B) :
    OnePageDiff (insert r (A.erase x)) (insert r (B.erase x)) a b := by
  apply (h.erase_common x hxa hxb).insert_common r
  · intro hr
    exact hrA (Finset.mem_erase.mp hr).2
  · intro hr
    exact hrB (Finset.mem_erase.mp hr).2

end OnePageDiff

end Caching

end CLRS
