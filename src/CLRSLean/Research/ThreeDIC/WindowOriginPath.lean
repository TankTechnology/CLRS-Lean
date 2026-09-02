import CLRSLean.Research.ThreeDIC.FiniteGrid
import Mathlib.Data.List.Chain

/-!
# Explicit paths through finite repair-window origins

This module constructs inclusive monotone paths between natural coordinates
and combines two such paths into a Manhattan path between window origins.
-/

namespace CLRS.Research.ThreeDIC

/-- Inclusive monotone path from {lit}`a` to {lit}`b`. -/
def natIntervalPath (a b : Nat) : List Nat :=
  if a ≤ b then List.range' a (b - a + 1)
  else (List.range' b (a - b + 1)).reverse

theorem natIntervalPath_head? (a b : Nat) :
    (natIntervalPath a b).head? = some a := by
  unfold natIntervalPath
  split
  · simp [List.head?_range']
  · simp [List.getLast?_range']; omega

theorem natIntervalPath_getLast? (a b : Nat) :
    (natIntervalPath a b).getLast? = some b := by
  unfold natIntervalPath
  split
  · simp [List.getLast?_range']; omega
  · simp [List.head?_range']

private theorem natIntervalPath_length (a b : Nat) :
    (natIntervalPath a b).length = Nat.dist a b + 1 := by
  unfold natIntervalPath
  split <;> simp [Nat.dist] <;> omega

private theorem natIntervalPath_drop_getLast? (a b : Nat) :
    ((natIntervalPath a b).drop 1).getLast? =
      if a = b then none else some b := by
  rw [List.getLast?_drop, natIntervalPath_length, natIntervalPath_getLast?]
  by_cases h : a = b
  · simp [h]
  · have hdist : 0 < Nat.dist a b := Nat.dist_pos_of_ne h
    simp [h]
    omega

private theorem natIntervalPath_tail_getLast? (a b : Nat) :
    (natIntervalPath a b).tail.getLast? =
      if a = b then none else some b := by
  simpa using natIntervalPath_drop_getLast? a b

private theorem natIntervalPath_tail_map_getLast?
    (a b : Nat) (f : Nat → α) :
    ((natIntervalPath a b).tail.map f).getLast? =
      if a = b then none else some (f b) := by
  rw [List.getLast?_map, natIntervalPath_tail_getLast?]
  split <;> simp_all

private theorem range'_dist_isChain (a n : Nat) :
    (List.range' a n).IsChain (fun x y => Nat.dist x y = 1) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [List.length_range'] at hi
  simp only [List.getElem_range'_1]
  unfold Nat.dist
  omega

theorem natIntervalPath_isChain (a b : Nat) :
    (natIntervalPath a b).IsChain (fun x y => Nat.dist x y = 1) := by
  unfold natIntervalPath
  split
  · exact range'_dist_isChain _ _
  · rw [List.isChain_reverse]
    simpa only [Nat.dist_comm] using range'_dist_isChain b (a - b + 1)

theorem natIntervalPath_mem_between {a b z : Nat}
    (hz : z ∈ natIntervalPath a b) :
    min a b ≤ z ∧ z ≤ max a b := by
  unfold natIntervalPath at hz
  split at hz
  · simp only [List.mem_range'_1] at hz
    omega
  · simp only [List.mem_reverse, List.mem_range'_1] at hz
    omega

/-- Manhattan path from origin {lit}`a` to origin {lit}`b`. -/
def windowOriginPath (a b : Nat × Nat) : List (Nat × Nat) :=
  (natIntervalPath a.1 b.1).map (fun i => (i, a.2)) ++
  (natIntervalPath a.2 b.2).tail.map (fun j => (b.1, j))

theorem windowOriginPath_head? (a b : Nat × Nat) :
    (windowOriginPath a b).head? = some a := by
  simp [windowOriginPath, natIntervalPath_head?]

theorem windowOriginPath_getLast? (a b : Nat × Nat) :
    (windowOriginPath a b).getLast? = some b := by
  rw [windowOriginPath, List.getLast?_append]
  rw [natIntervalPath_tail_map_getLast?]
  rw [List.getLast?_map, natIntervalPath_getLast?]
  by_cases h : a.2 = b.2
  · simp [h]
  · simp [h]

private theorem horizontalOriginPath_isChain (a b q : Nat) :
    ((natIntervalPath a b).map (fun i => (i, q))).IsChain windowAdjacent := by
  apply List.isChain_map_of_isChain (fun i => (i, q))
    (R := fun x y => Nat.dist x y = 1) (S := windowAdjacent)
  · intro x y hxy
    simp only [windowAdjacent, Prod.mk.injEq, and_true]
    unfold Nat.dist at hxy
    omega
  · exact natIntervalPath_isChain a b

private theorem verticalOriginPath_isChain (p a b : Nat) :
    ((natIntervalPath a b).map (fun j => (p, j))).IsChain windowAdjacent := by
  apply List.isChain_map_of_isChain (fun j => (p, j))
    (R := fun x y => Nat.dist x y = 1) (S := windowAdjacent)
  · intro x y hxy
    simp only [windowAdjacent, Prod.mk.injEq, true_and]
    unfold Nat.dist at hxy
    omega
  · exact natIntervalPath_isChain a b

theorem windowOriginPath_isChain (a b : Nat × Nat) :
    (windowOriginPath a b).IsChain windowAdjacent := by
  let horizontal := (natIntervalPath a.1 b.1).map (fun i => (i, a.2))
  let verticalTail := (natIntervalPath a.2 b.2).tail.map (fun j => (b.1, j))
  change (horizontal ++ verticalTail).IsChain windowAdjacent
  have hHorizontal : horizontal.IsChain windowAdjacent :=
    horizontalOriginPath_isChain a.1 b.1 a.2
  have hVertical :
      ((natIntervalPath a.2 b.2).map (fun j => (b.1, j))).IsChain windowAdjacent :=
    verticalOriginPath_isChain b.1 a.2 b.2
  have hVerticalTail : verticalTail.IsChain windowAdjacent := by
    simpa [verticalTail] using hVertical.tail
  apply hHorizontal.append hVerticalTail
  intro x hx y hy
  have hlast : horizontal.getLast? = some (b.1, a.2) := by
    simp [horizontal, natIntervalPath_getLast?]
  rw [hlast] at hx
  simp only [Option.mem_some_iff] at hx
  subst x
  rw [List.head?_map, Option.mem_map] at hy
  obtain ⟨j, hj, rfl⟩ := hy
  have hv : (natIntervalPath a.2 b.2).IsChain
      (fun u v => Nat.dist u v = 1) := natIntervalPath_isChain _ _
  have hhead : a.2 ∈ (natIntervalPath a.2 b.2).head? := by
    rw [natIntervalPath_head?]
    simp
  have hcons : a.2 :: (natIntervalPath a.2 b.2).tail =
      natIntervalPath a.2 b.2 := List.cons_head?_tail hhead
  rw [← hcons] at hv
  have hjdist : Nat.dist a.2 j = 1 := hv.rel_head? hj
  simp only [windowAdjacent, Prod.mk.injEq, true_and]
  unfold Nat.dist at hjdist
  omega

private theorem natIntervalPath_add_le
    {N M a b z : Nat} (ha : a + M ≤ N) (hb : b + M ≤ N)
    (hz : z ∈ natIntervalPath a b) :
    z + M ≤ N := by
  have hbetween := natIntervalPath_mem_between hz
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab, max_eq_right hab] at hbetween
    omega
  · rw [min_eq_right hba, max_eq_left hba] at hbetween
    omega

theorem windowOriginPath_mem_valid
    {N M : Nat} {a b z : Nat × Nat}
    (ha : validWindowOrigin N M a) (hb : validWindowOrigin N M b)
    (hz : z ∈ windowOriginPath a b) :
    validWindowOrigin N M z := by
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  simp only [windowOriginPath, List.mem_append, List.mem_map] at hz
  rcases hz with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact ⟨natIntervalPath_add_le ha₁ hb₁ hi, ha₂⟩
  · exact ⟨hb₁, natIntervalPath_add_le ha₂ hb₂ (List.mem_of_mem_tail hj)⟩

end CLRS.Research.ThreeDIC
