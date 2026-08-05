import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.LowerBound.Correctness

/-!
# CLRS Chapter 27.3 — Interleaved P-MERGE Witness Lists

The even and odd key lists are sorted, have transparent lengths, and their
prefixes reproduce the same witness family at smaller sizes.
-/

namespace CLRS
namespace Chapter27

/-- The first {name}`n` even natural numbers. -/
def evenKeys (n : ℕ) : List ℕ := (List.range n).map (fun i => 2 * i)

/-- The first {name}`n` odd natural numbers. -/
def oddKeys (n : ℕ) : List ℕ := (List.range n).map (fun i => 2 * i + 1)

@[simp] theorem evenKeys_length (n : ℕ) : (evenKeys n).length = n := by
  simp [evenKeys]

@[simp] theorem oddKeys_length (n : ℕ) : (oddKeys n).length = n := by
  simp [oddKeys]

theorem evenKeys_sorted (n : ℕ) : (evenKeys n).Pairwise (· ≤ ·) := by
  rw [evenKeys, List.pairwise_map]
  exact List.pairwise_lt_range.imp (by omega)

theorem oddKeys_sorted (n : ℕ) : (oddKeys n).Pairwise (· ≤ ·) := by
  rw [oddKeys, List.pairwise_map]
  exact List.pairwise_lt_range.imp (by omega)

@[simp] theorem evenKeys_take (m n : ℕ) :
    (evenKeys n).take m = evenKeys (min m n) := by
  simp [evenKeys, ← List.map_take]

@[simp] theorem oddKeys_take (m n : ℕ) :
    (oddKeys n).take m = oddKeys (min m n) := by
  simp [oddKeys, ← List.map_take]

theorem evenKeys_take_of_le (m n : ℕ) (h : m ≤ n) :
    (evenKeys n).take m = evenKeys m := by simp [h]

theorem oddKeys_take_of_le (m n : ℕ) (h : m ≤ n) :
    (oddKeys n).take m = oddKeys m := by simp [h]

@[simp] theorem evenKeys_get (n : ℕ) (i : Fin (evenKeys n).length) :
    (evenKeys n).get i = 2 * i.1 := by
  simp [evenKeys, List.get_eq_getElem]

@[simp] theorem evenKeys_getElem (n i : ℕ) (h : i < (evenKeys n).length) :
    (evenKeys n)[i] = 2 * i := by
  simp [evenKeys]

@[simp] theorem oddKeys_get (n : ℕ) (i : Fin (oddKeys n).length) :
    (oddKeys n).get i = 2 * i.1 + 1 := by
  simp [oddKeys, List.get_eq_getElem]

namespace ParallelMerge
namespace Costs
namespace Span

private theorem lowerBoundSpec_not_lt [LinearOrder α] {xs : List α} {pivot : α}
    {i j : ℕ} (hi : LowerBoundSpec xs pivot i)
    (hj : LowerBoundSpec xs pivot j) (hij : i < j) : False := by
  have hiLen : i < xs.length := lt_of_lt_of_le hij hj.index_le_length
  let x := xs.get ⟨i, hiLen⟩
  have hxDrop : x ∈ xs.drop i := by
    rw [List.mem_iff_getElem]
    refine ⟨0, ?_, ?_⟩
    · simp [hiLen]
    · simp [x, List.get_eq_getElem]
  have hxTake : x ∈ xs.take j := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simp [hiLen, hij]
    · simp [x, List.get_eq_getElem]
  exact (not_lt_of_ge (hi.right_ge x hxDrop)) (hj.left_lt x hxTake)

private theorem lowerBoundSpec_unique [LinearOrder α] {xs : List α} {pivot : α}
    {i j : ℕ} (hi : LowerBoundSpec xs pivot i)
    (hj : LowerBoundSpec xs pivot j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact lowerBoundSpec_not_lt hi hj hij
  · exact lowerBoundSpec_not_lt hj hi hji

private theorem oddKeys_mid_spec (m n : ℕ) (hmn : m ≤ n) :
    LowerBoundSpec (oddKeys n) (2 * m) m := by
  constructor
  · simpa using hmn
  · intro x hx
    rw [oddKeys_take_of_le m n hmn] at hx
    simp only [oddKeys, List.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [List.mem_range] at hi
    omega
  · intro x hx
    obtain ⟨j, hj, hval⟩ := List.mem_iff_getElem.mp hx
    have hglobal : m + j < (oddKeys n).length := by
      rw [List.length_drop] at hj
      omega
    have hget : (oddKeys n)[m + j] = 2 * (m + j) + 1 := by
      simp [oddKeys]
    rw [← hval, List.getElem_drop, hget]
    omega

/-- Binary lower bound splits an odd-key list exactly at the even pivot's
rank. -/
theorem binaryLowerBound_oddKeys_value (m n : ℕ) (hmn : m ≤ n) :
    (binaryLowerBound (oddKeys n) (2 * m)).value = m := by
  apply lowerBoundSpec_unique (α := ℕ)
  · exact binaryLowerBound_partition (oddKeys n) (2 * m) (oddKeys_sorted n)
  · exact oddKeys_mid_spec m n hmn

end Span
end Costs
end ParallelMerge

end Chapter27
end CLRS
