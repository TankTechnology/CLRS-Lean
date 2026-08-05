import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMergeSort.Correctness
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms.ParallelMerge.Costs.Span.WitnessLists

/-!
# CLRS Chapter 27.3 — Worst-Family P-MERGE-SORT Inputs

At each level the witness places all even keys in the left half and all odd
keys in the right half.  Recursive sorting therefore feeds the interleaved
P-MERGE lower-bound family into the final merge.
-/

namespace CLRS
namespace Chapter27

/-- Power-of-two P-MERGE-SORT witness: recursively generated even keys occupy
the left half and recursively generated odd keys occupy the right half. -/
def worstMergeSortInput : ℕ → List ℕ
  | 0 => [0]
  | k + 1 =>
      (worstMergeSortInput k).map (fun x => 2 * x) ++
        (worstMergeSortInput k).map (fun x => 2 * x + 1)

@[simp] theorem worstMergeSortInput_length (k : ℕ) :
    (worstMergeSortInput k).length = 2 ^ k := by
  induction k with
  | zero => simp [worstMergeSortInput]
  | succ k ih =>
      simp [worstMergeSortInput, ih, pow_succ]
      omega

namespace ParallelMergeSort
namespace Costs
namespace Span

private theorem evenOddKeys_perm_range (n : ℕ) :
    (evenKeys n ++ oddKeys n).Perm (List.range (2 * n)) := by
  have heven : (evenKeys n).Nodup := by
    exact List.nodup_range.map (by
      intro a b h
      change 2 * a = 2 * b at h
      omega)
  have hodd : (oddKeys n).Nodup := by
    exact List.nodup_range.map (by
      intro a b h
      change 2 * a + 1 = 2 * b + 1 at h
      omega)
  have hdisjoint : List.Disjoint (evenKeys n) (oddKeys n) := by
    rw [List.disjoint_left]
    intro x hx hxo
    simp only [evenKeys, List.mem_map, List.mem_range] at hx
    simp only [oddKeys, List.mem_map, List.mem_range] at hxo
    omega
  apply (List.perm_ext_iff_of_nodup
    (heven.append hodd hdisjoint) List.nodup_range).2
  intro x
  simp only [List.mem_append, evenKeys, oddKeys, List.mem_map,
    List.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) <;> omega
  · intro hx
    obtain ⟨i, hxi⟩ : ∃ i, x = 2 * i ∨ x = 2 * i + 1 := by
      exact ⟨x / 2, by omega⟩
    rcases hxi with hxi | hxi
    · left
      exact ⟨i, by omega, hxi.symm⟩
    · right
      exact ⟨i, by omega, hxi.symm⟩

/-- The recursively generated witness contains exactly `0, ..., 2^k - 1`. -/
theorem witness_perm_range (k : ℕ) :
    (worstMergeSortInput k).Perm (List.range (2 ^ k)) := by
  induction k with
  | zero => simp [worstMergeSortInput]
  | succ k ih =>
      have heven := ih.map (fun x => 2 * x)
      have hodd := ih.map (fun x => 2 * x + 1)
      have happ := heven.append hodd
      simpa [worstMergeSortInput, evenKeys, oddKeys, pow_succ,
        Nat.mul_comm] using happ.trans (evenOddKeys_perm_range (2 ^ k))

@[simp] theorem witness_take_half (k : ℕ) :
    (worstMergeSortInput (k + 1)).take (2 ^ k) =
      (worstMergeSortInput k).map (fun x => 2 * x) := by
  simp [worstMergeSortInput, worstMergeSortInput_length]

@[simp] theorem witness_drop_half (k : ℕ) :
    (worstMergeSortInput (k + 1)).drop (2 ^ k) =
      (worstMergeSortInput k).map (fun x => 2 * x + 1) := by
  simp [worstMergeSortInput, worstMergeSortInput_length]

/-- Sorting the witness's even half produces the canonical even-key list. -/
theorem sorted_even_half (k : ℕ) :
    (pMergeSort ((worstMergeSortInput k).map (fun x => 2 * x))).value =
      evenKeys (2 ^ k) := by
  exact List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (pMergeSort_value_sorted _) (evenKeys_sorted _)
    ((pMergeSort_value_perm _).trans
      ((witness_perm_range k).map (fun x => 2 * x)))

/-- Sorting the witness's odd half produces the canonical odd-key list. -/
theorem sorted_odd_half (k : ℕ) :
    (pMergeSort ((worstMergeSortInput k).map (fun x => 2 * x + 1))).value =
      oddKeys (2 ^ k) := by
  exact List.Perm.eq_of_pairwise' (r := (· ≤ ·))
    (pMergeSort_value_sorted _) (oddKeys_sorted _)
    ((pMergeSort_value_perm _).trans
      ((witness_perm_range k).map (fun x => 2 * x + 1)))

end Span
end Costs
end ParallelMergeSort

end Chapter27
end CLRS
