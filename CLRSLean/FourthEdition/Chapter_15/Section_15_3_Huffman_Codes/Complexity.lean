import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes

/-!
# Huffman comparison accounting

The verified executable uses sorted lists, while CLRS uses a binary min-heap.
This module makes the distinction explicit: the executable list realization has
a proved quadratic comparison bound; the textbook heap realization has the
usual {lit}`n log n` operation envelope under logarithmic heap operations.
-/

namespace CLRS.HuffmanV2

/-- Comparisons performed by the executable insertion into a sorted forest. -/
def insortComparisons (t : HuffTree) : List HuffTree → Nat
  | [] => 0
  | u :: us =>
      1 + if rootFreq t ≤ rootFreq u then 0 else insortComparisons t us

theorem insortComparisons_le_length (t : HuffTree) (ts : List HuffTree) :
    insortComparisons t ts ≤ ts.length := by
  induction ts with
  | nil => simp [insortComparisons]
  | cons u us ih =>
      simp [insortComparisons]
      split <;> omega

/-- Comparisons performed by the insertion-sort initialization. -/
def sortForestComparisons : List HuffTree → Nat
  | [] => 0
  | t :: ts =>
      sortForestComparisons ts + insortComparisons t (sortForest ts)

theorem sortForest_length (ts : List HuffTree) :
    (sortForest ts).length = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [sortForest, insortTree_length, ih]

theorem sortForestComparisons_le_sq (ts : List HuffTree) :
    sortForestComparisons ts ≤ ts.length ^ 2 := by
  induction ts with
  | nil => simp [sortForestComparisons]
  | cons t ts ih =>
      have hins := insortComparisons_le_length t (sortForest ts)
      rw [sortForest_length] at hins
      simp only [sortForestComparisons, List.length_cons]
      nlinarith

/-- Comparisons used by repeated merge-and-reinsert after initialization. -/
def huffmanComparisons : List HuffTree → Nat
  | [] => 0
  | [_] => 0
  | t₁ :: t₂ :: rest =>
      insortComparisons (unite t₁ t₂) rest +
        huffmanComparisons (insortTree (unite t₁ t₂) rest)
termination_by ts => ts.length
decreasing_by
  rw [insortTree_length]
  simp

theorem huffmanComparisons_le_sq (ts : List HuffTree) :
    huffmanComparisons ts ≤ ts.length ^ 2 := by
  induction hlen : ts.length using Nat.strong_induction_on generalizing ts with
  | h n ih =>
      cases ts with
      | nil => simp [huffmanComparisons]
      | cons t₁ tail =>
          cases tail with
          | nil => simp [huffmanComparisons]
          | cons t₂ rest =>
              let next := insortTree (unite t₁ t₂) rest
              have hnextLen : next.length = rest.length + 1 := by
                simpa [next] using insortTree_length (unite t₁ t₂) rest
              have hnextLt : next.length < n := by
                rw [hnextLen, ← hlen]
                simp
              have hrec : huffmanComparisons next ≤ next.length ^ 2 :=
                ih next.length hnextLt next rfl
              have hins := insortComparisons_le_length (unite t₁ t₂) rest
              simp only [huffmanComparisons]
              change insortComparisons (unite t₁ t₂) rest +
                  huffmanComparisons next ≤ n ^ 2
              rw [hnextLen] at hrec
              have hn : n = rest.length + 2 := by
                simpa using hlen.symm
              nlinarith

/-- Total comparisons of the verified list-based Huffman realization. -/
def huffmanOfFreqsComparisons (xs : List (Nat × Nat)) : Nat :=
  let leaves := leavesOfFreqs xs
  sortForestComparisons leaves + huffmanComparisons (sortForest leaves)

/-- The verified list implementation uses at most `2 n²` comparisons. -/
theorem huffmanOfFreqsComparisons_le_quadratic (xs : List (Nat × Nat)) :
    huffmanOfFreqsComparisons xs ≤ 2 * xs.length ^ 2 := by
  have hsort := sortForestComparisons_le_sq (leavesOfFreqs xs)
  have hmerge := huffmanComparisons_le_sq (sortForest (leavesOfFreqs xs))
  rw [sortForest_length] at hmerge
  simp [huffmanOfFreqsComparisons, leavesOfFreqs] at hsort hmerge ⊢
  omega

/-- A conservative height bound for one binary-heap operation. -/
def heapHeightBudget (n : Nat) : Nat := Nat.log 2 n + 1

/--
Textbook heap work envelope: each of the {lit}`n - 1` merges performs at most three
heap operations, each bounded by the current heap-height budget.
-/
def textbookHeapHuffmanWork (n : Nat) : Nat :=
  3 * (n - 1) * heapHeightBudget n

/-- Explicit {lit}`O(n log n)` envelope for the textbook priority-queue algorithm. -/
theorem textbookHeapHuffmanWork_le_nlogn (n : Nat) :
    textbookHeapHuffmanWork n ≤ 3 * n * (Nat.log 2 n + 1) := by
  simp [textbookHeapHuffmanWork, heapHeightBudget]

end CLRS.HuffmanV2
