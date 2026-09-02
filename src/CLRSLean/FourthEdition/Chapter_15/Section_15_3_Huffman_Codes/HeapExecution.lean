import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution.Cost

/-!
# Verified binary-heap Huffman interface

This facade exposes the textbook implementation result in one place: a stable
list-backed binary min-heap, exact refinement to the existing Huffman semantics,
frequency preservation and optimality, and an execution-attached
`O(n log n)` heap-controller bound.
-/

namespace CLRS.HuffmanV2

/-- The costed heap program erases exactly to the established Huffman function. -/
theorem heapHuffmanOfFreqsWithCost_eq (xs : List (Nat × Nat)) :
    (heapHuffmanOfFreqsWithCost xs).value = huffmanOfFreqs xs := by
  rw [heapHuffmanOfFreqsWithCost_value, heapHuffmanOfFreqs_eq]

/--
Bundled public contract for the genuine binary-heap Huffman implementation.
The first three conclusions concern the returned tree; the final conclusion is
the explicit controller-work bound for that same execution.
-/
theorem heapHuffmanOfFreqs_correct (xs : List (Nat × Nat))
    (h_nodup : (xs.map Prod.fst).Nodup)
    (h_pos : ∀ p ∈ xs, p.2 > 0)
    (h_nonempty : xs ≠ []) :
    (heapHuffmanOfFreqsWithCost xs).value = huffmanOfFreqs xs ∧
      (∀ symbol,
        freqOf symbol (heapHuffmanOfFreqsWithCost xs).value =
          tableFreq xs symbol) ∧
      optimum (heapHuffmanOfFreqsWithCost xs).value ∧
      (heapHuffmanOfFreqsWithCost xs).work ≤
        xs.length * (4 * (Nat.log 2 (xs.length + 1) + 1)) := by
  have hvalue := heapHuffmanOfFreqsWithCost_value xs
  have hsem := heapHuffmanOfFreqs_semantic_correct xs h_nodup h_pos h_nonempty
  refine ⟨heapHuffmanOfFreqsWithCost_eq xs, ?_, ?_,
    heapHuffmanOfFreqs_work_le_nlogn xs⟩
  · intro symbol
    rw [hvalue]
    exact hsem.1 symbol
  · rw [hvalue]
    exact hsem.2

end CLRS.HuffmanV2
