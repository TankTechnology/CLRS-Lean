import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.HeapExecution

/-! # Chapter 15 heap-Huffman regression surface -/

#check CLRS.HuffmanV2.heapHuffmanOfFreqs_eq
#check CLRS.HuffmanV2.heapHuffmanOfFreqs_correct
#check CLRS.HuffmanV2.heapHuffmanOfFreqs_work_le_nlogn

example :
    CLRS.HuffmanV2.heapHuffmanOfFreqs [(0, 5), (1, 5), (2, 7)] =
      CLRS.HuffmanV2.huffmanOfFreqs [(0, 5), (1, 5), (2, 7)] :=
  CLRS.HuffmanV2.heapHuffmanOfFreqs_eq _

example :
    (CLRS.HuffmanV2.heapHuffmanOfFreqsWithCost
      [(0, 2), (1, 3), (2, 7), (3, 11)]).work ≤
        4 * (4 * (Nat.log 2 (4 + 1) + 1)) :=
  CLRS.HuffmanV2.heapHuffmanOfFreqs_work_le_nlogn _
