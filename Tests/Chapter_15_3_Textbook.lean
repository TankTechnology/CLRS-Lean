import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.TextbookCost
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.TextbookLemmas
import CLRSLean.FourthEdition.Chapter_15.Section_15_3_Huffman_Codes.Complexity

open CLRS.HuffmanV2

#check textbookCost_eq_cost
#check lemma15_2_greedy_choice
#check lemma15_3_optimal_substructure
#check huffmanOfFreqsComparisons_le_quadratic
#check textbookHeapHuffmanWork_le_nlogn

#assert_axioms textbookCost_eq_cost
#assert_axioms lemma15_2_greedy_choice
#assert_axioms lemma15_3_optimal_substructure
#assert_axioms huffmanOfFreqsComparisons_le_quadratic

example :
    textbookCost
      (HuffTree.htInner (HuffTree.htLeaf 0 2) (HuffTree.htLeaf 1 3)) = 5 := by
  decide

