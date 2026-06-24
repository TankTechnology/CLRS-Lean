# Chapter 16 - Greedy Algorithms

## Section 16.1 - Activity Selection

- Lean source: `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`
- Status: `proved` for the finite sorted-list model
- Main theorems:
  - `CLRS.ActivitySelection.earliest_finish_minFinish`
  - `CLRS.ActivitySelection.finishSorted_head_minFinish`
  - `CLRS.ActivitySelection.finishSorted_greedyChoiceCertificate`
  - `CLRS.ActivitySelection.greedySelect_sublist`
  - `CLRS.ActivitySelection.greedySelect_feasible`
  - `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`
  - `CLRS.ActivitySelection.greedySelect_maxCardinality`

This section formalizes the finite activity model, feasibility of selected
activity lists, finish-time ordering, the executable earliest-finish selector,
and the recursive greedy selector.  On finish-time-sorted inputs,
`greedySelect` is proved to return a feasible sublist with maximum cardinality
among all feasible sublists of the input.  Lower-level array/pseudocode
execution refinement remains outside this finite-list theorem statement.

## Section 16.3 - Huffman Codes

- Lean source: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`
- Status: `proved`
- Main theorem: `HuffmanV2.optimum_huffman_freqs`

This is currently the strongest completed CLRS-style case study in the project.
The proof uses a split-leaf exchange argument:

1. merge the two least frequent symbols;
2. use the inductive optimum for the merged instance;
3. split the merged leaf back into the two original leaves;
4. show no competing tree can have smaller cost.

The public interface is frequency-table based, so users do not need to interact
with the internal forest proof.
