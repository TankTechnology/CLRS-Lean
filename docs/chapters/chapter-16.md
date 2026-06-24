# Chapter 16 - Greedy Algorithms

## Section 16.1 - Activity Selection

- Lean source: `CLRSLean/Chapter_16/Section_16_1_Activity_Selection.lean`
- Status: `partial`
- Main theorems:
  - `CLRS.ActivitySelection.earliest_finish_minFinish`
  - `CLRS.ActivitySelection.finishSorted_head_minFinish`
  - `CLRS.ActivitySelection.greedySelect_sublist`
  - `CLRS.ActivitySelection.greedySelect_feasible`
  - `CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`

This section formalizes the finite activity model, feasibility of selected
activity lists, finish-time ordering, the executable earliest-finish selector,
and the recursive greedy selector's sublist and feasibility properties.  The
remaining textbook strengthening is to derive the exchange certificate
automatically and connect it to the full recursive `greedySelect`
maximum-cardinality theorem.

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
