# Chapter 16 - Greedy Algorithms

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
