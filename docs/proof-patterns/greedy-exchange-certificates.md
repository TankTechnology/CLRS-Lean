# Greedy Exchange Certificates

This note records the public proof pattern used by the Chapter 16 greedy
algorithm formalizations.

## Shape

The generic Lean skeleton is `CLRS.ProofPatterns.ExchangeCertificate` in
`CLRSLean/ProofPatterns/Exchange.lean`.  Chapter-specific proofs should still
define their own certificate fields when needed, then expose a small bridge to
the generic shape once the same exchange move appears in another chapter.

1. State the recursive greedy algorithm on a small functional model.
2. Identify the greedy choice and the post-greedy subproblem.
3. Package the exchange argument as a certificate theorem.
4. Prove the recursive subproblem optimum.
5. Consume the certificate to lift the subproblem optimum back to the original
   problem.
6. Expose a direct theorem interface for readers who do not need the certificate.

## Activity Selection

`GreedyChoiceCertificate` says that every feasible competitor for the current
activity list can be exchanged into one that starts with the chosen activity and
then uses only the filtered tail subproblem.

The proof then has two layers:

- `greedy_choice_optimal_from_certificate` is the reusable exchange step.
- `finishSorted_greedyChoiceCertificate` builds the certificate automatically
  from finish-time order.

The final interface is:

- `greedySelect_cons_eq`
- `greedySelect_after_maxCardinality`
- `greedySelect_cons_maxCardinality`
- `greedySelect_maxCardinality`
- `greedySelect_optimal_length`
- `greedySelect_cons_recursive_correct`
- `activitySelection_cons_recursive_correct`
- `activitySelection_cons_correct`
- `activitySelection_correct`

## Huffman Codes

Huffman uses the same certificate style at a larger scale.  The long tree
exchange proof is hidden behind `SplitLeafOptimalitySpec` and
`split_leaf_preserves_optimum`.  The bundled forest proof then repeatedly
merges the two cheapest trees, applies the recursive optimum, and splits the
merged leaf back into the two original symbols.

The final interface is frequency-table based:

- `CLRS.HuffmanV2.optimum_huffman_freqs`
- `CLRS.HuffmanV2.huffmanOfFreqs_correct`
- `CLRS.HuffmanV2.huffmanOfFreqs_cost_le`

This keeps the proof inspectable while letting readers use the theorem without
touching the internal forest invariant.  The `huffmanOfFreqs_cost_le` theorem
is the most direct textbook-style form: every consistent tree with the same
frequency table has cost at least the Huffman output.
