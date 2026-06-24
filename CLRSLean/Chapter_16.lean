import CLRSLean.Chapter_16.Section_16_1_Activity_Selection
import CLRSLean.Chapter_16.Section_16_3_Huffman_Codes

/-!
# Chapter 16 - Greedy Algorithms

The current Chapter 16 site contains two greedy-algorithm tracks.  Section 16.1
records a certificate-based activity-selection proof skeleton, while Section
16.3 is the project's strongest completed greedy-algorithm case study.

## Sections

* 16.1 Activity selection: {lit}`partial`.
  Main results: {name}`CLRS.ActivitySelection.earliest_finish_minFinish` and
  {name}`CLRS.ActivitySelection.greedy_choice_optimal_from_certificate`.
* 16.3 Huffman codes: {lit}`proved`.
  Main result: {name}`CLRS.HuffmanV2.optimum_huffman_freqs`.

## Proof Theme

Both sections expose the same high-level CLRS pattern: make a greedy choice,
turn the textbook exchange argument into a reusable certificate, then compose it
with the recursive subproblem.

For Huffman, the key move is a split-leaf transformation:

```
merge the two least frequent symbols
-> use the inductive optimum for the merged instance
-> split the merged leaf back into the two original leaves
-> compare costs against every competing tree
```

The final public theorem is stated over a frequency table.  Readers do not need
to work with the internal forest invariant unless they want to inspect the proof
machinery.

## Why This Page Matters

Huffman is a useful benchmark for CLRSLean because it proves true optimality,
not only functional correctness.  Activity selection is the lighter companion:
it already has the finite-list model, executable greedy selectors, and the
certificate theorem; the remaining strengthening is to derive the certificate
automatically from a finish-time-sorted input interface.
-/
