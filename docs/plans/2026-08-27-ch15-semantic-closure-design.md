# Chapter 15 semantic-closure design

## Goal

Close the eleven MINOR findings in the Chapter 15 semantic-fidelity audit while
keeping the large existing proofs stable.  New textbook-facing statements live
in small companion modules and reuse the established correctness theorems.

## Module boundaries

- `Section_15_1_Activity_Selection/TextbookModel.lean`
  adds the textbook `start < finish` input predicate and subtype without
  changing the more general core model.
- `Section_15_1_Activity_Selection/Iterative.lean`
  implements the one-pass iterative selector, proves equivalence with the
  recursive selector on finish-sorted inputs, and gives an exact linear scan
  count.
- `Section_15_2_Greedy_Meta.lean`
  keeps the generic solver but gives the greedy-choice and optimal-substructure
  properties separate, solver-independent meanings.
- `Section_15_2_Greedy_Meta/ActivitySelection.lean`
  instantiates the generic greedy framework with finish-sorted activity lists.
- `Section_15_3_Huffman_Codes/TextbookCost.lean`
  defines equation (15.4) and proves it equal to the internal-node cost already
  used by the optimality development.
- `Section_15_3_Huffman_Codes/TextbookLemmas.lean`
  exposes named interfaces corresponding to Lemmas 15.2 and 15.3.
- `Section_15_3_Huffman_Codes/Complexity.lean`
  states and proves the list implementation's quadratic work bound and the
  textbook heap implementation's operation-accounting bound.
- `Section_15_4_Offline_Caching/EmptyStart.lean`
  closes the empty-cache boundary for the current cache semantics and clearly
  separates it from a capacity-aware warm-up model.

The Chapter 15 facade imports the companions, so existing imports remain valid
and no large source file must be recompiled while an individual companion is
being developed.

## Acceptance criteria

1. Every new public theorem has a focused compile test.
2. The Chapter 15 trust surface reports only the standard Lean axioms already
   accepted by the project.
3. The semantic audit contains no unresolved Chapter 15 MINOR finding; any
   deliberately different executable cost model is documented with a proved
   bridge or bound.
4. Each coherent section is committed separately before final Chapter 15
   documentation and progress metadata are updated.

