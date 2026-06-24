# CLRS Chapter Formalization Skill Iteration Log

This log records concrete updates to
`.codex/skills/clrs-chapter-formalization/SKILL.md` after using it on CLRS-Lean
chapters.

## 2026-06-24 - Initial Skill

- Added the chapter loop: triage, Lean-friendly model choice, theorem interface,
  implementation, site wiring, verification, and post-chapter refinement.
- Added early chapter patterns for functional data structures, lookup tables,
  search trees, and balanced trees.
- Added honesty rules to prevent non-compiler-clean exploration files from being
  presented as finished proofs.

## 2026-06-24 - After Chapter 10

- Added a linked-list pattern: when no imperative memory semantics exists, prove
  search soundness, front-insert membership, and delete-all membership
  characterizations over `List`.
- Confirmed that Chapter 10 can be `proved` only for the functional model;
  pointer updates, free lists, and allocation remain outside the proved status.

## 2026-06-24 - After Chapter 11

- Added a hash-table performance pattern: prove deterministic table-update and
  bucket-search correctness first; keep simple-uniform-hashing expected-time
  theorems separate until a probability model is selected.
- Confirmed that direct addressing is small enough to mark `proved` for the
  functional table model, while chained hashing is currently `partial` because
  the average-case analysis is not formalized.

## 2026-06-24 - After Chapter 12

- Strengthened the tree-chapter pattern: first prove
  `membership after insert ↔ inserted key or old membership`, then use that
  equivalence for upper/lower-bound preservation and the ordered invariant.
- Cleaned unused `simp` arguments after the first successful build; this keeps
  new theorem files quieter without expanding proof scope.
- Added the next tree-layer lesson: when parent pointers are not modeled yet,
  still prove functional successor/predecessor as least-greater/greatest-less
  queries over the ordered tree.  This removes a real textbook gap without
  pretending that pointer-level `TREE-SUCCESSOR` is already verified.
- Added the deletion lesson: once the pure tree model has extremal-key bounds,
  prove `deleteMin`, `deleteRoot`, membership-after-delete, and
  ordering-preservation theorems before deferring pointer-level transplant.

## 2026-06-24 - After Chapter 13

- Strengthened the balanced-tree pattern: prove rotation membership preservation
  and root-recoloring local invariant lemmas before attempting executable
  red-black insertion or deletion.
- Added a warning from practice: doc comments should use `{lit}` for future
  theorem names or textbook pseudocode names; `{name}` should be reserved for
  names that already exist at that point in the file.

## 2026-06-24 - After Chapter 4 Recurrence Layer

- Added a divide-and-conquer recurrence pattern: proof-method sections should
  become small public theorem templates, not just prose.  Section 4.3 now proves
  substitution upper/lower/sandwich principles plus linear and geometric
  templates; Section 4.4 now proves finite recursion-tree unrolling and
  envelope bounds.
- Refined the status rule for Chapter 4: keep maximum subarray, Strassen, and
  the all-input Master Theorem extension as future work, but do not list
  recurrence-method infrastructure as future work once compiler-clean theorem
  templates exist.

## 2026-06-24 - After Chapter 4.1 Maximum Subarray

- Added a divide-and-conquer selection-problem pattern: prove a clean exhaustive
  finite-search specification before proving the textbook optimized
  implementation.
- For maximum subarray, the useful first theorem is not runtime analysis; it is
  candidate-enumerator exactness plus finite argmax optimality.  The CLRS
  divide-and-conquer pseudocode can now be treated as a refinement target.

## 2026-06-24 - After Chapter 16.1 Activity Selection Executable Layer

- Added a greedy-recursion pattern: first prove sorted-order facts for the
  greedy choice, then prove executable recursion invariants such as sublist and
  feasibility, and only then attack the exchange-certificate optimality layer.
- For activity selection, `greedySelect` should not remain a bare definition
  while the maximum-cardinality proof is pending.  Its sublist and feasibility
  theorems are useful public progress and expose the remaining gap precisely.

## 2026-06-24 - Complete Chapter Proof Workflow

- Upgraded the skill from a general chapter loop to a complete-chapter workflow:
  enumerate every section, choose a best current theorem for each, prove
  tractable targets before deferring, wire the site, and verify both Lean and
  literate HTML.
- Added explicit stop conditions: a chapter pass is not complete while a section
  has only prose, while a useful theorem can be stated and proved now, or while
  a blocker does not name the missing definition, lemma, or representation.
- Added an autonomy rule: when remaining proof targets are tractable, continue
  to the next section instead of waiting for another prompt.
