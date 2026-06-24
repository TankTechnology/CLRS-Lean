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

## 2026-06-24 - After Chapter 11.2 Chained-Hash Deletion

- Strengthened the hash-table pattern: deterministic chaining should cover
  deletion too, not only insertion.  In a fixed-hash functional model, deletion
  is a bucket filter and admits a concise `search-after-delete iff` theorem.
- Keep Section 11.2 `partial` until simple-uniform-hashing expected-time
  analysis exists, but list the deterministic insert/delete/search layer as
  compiler-clean public progress.

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

## 2026-06-24 - After Chapter 13 Red-Red Repair

- Strengthened the balanced-tree pattern again: after membership and repainting
  lemmas, prove local red-red repair certificates.  These should combine
  rotation, repainting the new root black, child subtree `RedBlackShape`
  hypotheses, and black-height equalities.
- Keep the chapter `partial` until executable `RB-INSERT-FIXUP` and
  `RB-DELETE-FIXUP` are mechanized; the repair certificates are supporting
  infrastructure, not the full algorithm.

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

## 2026-06-24 - After Chapter 16.1 Activity Selection Optimality

- Once `greedySelect_sublist` and `greedySelect_feasible` are available, the
  sorted-order exchange certificate is tractable.  The useful lemma shape is:
  if a feasible competitor starts with `first`, and the greedy activity has
  minimum finish time in the sorted candidate list, then the competitor tail is
  a sublist of `activitiesAfter` the greedy activity.
- Keep the explicit certificate theorem as a reusable proof interface, but do
  not leave the section marked `partial` after the public sorted-list theorem
  `greedySelect_maxCardinality` compiles.

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

## 2026-06-24 - After Chapter 3.2 Standard Functions

- Added the standard-function bridge pattern: when Mathlib already proves a
  CLRS growth-table comparison, wrap it with a CLRS-facing theorem name instead
  of keeping the item as prose in a `partial` gap.
- Applied the pattern to log-vs-polynomial, polynomial-vs-exponential, and
  exponential-base comparisons; keep Section 3.2 `partial` only for the
  remaining table entries that still lack CLRS-facing wrappers.

## 2026-06-24 - After Chapter 3.2 Harmonic Growth

- Added a harmonic-number bridge pattern: if Mathlib proves convergence such
  as `H_n - log n → γ`, turn it into CLRS-facing asymptotic equivalence and
  Θ-growth theorems instead of leaving harmonic growth in prose.
- After `CLRS.Chapter03.isBigTheta_harmonic_log`, downstream Chapter 5 status
  should ask for an expected-hires asymptotic wrapper, not for the harmonic
  asymptotic itself.

## 2026-06-24 - After Chapter 5 Expected-Hires Asymptotics

- Added a downstream-wrapper pattern: when one section proves an exact closed
  form and another section proves the closed form's asymptotics, add the
  section-level Θ theorem instead of keeping a "connect these" future-work item.
- For Chapter 5, the bridge is `expectedHires = harmonic`, the equality between
  the section's real harmonic sum and Mathlib's harmonic numbers, and
  Chapter 3.2's `CLRS.Chapter03.isBigTheta_harmonic_log`.
