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

## 2026-06-24 - After Chapter 4.1 Crossing Helper

- For maximum subarray, the next useful divide-and-conquer layer after the
  exhaustive specification is the crossing helper, not the whole recursive
  algorithm at once.  Define nonempty suffixes, crossing candidates as
  suffix-left plus prefix-right, prove the crossing enumerator exact, and reuse
  the finite argmax selector for `maxCrossingSubarray_correct`.
- After the crossing helper, prove the split-combine interface before writing
  the executable recursion: every nonempty subarray of `left ++ right` is either
  left-only, right-only, or crossing, and a candidate that dominates those three
  cases dominates the whole append.  This leaves a sharper remaining target:
  define the executable recursive selector and prove it against the combine
  theorem.

## 2026-06-24 - After Chapter 4.1 Executable Combine Step

- After proving a case-split interface, immediately add the executable
  one-step combiner when it is small: for maximum subarray, selecting among
  `maxSubarray left`, `maxSubarray right`, and `maxCrossingSubarray left right`
  gave a compact theorem, `maxSubarrayDivideStep_correct`.
- This is the right checkpoint before full recursion: the remaining selector
  proof can focus on termination/splitting, while the local optimality argument
  is already sealed.

## 2026-06-24 - After Chapter 4.1 Recursive Selector

- Once the one-step combiner is proved, introduce a small result predicate for
  optional maximum-subarray selectors and prove that the combiner preserves it.
  This lets the recursive proof become a direct structural induction over a
  split tree instead of replaying local optimality at every node.
- For list divide-and-conquer algorithms, an explicit split tree plus a fuelled
  splitter is a good intermediate model: it gives an executable selector and a
  clean correctness theorem while leaving runtime recurrence/RAM semantics as a
  separate strengthening target.

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

## 2026-06-24 - After Chapter 3.2 Factorial Growth

- Added a factorial-table bridge pattern: first expose simple concrete bounds
  such as an offset lower bound and a half-scale lower bound, then wrap Mathlib
  limit theorems such as `tendsto_factorial_div_pow_self_atTop` as CLRS-facing
  `little-o` statements.
- When Mathlib already has a sharper theorem than the local proof, replace long
  arithmetic induction with the library lemma and keep the section's theorem
  name as the reader-facing interface.
- For half-scale floor/ceiling growth, prove the natural arithmetic facts once
  with `Nat.div_add_mod` plus `omega`, then expose only the CLRS-facing
  Θ wrappers as public theorem names.

## 2026-06-24 - After Chapter 5 Expected-Hires Asymptotics

- Added a downstream-wrapper pattern: when one section proves an exact closed
  form and another section proves the closed form's asymptotics, add the
  section-level Θ theorem instead of keeping a "connect these" future-work item.
- For Chapter 5, the bridge is `expectedHires = harmonic`, the equality between
  the section's real harmonic sum and Mathlib's harmonic numbers, and
  Chapter 3.2's `CLRS.Chapter03.isBigTheta_harmonic_log`.

## 2026-06-24 - After Chapter 23.2 Sorted Lightness

- For Kruskal, do not keep the entire sorted-order argument hidden behind a
  safe-edge certificate.  Prove a small public theorem: sorted edge order plus a
  processed-prefix exclusion invariant implies the current edge is light across
  the component cut.
- This makes the remaining MST gap sharper: the next theorem should derive the
  processed-prefix exclusion invariant from an exact component/cycle-test model,
  while union-find implementation correctness can remain deferred.

## 2026-06-24 - After Chapter 23.2 Exact Components

- Once exact components are available, prove prefix accounting over the actual
  Kruskal recursion.  Each processed edge is either still selected in the
  current forest or has endpoints connected by that forest.
- Use that accounting theorem to derive processed-prefix exclusion instead of
  keeping it as a caller-supplied hypothesis.  The sorted-order theorem remains
  useful, but exact-component Kruskal should expose a stronger wrapper:
  `cut_certificate_of_exact_component_kruskal_prefix`.
- After this pass, the honest MST frontier is concrete path/cycle exchange,
  final-tree construction, and optional union-find refinement.

## 2026-06-25 - After Chapter 23.2 Complete-Scan Spanning

- Do not keep the whole final-tree obligation as one opaque hypothesis once the
  exact-component accounting theorem exists.  First prove the two structural
  parts that follow directly from a complete scan: the output contains only graph
  edges, and every original graph edge has endpoints connected in the output.
- A reusable path-transport lemma is the right bridge: if every edge of one
  edge set has endpoints connected in another, then every path over the first
  edge set transports to the second.  This turns graph connectedness over
  `G.edges` into Kruskal-output spanning.
- After this pass, the remaining final-tree target is specifically forest
  preservation for the component cycle test, plus the separate concrete
  path/cycle exchange edge.

## 2026-06-25 - After Chapter 23.2 Forest Preservation

- For custom graph connectivity based on `Relation.ReflTransGen`, prove a
  one-edge insertion splitting lemma before proving forest preservation.  The
  useful public shape is `Graph.connected_insert_edge_cases`: a path after
  inserting edge `e` either already exists in the old edge set or bridges
  through the endpoints of `e`.
- With that lemma, `FiniteGraph.isForest_insert_of_not_connected` is a compact
  proof: if removing an old edge yields a path only because it used the inserted
  edge, then the old edge plus the two old path fragments connect the inserted
  edge's endpoints, contradicting the accept condition.
- After this pass, the complete exact-component Kruskal final-tree obligation is
  proved from an initial forest.  The remaining Kruskal proof targets are the
  concrete tree-exchange edge and a recursive wrapper that uses the
  prefix-local sorted-lightness certificate instead of a global lightness
  hypothesis.

## 2026-06-25 - After Chapter 6 Functional Heaps

- For implementation-heavy chapters, a first theorem-bearing pass should expose
  an abstract functional interface instead of blocking on RAM arrays.  In
  Chapter 6, descending lists give a compact max-heap invariant and make
  heapsort correctness a clean `List.Pairwise.reverse` theorem.
- Keep operation specifications multiset-oriented with `List.Perm`: insertion
  adds one key, heap construction preserves the input, key increase is a rebuild
  of `new :: h.erase old`, and deletion is a rebuild of `h.erase key`.
- Record the array `MAX-HEAPIFY`/in-place heapsort layer as a refinement target,
  not as an unproved theorem hidden inside the functional model.

## 2026-07-15 - After Chapter 9 Selection Closure

- A path-only cost counter is not an end-to-end divide-and-conquer cost when
  pivot construction is itself recursive.  Define the nested pivot charge and
  the selected strict-branch charge in the same operational cost semantics.
- Strengthen the cost induction with both pivot fuel and selector fuel.  This
  makes the group-median recursive call and the outer strict-branch call
  available from one strong induction on input length.
- For fresh randomized recursion, define expectation at the current state and
  average anew over `Fin n` at every recursive call.  Rank certificates then
  give the pointwise bridge from the actual chosen continuation to
  `max i (n - 1 - i)`, avoiding a fake fixed-index random model.
