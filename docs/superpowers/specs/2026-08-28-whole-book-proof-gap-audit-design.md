# Whole-Book Proof-Gap Audit

## Goal

Reassess all 35 fourth-edition chapters against their main textbook proof
obligations, distinguish genuine semantic gaps from deliberately excluded
machine-level refinements, and turn every genuine gap into a concrete Lean
closure target.

The audit does not replace the existing selected-theorem ledger.  It explains
what that ledger proves, checks that the selected boundary has not hidden a
central textbook obligation, and records any remaining work in GitHub issues
rather than creating another permanent live status database.

## Why the existing completion count is insufficient

The repository currently reports 1,668 of 1,668 selected theorem entries.  The
count is useful, but it is relative to the declarations already selected for
tracking.  It cannot by itself establish that:

- the executable algorithm is the same algorithm whose specification is
  proved;
- a textbook invariant is preserved rather than made definitional by a simpler
  model;
- a cost theorem is attached to the execution whose value is proved correct;
- a probability formula is derived from an explicit sample space rather than
  introduced as the model; or
- reader-facing prose still agrees with the current source.

The initial evidence pass already found two concrete contradictions that the
current repository checks accept:

- Chapter 31 tracks 18 theorem groups, while `completion_read` says 17 and the
  notes claim Sections 31.1--31.9 although canonical fourth-edition coverage is
  Sections 31.1--31.8.
- Chapter 32's Rabin--Karp source says the rolling recurrence is a named gap,
  although `hash_slide`, the rolling matcher, its correctness theorem, and its
  deterministic cost bounds are present and trust-audited.

It also found two high-confidence semantic-bridge candidates:

- Chapter 2 proves a local executable and costed `MERGE`, but its public
  `mergeSort` delegates to Mathlib's `List.mergeSort`; no theorem connects the
  recursive top-level execution to the local `MERGE` implementation.
- Chapter 11 defines the uniform-hashing probe-tail product and proves the CLRS
  expectation bounds from it, but does not derive that product from an explicit
  uniformly random permutation of table slots.

## Audit contract

Every canonical chapter is evaluated in six independent lanes:

1. **Algorithm semantics** -- the public executable definition follows the
   relevant CLRS control structure, or a refinement theorem connects it to a
   faithful specification.
2. **Correctness and preservation** -- output specification, permutation or
   membership semantics, and all required structural invariants are proved.
3. **Optimality or lower bound** -- exchange, cut, adversary, or lower-bound
   arguments central to the section are present as Lean theorems.
4. **Cost attachment** -- the claimed cost is read from, or proved equal to a
   cost associated with, the same execution whose result is proved correct.
5. **Model provenance** -- probabilistic, graph, numeric, and machine models
   expose the assumptions needed by the textbook theorem and do not make its
   hard conclusion true by definition.
6. **Public evidence** -- chapter guide, interface test, native axiom audit,
   progress row, and edition map agree on the exact boundary.

Each lane receives one of these classifications:

- `proved`: direct named theorem evidence covers the obligation;
- `document-drift`: the proof exists but public prose or metadata contradicts
  it;
- `interface-gap`: the proof exists but is not reachable or pinned through the
  canonical chapter interface;
- `semantic-bridge-gap`: the relevant components exist but their connection is
  not proved;
- `core-proof-gap`: a central textbook theorem, invariant, or execution layer
  is genuinely absent;
- `deferred-implementation`: pointer, mutation, RAM, cache, hardware,
  distributed, or floating-point behavior explicitly outside project scope;
- `future-work`: exercises, chapter problems, and optional strengthenings that
  are not part of the main textbook theorem path.

`deferred-implementation` and `future-work` are not counted as failures of the
mathematical chapter boundary.  A functional analogue is not enough for
`proved` when it bypasses the section's central imperative invariant.

## Evidence hierarchy

The audit uses evidence in this order:

1. theorem statements and executable definitions in canonical source modules;
2. focused interface tests and `Tests/Trust/Chapter_NN.lean`;
3. fourth-edition chapter aggregators and section module documentation;
4. `docs/clrs-proof-progress.csv` and
   `docs/clrs-fourth-edition-map.csv`;
5. dated semantic-audit snapshots and closed GitHub issues.

Later items may help locate work but cannot override contradictory source
evidence.  Absence of `sorry` establishes proof term completeness, not semantic
fidelity.

## Output artifacts

The audit produces one dated immutable report:

`docs/audits/2026-08-28-whole-book-proof-gap-audit.md`

The report contains one row per chapter, with the six lane classifications,
named theorem evidence, exact missing bridge or theorem, severity, and proposed
closure issue.  It ends with a ranked cross-chapter closure queue.

No new live proof-gap CSV is introduced.  Factual status remains in the two
existing CSV ledgers; unresolved proof work lives in GitHub issues.  The dated
report is an evidence snapshot for its commit, consistent with the repository's
current audit policy.

## First closure batches

### Batch 0: consistency gate

- Make the progress validator reject a numeric tracked-theorem claim that
  disagrees with `tracked_key_theorems`.
- Make it reject a prose claim that a fully proved section range includes a
  section outside `represented_sections`.
- Correct the Chapter 31 count/range and the stale Chapter 32 Rabin--Karp gap
  note.

### Batch 1: Chapter 2 executable merge-sort bridge

Define a focused executable top-level merge sort whose recursive combine step
is `CLRS.Chapter02.merge`, then prove:

- its defining split/recursive/merge equation;
- output permutation preservation;
- sortedness under the recursive invariant;
- equality with the existing public sorted result, or an exact shared
  specification theorem;
- a cost record whose merge comparisons and output writes come from
  `mergeWithCost`, followed by the appropriate all-input asymptotic bridge.

This closes a central algorithm-to-combine gap without introducing mutable-array
or RAM semantics.

### Batch 2: Chapter 11 explicit uniform-hashing bridge

Use uniformly distributed permutations of `Fin m` as probe orders.  For a
fixed occupied set of cardinality `n`, prove that the probability that the
first `i` probes are occupied equals the existing without-replacement product
`probeTail m n i`.  Then re-export the unsuccessful, insertion, and successful
probe bounds from the sample-space-derived expectation.

### Later batches

The audit determines whether Chapter 4 arbitrary-input branching trees,
Chapter 18 executable/specification shape refinement, Chapter 21 stateful
union-find/Kruskal integration, or other candidates are genuine main-path gaps.
Only high-confidence findings become proof issues; stale documentation is
repaired directly, and low-level scope exclusions remain optional issues.

## Verification and submission policy

Every proof batch follows a red-green public-interface loop and is committed as
an independently checkable stage.  Development uses focused `lake env lean` or
module builds; the full chapter or repository build is reserved for the final
integration gate.

Required final evidence for each batch:

- focused source elaboration;
- public interface test;
- chapter trust/axiom audit;
- placeholder scan;
- `python3 scripts/check_repository.py`;
- `git diff --check`;
- a full `lake build CLRSLean` before merging the complete batch.

Website generation and deployment are not part of this proof audit.
