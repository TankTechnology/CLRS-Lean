---
name: clrs-chapter-formalization
description: Use when working on CLRS-Lean chapter-scale Lean formalization, especially when asked to complete, extend, audit, organize, or plan an entire CLRS chapter or a sequence of chapters.
---

# CLRS Chapter Formalization

Use this skill to turn a CLRS chapter into a maintainable, honest,
theorem-bearing Lean development inside CLRS-Lean.

Core principle: prove as much of the chapter as the current representation can
honestly support.  Do not stop at a proof map when a meaningful Lean theorem can
be stated and proved now.

## Complete-Chapter Workflow

For each chapter, run this loop in order:

1. **Read the local project contract**
   - Read `CLRSLean.lean`, `literate.toml`, `CLRSLean/Status.lean`,
     `docs/proof-map.md`, and the relevant `CLRSLean/Chapter_NN.lean`.
   - Inspect nearby chapter files for naming, namespace, and proof style.

2. **Build a full section inventory**
   - Enumerate every textbook section in the chapter, not only the obvious one.
   - For each section, record: main algorithm/data structure, theorem-like
     textbook claims, proof method, likely Lean model, and status.
   - Do not mark a section `future-work` merely because it is hard.  First ask:
     "Is there a smaller theorem, abstract model, certificate interface, or
     proof-method lemma that can compile now?"

3. **Choose Lean-friendly first models**
   - Prefer pure inductive/list/Finset models before imperative arrays.
   - Prefer mathematical correctness and proof-method theorems before RAM
     semantics, pointer mutation, or low-level performance refinement.
   - For data-structure chapters, separate the mathematical interface from
     executable refinement:
     - Chapter 10: functional stacks, queues, lists, and trees before pointers.
     - Chapter 11: direct-address or abstract hash interfaces before RAM tables.
     - Chapter 12: inductive BSTs before pointer-based tree mutation.
     - Chapter 13: colored-tree invariants and local transformations before
       full red-black insertion/deletion.
   - Make the limitation visible in the section docstring.

4. **Plan proof order**
   - Start with sections whose definitions unlock later sections.
   - Prove proof-method infrastructure before concrete algorithm instances when
     that reduces duplicated work.
   - For each section, define a "best current theorem": the strongest useful
     theorem that should compile without hidden assumptions.

5. **Write the public theorem interface first**
   - Pick theorem names that read like CLRS claims.
   - Make statements strong enough to be useful but small enough to prove.
   - Prefer several small theorems over one massive theorem with opaque
     hypotheses.
   - If exploration needs `sorry`, keep it out of imported chapter files and do
     not list it as `proved`.

6. **Implement and prove section by section**
   - Add the chapter guide file `CLRSLean/Chapter_NN.lean`.
   - Add section files under `CLRSLean/Chapter_NN/`.
   - Keep each file focused: definitions, local lemmas, public theorem block.
   - After each file, run `lake build CLRSLean.Chapter_NN...`.
   - If a proof fails, try at least one of these before deferring:
     - strengthen or expose an invariant;
     - split the theorem into reusable lemmas;
     - use a certificate/interface hypothesis for the missing textbook step;
     - prove a simpler but still useful theorem for the current model.

7. **Wire the book**
   - Import the chapter from `CLRSLean.lean`.
   - Add chapter and section ordering/titles to `literate.toml`.
   - Update `CLRSLean/Status.lean`, `docs/proof-map.md`, and `docs/index.md`.
   - If the chapter is partial, the exact gap must appear in both the Lean
     status page and the proof map.

8. **Verify**
   - Search for accidental unfinished proof markers in theorem-bearing Lean
     files:
     `rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_NN -g '*.lean'`.
   - Run `git diff --check`.
   - Run `lake build`.
   - For site-visible changes, run `lake build :literateHtml`.
   - If static HTML size matters, run `scripts/optimize_literate_html.py` on a
     temporary copy and inspect large pages.
   - Record warnings as warnings; do not call a chapter complete because a
     different command passed.

9. **Refine this skill after the chapter**
   - Add one concrete lesson learned to the skill or to the iteration log.
   - If the chapter exposed a new reusable pattern, add it to "Chapter Patterns".
   - If the chapter showed a recurring blocker, add it to "Known Blockers".

## Stop Conditions

A chapter pass is complete only when every section is accounted for in source
and status docs:

- `proved`: named Lean theorem(s) compile without `sorry`.
- `partial`: useful theorem infrastructure compiles, and the exact missing
  theorem layer is stated in docs.
- `blocked-design`: at least one concrete modeling/proof attempt revealed a
  representation decision that must be made.
- `deferred-implementation`: low-level implementation correctness is not needed
  for the current mathematical theorem.
- `future-work`: exercises, chapter-end Problems, or strengthenings outside the
  main theorem path.

Red flags: stop and continue proving instead of reporting completion if a
section only has prose, a "planned theorem" could be stated today, or a gap says
"hard" without naming the missing definition, lemma, or representation.

## Required File Shape

Each theorem-bearing section must follow this shape:

```lean
import Mathlib

/-!
# CLRS Section NN.M - Title

Short reader-facing explanation.

Main results:

- Theorem {lit}`public_theorem_name`: what it proves.

Current gaps:

- Exact missing representation/proof layer, or "none for this model".
-/

namespace CLRS
namespace ChapterNN

/-! ## Definitions -/

/-- Doc comment. -/
def ...

/-! ## Public theorems -/

/-- Doc comment tying the theorem to CLRS. -/
theorem ...

end ChapterNN
end CLRS
```

## Chapter Patterns

- **Functional stack/queue chapters:** use lists as the initial model.  Prove
  equations such as pop-after-push, FIFO behavior, and size preservation.
- **Linked-list chapters without memory semantics:** model the list by `List`
  and prove search soundness, front-insert membership, and deletion membership
  characterizations.  Keep predecessor/successor pointer updates out of the
  proved status until an imperative memory model exists.
- **Lookup-table chapters:** use association lists or direct-address functions
  as the mathematical model.  Prove lookup-after-insert and unaffected-key
  theorems before adding hashing costs.
- **Hash-table performance chapters:** split deterministic correctness from
  expected-time analysis.  First prove bucket/update/search facts for a fixed
  hash function, including deletion/search-after-delete facts; only introduce
  probability once the deterministic interface is stable.
- **Tree chapters:** use inductive trees, an `InTree` predicate, an `Ordered`
  invariant, and theorem names for insertion membership and invariant
  preservation.  Prove a membership-after-insert equivalence before proving
  ordering preservation; it turns bound-preservation lemmas into short
  case splits.  After insertion, prove search correctness and minimum/maximum
  membership plus bound theorems.  Then prove functional successor/predecessor
  as least-greater/greatest-less queries, and prove functional deletion with
  `deleteMin`, `deleteRoot`, membership-after-delete, and ordering-preservation
  theorems before deferring parent-pointer/transplant refinement; these proofs
  are usually structural recursion over the ordered-tree invariant plus
  extremal-key bounds.
- **Balanced-tree chapters:** begin with invariants that can be checked locally:
  node color, no red-red edge, black height, and local rotations.  Full
  insertion/deletion should be marked partial until the balancing algorithm is
  mechanized.  Prove rotation membership preservation before attempting
  invariant preservation for fixup algorithms, then prove red-red local repair
  certificates that combine rotation, root repainting, black-height balance, and
  the bundled shape invariant.
- **Divide-and-conquer recurrence chapters:** formalize proof methods as small,
  reusable theorem templates before attacking every algorithm.  For the
  substitution method, prove base-plus-step upper/lower/sandwich principles and
  common linear or geometric recurrence bounds.  For recursion trees, prove an
  exact finite-sum unrolling theorem and envelope bounds over level costs, then
  instantiate those results for concrete algorithms.
- **Divide-and-conquer selection problems:** when the textbook implementation is
  harder than the mathematical specification, first prove a clean exhaustive
  finite-search specification.  For maximum subarray, enumerate all nonempty
  contiguous subarrays, prove the enumerator exact, prove finite argmax
  optimality, and then use that theorem as the refinement target for the
  divide-and-conquer pseudocode.
- **Greedy-recursion chapters:** split the proof into three layers before the
  final optimality theorem: sorted-order facts about the greedy choice,
  executable recursion invariants such as sublist and feasibility, and an
  exchange/certificate layer for optimality.  Do not leave executable recursive
  selectors without sublist and feasibility theorems while waiting for the full
  exchange proof.

## Known Blockers

- Full RAM semantics and pointer mutation are project-level future work.
- Floor/ceiling all-input recurrence proofs need explicit monotonicity and
  sandwich lemmas; exact-power proofs alone are not the full theorem.
- Red-black tree insertion and deletion need a careful balancing representation;
  do not list them as `proved` until Lean proves the executable algorithm
  preserves red-black invariants.
- Hash-table expected-time proofs require a probability model.  Direct-address
  and deterministic collision-chain correctness can be proved before that.
- Chapter-end exercises and Problems belong to a second track after the main
  chapter interface is stable.

## Iteration Log

- Chapter 11/12/13 cleanup pass: do not leave deterministic query theorems in
  prose once the functional model exists.  For hash tables, prove an
  insertion-search iff before moving to probability.  For BSTs, prove search
  equivalence and extremal-key bounds before successor/deletion.  For local
  tree transformations, prove both invariant preservation and membership
  preservation so the public interface is complete enough for later algorithms.
- Proof-status audit pass: remove prose that implies imported files may contain
  `sorry`; record unfinished theorem targets in status ledgers instead.  When a
  chapter has several small local invariants, add a bundled predicate/theorem so
  later algorithm proofs have one clear interface rather than scattered facts.
- Chapter 12 successor/predecessor pass: when pointer algorithms are not yet in
  scope, prove the pure functional query theorem anyway: returned successors are
  tree members, strictly greater than the query, and least among greater keys;
  predecessors use the symmetric greatest-less statement.
- Chapter 12 deletion pass: after functional successor/predecessor, prove the
  pure deletion layer instead of leaving it as prose.  Useful public theorems are
  membership-after-delete and ordering preservation; keep only parent-pointer,
  transplant, and pointer mutation as the remaining CLRS refinement layer.
- Chapter 4.1 maximum-subarray pass: do not wait for the divide-and-conquer
  recurrence before proving the core specification.  A finite exhaustive
  selector plus an exact contiguous-subarray enumerator gives a strong public
  theorem and a precise future refinement target.
- Chapter 16.1 activity-selection pass: before proving maximum cardinality,
  prove the finish-sorted head lemma and the executable greedy selector's
  sublist and feasibility invariants.  These are small theorem layers that make
  the remaining exchange-certificate gap much sharper.
- Chapter 11.2 chained-hashing pass: do not leave deletion as prose while
  expected-time analysis is blocked.  A fixed-hash functional model can still
  prove bucket delete, search-after-delete failure, and the full
  `hashSearch_hashDelete_iff` characterization.
- Chapter 13 red-black local-repair pass: after rotation membership and root
  repainting, prove the red-red rotation repair certificates that future
  fixup algorithms need.  Good public theorem targets combine child subtree
  `RedBlackShape` hypotheses, matching black-height assumptions, rotation, and
  repainting the new root black.
- Chapter 3.2 standard-function pass: when a CLRS growth-table entry already
  exists in Mathlib, add a small CLRS-facing wrapper theorem instead of leaving
  it as prose.  Log-vs-polynomial, polynomial-vs-exponential, and
  exponential-base comparisons are good examples of one-lemma bridges that
  materially shrink a `partial` gap.
- Chapter 3.2 harmonic-number pass: use Mathlib convergence/bounds theorems to
  prove CLRS-facing asymptotic wrappers, then update downstream chapter gaps
  that depended on the missing standard-function fact.  In particular, once
  `H_n = Θ(log n)` is proved in Chapter 3.2, Chapter 5's remaining work is the
  expected-hires wrapper, not the harmonic asymptotic itself.

## Honesty Rules

- A `proved` status requires a named Lean theorem that compiles without `sorry`.
- A section can be valuable while `partial`; make the boundary precise.
- Never import a non-compiler-clean exploration file into `CLRSLean.lean`.
- Prefer a smaller theorem that compiles over a grand theorem with hidden
  assumptions.
- Do not wait for the user to ask for the next section when a chapter pass has
  remaining tractable proof targets; move to the next proof target autonomously.
