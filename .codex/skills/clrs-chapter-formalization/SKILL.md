---
name: clrs-chapter-formalization
description: Use this skill whenever working on CLRSLean chapter-scale Lean formalization, especially when the user asks to complete, extend, audit, or organize an entire CLRS chapter or a sequence of chapters. This skill guides chapter triage, Lean-friendly model selection, theorem interface design, proof implementation, status ledger updates, site wiring, verification, and post-chapter skill refinement.
---

# CLRS Chapter Formalization

Use this skill to turn a CLRS chapter into a maintainable, honest, theorem-bearing
Lean development inside CLRSLean.

The goal is not to pretend that every textbook sentence has been mechanized in
one pass.  The goal is to create a chapter track that compiles, exposes useful
public theorem names, states remaining gaps explicitly, and can be deepened
without redoing the site structure.

## Chapter Loop

For each chapter, run this loop in order:

1. **Read the local project contract**
   - Read `CLAUDE.md`, `CLRSLean.lean`, `literate.toml`, `CLRSLean/Status.lean`,
     and `docs/proof-map.md`.
   - Inspect nearby chapter files for naming, namespace, and proof style.

2. **Triage the CLRS chapter**
   - Identify the main textbook claims and the data structures or algorithms.
   - Classify each target as one of:
     - `proved`: can be proved now for the current Lean model;
     - `partial`: useful theorem infrastructure can compile now, but the full
       textbook theorem needs more representation work;
     - `blocked-design`: the proof depends on choosing a representation such as
       heaps, arrays, probability spaces, tree rotations, or finite paths;
     - `deferred-implementation`: an executable implementation proof is useful
       but not needed for the mathematical theorem.

3. **Choose a Lean-friendly first model**
   - Prefer pure inductive/list/Finset models before imperative arrays.
   - For data-structure chapters, separate the mathematical interface from
     executable refinement:
     - Chapter 10: functional stacks, queues, lists, and trees before pointers.
     - Chapter 11: direct-address or abstract hash interfaces before RAM tables.
     - Chapter 12: inductive BSTs before pointer-based tree mutation.
     - Chapter 13: colored-tree invariants and local transformations before
       full red-black insertion/deletion.
   - Make the limitation visible in the section docstring.

4. **Write the public theorem interface first**
   - Pick theorem names that read like CLRS claims.
   - Make statements strong enough to be useful but small enough to prove.
   - Prefer several small theorems over one massive theorem with opaque
     hypotheses.
   - Do not introduce `sorry` in a theorem that will be listed as `proved`.

5. **Implement and prove incrementally**
   - Add the chapter guide file `CLRSLean/Chapter_NN.lean`.
   - Add section files under `CLRSLean/Chapter_NN/`.
   - Keep each file focused: definitions, local lemmas, public theorem block.
   - After each file, run `lake build CLRSLean.Chapter_NN...`.
   - If a proof fails, reduce the theorem statement or expose the missing
     certificate rather than smuggling in an unproved theorem.

6. **Wire the book**
   - Import the chapter from `CLRSLean.lean`.
   - Add chapter and section ordering/titles to `literate.toml`.
   - Update `CLRSLean/Status.lean`, `docs/proof-map.md`, and `docs/index.md`.
   - If the chapter is partial, the exact gap must appear in both the Lean
     status page and the proof map.

7. **Verify**
   - Run `lake build`.
   - For site-visible changes, run `lake build :literateHtml`.
   - If static HTML size matters, run `scripts/optimize_literate_html.py` on a
     temporary copy and inspect large pages.
   - Record warnings as warnings; do not call a chapter complete because a
     different command passed.

8. **Refine this skill after the chapter**
   - Add one concrete lesson learned to the skill or to the iteration log.
   - If the chapter exposed a new reusable pattern, add it to "Chapter Patterns".
   - If the chapter showed a recurring blocker, add it to "Known Blockers".

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
  hash function; only introduce probability once the deterministic interface is
  stable.
- **Tree chapters:** use inductive trees, an `InTree` predicate, an `Ordered`
  invariant, and theorem names for insertion membership and invariant
  preservation.  Prove a membership-after-insert equivalence before proving
  ordering preservation; it turns bound-preservation lemmas into short
  case splits.
- **Balanced-tree chapters:** begin with invariants that can be checked locally:
  node color, no red-red edge, black height, and local rotations.  Full
  insertion/deletion should be marked partial until the balancing algorithm is
  mechanized.  Prove rotation membership preservation before attempting
  invariant preservation for fixup algorithms.

## Known Blockers

- Full RAM semantics and pointer mutation are project-level future work.
- Red-black tree insertion and deletion need a careful balancing representation;
  do not list them as `proved` until Lean proves the executable algorithm
  preserves red-black invariants.
- Hash-table expected-time proofs require a probability model.  Direct-address
  and deterministic collision-chain correctness can be proved before that.
- Chapter-end exercises and Problems belong to a second track after the main
  chapter interface is stable.

## Honesty Rules

- A `proved` status requires a named Lean theorem that compiles without `sorry`.
- A section can be valuable while `partial`; make the boundary precise.
- Never import a non-compiler-clean exploration file into `CLRSLean.lean`.
- Prefer a smaller theorem that compiles over a grand theorem with hidden
  assumptions.
