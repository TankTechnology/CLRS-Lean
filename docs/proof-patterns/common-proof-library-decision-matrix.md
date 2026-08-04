# Common Proof Library Decision Matrix

This matrix records where reusable proof principles canonically live, which
parts of their public API are compatibility surfaces, and how they affect
progress accounting.  Its purpose is to prevent two opposite mistakes:
reproving generic algebra in every chapter, and moving chapter semantics into
an abstraction before there is real reuse pressure.

## Ownership Matrix

| Proof principle | Canonical owner | Current consumers | Compatibility surface | Progress treatment | Condition for further extraction | State |
| --- | --- | --- | --- | --- | --- | --- |
| Finite uniform expectation algebra | `CLRS.Probability` in `Probability/FiniteExpectation.lean` | Chapters 5, 8, and 11 | Chapter 5 keeps its established `fintypeExpect_mono`; Chapter 11 keeps `fintypeExpect_mono` and `fintypeExpect_neg`, all with unchanged theorem types | Count the common algebra once; chapter wrappers and aliases add zero groups | Add algebra here when it is independent of a chapter's probability model | Active domain library |
| Exact-power to all-input recurrence transfer | `CLRS.Chapter04` in Section 4.6 | Chapters 4 and 27 | Chapter 27 keeps six cost-specific sandwich and all-input results | Shared transfer lemmas add no repeated Chapter 27 counts; distinct CLRS cost conclusions remain textbook groups | Move outside Chapter 4 only if a non-recurrence domain needs the same API and Chapter 4 becomes an invalid dependency | Active domain library |
| Potential-method telescope | `CLRS.Chapter17` amortized framework | Chapters 17, 19, and 21 | Consuming chapters retain their data-structure potentials and operation theorems | Count the framework once and each distinct textbook amortized-analysis obligation once | Move only if Chapter 17 ownership creates a real dependency cycle | Active domain library |
| Key fibers | `CLRS.ProofPatterns.Fiber` | Chapter 8 counting/radix/bucket developments; future hash-chain candidates | `CLRS.Chapter08.bucket` and all established `bucket_*` names remain public through `bucket_eq_fiber` | The exact bridge and delegated wrappers add zero groups | Enlarge the generic API only after a second independent consumer needs the same missing lemma | Active geometric pattern |
| Natural intervals | `CLRS.ProofPatterns.Interval` | Chapter 22 DFS timestamp intervals | DFS keeps `finishesBeforeDiscovered`, `intervalNestedInside`, and its theorem vocabulary | Projection and equivalence bridges add zero groups; the DFS parenthesis theorem remains a textbook group | Add relations only when another timestamp/index proof needs them | Active geometric pattern |
| Boundary traces | `CLRS.ProofPatterns.Boundary` | No chapter imports it yet | Existing loop invariants stay chapter-local | No count until it discharges a real proof obligation; adapters never count | Adopt when a loop trace matches the state/index interface without losing algorithm-specific hypotheses | Deferred pedagogical pattern |
| Exchange certificates | `CLRS.ProofPatterns.Exchange` | No chapter imports it yet | Activity selection, Huffman, and MST keep their local witnesses | No count until the generic certificate owns a reused proof; adapters never count | Adopt only when two consumers can use one witness shape without classical-choice packaging | Deferred pedagogical pattern |
| Local tree/heap surgery | Chapter-local lemmas; atlas entry only | Red-black trees, order-statistic trees, B-trees, heaps | All invariant-preservation statements remain local | Count distinct textbook invariant obligations, not a proposed frame abstraction | Extract after two data structures share an exact frame-preservation interface | Atlas only |
| DP table/grid geometry | Chapter-local recurrence and reconstruction layers; atlas entry only | Matrix chain, LCS, rod cutting, optimal BST | Problem-specific certificates remain local | Count textbook recurrences/correctness groups | Extract only after value, dependency, and reconstruction interfaces genuinely coincide | Atlas only |

## Theorem-Group Counting Policy

Progress measures textbook-facing proof obligations, not the number of public
Lean declarations.

- A canonical shared theorem is counted once at its owner.
- A compatibility wrapper, alias, namespace forward, or exact representation
  bridge adds no theorem group.
- Repeated applications of one shared principle add no infrastructure count.
- A consuming chapter may still count a result when it states a distinct CLRS
  obligation about that chapter's algorithm or cost model.
- Several structurally identical chapter instances may be recorded as one
  theorem group when the textbook treats them as one argument family.
- `docs/proof-map.md` may list every useful declaration for discovery, while
  `docs/clrs-proof-progress.csv` records only theorem groups.

This policy is prospective for new edits.  It does not silently rewrite the
historical total currently recorded by the progress ledger; normalizing that
total requires a separate repository-wide audit with an explicit migration
record.

## Promotion Checklist

Before moving a local lemma into shared infrastructure, verify all of the
following:

1. At least two real proof sites need the same mathematical statement, or an
   existing generic module has a concrete consumer and the change is an exact
   bridge.
2. The proposed owner can be imported without a dependency cycle.
3. Chapter-specific definitions do not leak into the generic theorem.
4. Existing public theorem types can remain unchanged through a small wrapper.
5. The shared theorem replaces proof work rather than merely adding another
   name.
6. The progress ledger will not increase for helpers, bridges, or wrappers.

When any item fails, keep the lemma local and record the proof shape in the
atlas instead.
