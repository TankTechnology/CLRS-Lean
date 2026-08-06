# Chapter 30 Wrap-Up Design

**Date:** 2026-08-05

## Goal

Close Chapter 30 as a stable, reader-oriented `main-proof-complete` chapter by
consolidating its proof architecture, headline results, cost conventions,
verification entry points, and reviewed boundary.  The formal theorem surface
is already complete; this pass improves discoverability and records the final
closure decision without changing theorem statements or implementations.

## Current State

Sections 30.1--30.3 are imported by `CLRSLean/Chapter_30.lean` and recorded as
46 proved theorem groups out of 46 tracked groups.  The development covers
polynomial representations, generic DFT algebra, recursive and iterative
radix-2 FFTs, FFT polynomial multiplication, execution-attached work, and a
layered FFT circuit with exact size and depth.  Nine Chapter 30 interface and
closure tests cover the public surface, and the final Milestone 2 audit records
the accepted axiom dependencies and repository verification.

The remaining presentation problem is that the chapter-level proof pipeline
and the distinction between execution work and circuit cost are spread across
the chapter guide, proof map, and audit.  A reader should be able to understand
the main result stack from the canonical Lean chapter guide and then follow a
single completion block to the detailed ledger and tests.

## Chosen Approach

Use the existing Lean chapter guide as the canonical reader entry point.  Do
not add a parallel `docs/chapters/chapter-30.md`, because it would duplicate
reader-facing material and create another synchronization surface.

The wrap-up will make four focused changes:

1. Expand the module documentation in `CLRSLean/Chapter_30.lean`.
2. Add a concise Chapter 30 completion block to `docs/proof-map.md`.
3. Clarify the Chapter 30 row in `docs/proof-status-board.md` so excluded
   implementation and numerical layers are explicitly optional extensions,
   not unfinished core proof groups.
4. Add one reusable Chapter 30 lesson to the iteration log in
   `.codex/skills/clrs-chapter-formalization/SKILL.md`.

## Canonical Chapter Guide

The `CLRSLean/Chapter_30.lean` module comment will present the chapter in this
order:

1. **Proof architecture.**  Explain the dependency chain from fixed polynomial
   representations, through generic DFT and recursive FFT, to iterative stages
   and the stored layered circuit.
2. **Section 30.1 headline results.**  Name the representation round trips,
   interpolation round trip, Horner correctness, and exact schoolbook work.
3. **Section 30.2 headline results.**  Name DFT inversion/convolution,
   recursive FFT correctness, unconditional complex FFT multiplication, and
   the all-input `Theta(n log n)` work results.
4. **Section 30.3 headline results.**  Name bit-reversal semantics, iterative
   equality with recursive FFT and DFT, execution-derived work, network
   evaluation, and exact circuit size/depth.
5. **Cost conventions.**  Keep functional execution and circuit accounting
   visibly separate:
   - recursive/iterative arithmetic work: `2 * k * 2^k`;
   - iterative total work including bit-reversal moves:
     `2^k + 2 * k * 2^k`;
   - circuit butterflies: `k * 2^(k-1)`;
   - primitive gates: `3 * k * 2^(k-1)`;
   - butterfly depth: `k`; and
   - primitive depth: `2 * k`.
6. **Reviewed boundary.**  State that the 46/46 theorem groups close the exact
   generic-arithmetic functional model.  List excluded optional layers without
   presenting them as missing core work.

All theorem references in the module comment will use resolvable Verso name
markup where appropriate.  Imports, namespaces, definitions, theorem
statements, and proofs remain unchanged.

## Maintainer Closure Records

`docs/proof-map.md` will gain a compact completion subsection after the Section
30.3 inventory.  It will record:

- status `main-proof-complete`;
- 46 tracked and 46 proved groups with zero missing core groups;
- the nine Chapter 30 interface and closure test files;
- the Milestone 1 and Milestone 2 audit paths;
- the accepted strong boundary; and
- the statement that exercises, Problems 30-1 through 30-6, mutable arrays,
  machine-level costs, floating-point analysis, concrete scheduling, NTT, and
  code generation are optional new layers.

`docs/proof-status-board.md` will preserve the same theorem coverage but label
its right-hand column as optional extensions rather than a pending Chapter 30
proof queue.  The progress CSV and generated README table already express the
correct 46/46 status and will not be hand-edited.

## Reusable Formalization Lesson

The chapter-formalization iteration log will record this Chapter 30 rule:

- an algorithmic cost theorem should read counters from the same execution
  record whose value is proved correct; and
- a circuit's evaluation, gate count, and depth should recurse over the same
  stored circuit syntax.

This prevents detached closed-form cost functions or descriptive circuit
metadata from being mistaken for verified execution or network bounds.

## Non-Goals

This wrap-up does not:

- change any Lean definition, theorem statement, proof, namespace, or import;
- reorganize or rename Chapter 30 modules;
- add theorem groups or change the 46/46 progress count;
- implement mutable or in-place FFT arrays;
- formalize RAM, cache, allocator, SIMD, GPU, communication, scheduler, or
  processor costs;
- add floating-point approximation or numerical-stability theorems;
- add NTT specialization or external code generation;
- cover exercises or Problems 30-1 through 30-6; or
- build, inspect, prepare, optimize, or deploy the website.

## Verification

The implementation pass will run:

1. `git diff --check`;
2. a direct `sorry`/`admit`/`axiom` scan over Chapter 30;
3. `lake build +CLRSLean.Chapter_30`;
4. all nine `Tests/Chapter_30_*.lean` files;
5. both closure tests, confirming no `sorryAx` or project-defined axiom;
6. `uv run python scripts/check_progress_csv.py`;
7. `uv run python scripts/gen_readme_table.py --check`;
8. `uv run python scripts/check_repository.py`; and
9. `lake build CLRSLean`.

Website generation and deployment are intentionally excluded.  Existing
non-blocking linter and documentation-role warnings will be recorded as
warnings rather than treated as proof failures.

## Completion Criteria

Chapter 30 is formally wrapped up when:

- the canonical chapter guide explains the full proof pipeline and cost split;
- the proof map exposes one unambiguous completion and verification entry;
- the status board describes excluded layers as optional extensions;
- the reusable execution/circuit lesson is recorded;
- progress remains 46/46 with zero missing core groups;
- the specified proof and repository checks pass; and
- no Chapter 30 source semantics have changed.
