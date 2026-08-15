import Mathlib

/-!
# Chapter 1 — The Role of Algorithms in Computing

This chapter is the doorway.  CLRS introduces what an algorithm is, why
correctness and efficiency matter, and how to think about algorithm design.
We do not repeat the original text; instead we show what those ideas look
like in Lean.

## Current source

Native fourth-edition guide.  Chapter 1 is prose-only: it has no section
directory and no theorem-bearing source, so the expository prose is owned here
directly.  The legacy import {lit}`CLRSLean.Chapter_01` forwards to this guide
during the compatibility period.

## An algorithm is a function … with a proof

In CLRS-Lean, *algorithm* means two things that live side by side:

1. A Lean function that computes something — the executable part.
2. A theorem that states what the function guarantees — the proof part.

For example, insertion sort is a pair {lit}`(f, P)` where {lit}`f` sorts a list and
{lit}`P` says that the result is ordered and permutes the input — see
Chapter 2 for the real Lean version.

Every section in later chapters follows this pattern: define the computation,
then prove the claim.

## Why formalize algorithm proofs?

Algorithm textbooks use pseudocode and loop invariants.  Lean can express
the same invariants as types, and the same inductive reasoning as dependent
pattern matching.  The gain is **machine-checked certainty**:

* No off-by-one errors in the invariant.
* No hand-waving about "and so forth" in an induction.
* The proof object can be inspected, reused, and composed.

The cost is precision: every case must be handled, every inequality justified.

## How to read the rest

Start with the sections that already have strong proof stories:

* Chapter 2: sorting correctness, a runtime bound, and a merge-sort recurrence.
* Chapter 16: Huffman optimality, the flagship greedy proof.
* Chapter 23: the MST cut property and Kruskal's induction.

To build and browse the site locally:

* {lit}`lake build` compiles everything.
* {lit}`lake build :literateHtml` generates this website.

## Conventions

* **0-indexed**: lists and sequences start at 0, for Mathlib compatibility.
* **Total functions**: partial operations return junk values, not {lit}`Option`.
* **Unfinished theorem targets**: kept out of imported proof files and recorded
  as {lit}`partial`, {lit}`blocked-design`, or {lit}`future-work` in the status pages.
  Each chapter page lists exactly what is missing.

## Repository

[TankTechnology/CLRS-Lean](https://github.com/TankTechnology/CLRS-Lean)

## Coverage boundary

The existing expository guide is reused; no theorem target is claimed.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/

namespace CLRS
namespace Chapter01
end Chapter01
end CLRS
