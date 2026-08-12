import Mathlib
import CLRSLean.Chapter_35

/-!
# Chapter 35 — Approximation Algorithms

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_35`.
Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The approximation-algorithm models (Sections 35.1–35.3: vertex cover, TSP,
set cover) and the randomized/subset-sum layers (Sections 35.4–35.5) are
represented.  Several optimum and algorithm definitions currently use
placeholder implementations, so this layer should be read as preliminary
scaffolding, not as a complete formalization.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
