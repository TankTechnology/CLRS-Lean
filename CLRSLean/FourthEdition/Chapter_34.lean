import Mathlib
import CLRSLean.Chapter_34

/-!
# Chapter 34 — NP-Completeness

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_34`.
Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The NP-completeness foundations (Section 34.1–34.3) and the classical
reduction chain (Section 34.4–34.5) are represented as an early modeling
scaffold.  The computational cost model is idealized (`polyTime` is `True`)
and the decision problems currently use placeholder semantics, so this layer
should be read as preliminary scaffolding, not as a complete formalization.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
