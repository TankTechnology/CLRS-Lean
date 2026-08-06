import CLRSLean.Chapter_29

/-!
# Chapter 29 — Linear Programming

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_29`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The modeling and duality developments are reused, while detailed SIMPLEX remains
online material.  The chapter is still partial: §29.1 lacks a general-form
normalization and a canonical main-text algorithm wrapper; §29.2 lacks finite
{lit}`StandardLP` encoding/refinement bridges for the specialized formulations;
and §29.3's strongest duality declarations still live in a legacy initialization
module that is also assigned to the online-material ledger.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
