import CLRSLean.Chapter_10

/-!
# Chapter 10 — Elementary Data Structures

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_10`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The legacy stack, queue, list, and rooted-tree developments are reused, together
with the fourth-edition §10.1 array-backed stack and queue interface
(top/head/tail pointers with overflow, underflow, and circular wrap-around).
Concrete RAM execution and pointer memory remain deferred.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
