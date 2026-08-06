import CLRSLean.Chapter_13

/-!
# Chapter 13 — Red-Black Trees

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_13`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The existing color/black-height invariant, logarithmic-height theorem, and
functional insertion/deletion developments are reused.  The chapter remains
partial because {lit}`RedBlackShape` does not contain the separate BST ordering
invariant: BST/inorder preservation for rotations and updates, textbook
fixup-loop refinement, and logarithmic execution-cost theorems remain.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
