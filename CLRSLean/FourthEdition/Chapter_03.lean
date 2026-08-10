import CLRSLean.Chapter_03

/-!
# Chapter 3 — Characterizing Running Times

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_03`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The legacy asymptotic-notation file supplies fourth-edition §§3.1--3.2, and the
legacy standard-functions file supplies §3.3.  All three sections cover their
represented mathematical interfaces: the five asymptotic relations are defined
with discrete witness forms for O, Ω, o, and ω, the shared-threshold two-sided
Θ witness (CLRS Definition 3.1), and the transpose-symmetry duality together
with the transitivity, additivity, and multiplicativity algebra for o/ω.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
