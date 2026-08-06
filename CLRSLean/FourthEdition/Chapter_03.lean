import CLRSLean.Chapter_03

/-!
# Chapter 3 — Characterizing Running Times

This is the canonical CLRS fourth-edition chapter guide during the migration
period.

## Current source

During the compatibility period this guide imports {lit}`CLRSLean.Chapter_03`. Existing declarations retain their current namespaces until the chapter-by-chapter source migration.

## Coverage boundary

The legacy asymptotic-notation file supplies fourth-edition §§3.1--3.2, and the
legacy standard-functions file supplies §3.3.  Sections 3.1 and 3.3 cover their
represented mathematical interfaces.  Section 3.2 remains partial: the five
asymptotic relations are defined; discrete witness forms exist for O, Ω, o, and
ω, while Θ is exposed as O-and-Ω.  The shared-threshold two-sided Θ witness and
the expected {lit}`o`/{lit}`ω` algebra and duality wrappers remain to be exposed.

See {lit}`docs/clrs-fourth-edition-map.csv` for the section-level mapping and
{lit}`docs/migrations/clrs4.md` for compatibility and deprecation policy.
-/
