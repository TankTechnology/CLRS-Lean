# Chapter 19 Section Layout and Site Deployment Design

## Goal

Expose the completed Fibonacci-heap development under the textbook section
boundaries 19.1, 19.2, 19.3, and 19.4, while preserving existing import paths
and publishing the reorganized Verso site through the repository's GitHub Pages
workflow.

## Chosen approach

Move the theorem-bearing implementation files to canonical section modules and
replace their old S1/S2/S3 paths with compatibility imports.  Public theorem
names and namespaces do not change.

The canonical mapping is:

- `Section_19_1_Fibonacci_Heap_Model.lean`: abstract finite-set model.
- `Section_19_2_Mergeable_Heap_Operations.lean`: executable forest, cached
  minimum, LINK, CONSOLIDATE, and extract-min.
- `Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.lean`: duplicate-safe
  paths and zippers, CUT, CASCADING-CUT, decrease-key, and delete.
- `Section_19_3_Decreasing_A_Key_And_Deleting_A_Node/Amortized_Costs.lean`:
  instrumented operations, per-operation bounds, and trace telescoping.
- `Section_19_4_Bounding_Maximum_Degree.lean`: subtree-size and degree bounds.

The existing paths below
`Section_19_1_Fibonacci_Heap_Model/S1_ExecutableFibHeap.lean`,
`S2_CascadingCuts.lean`, and `S3_AmortizedCosts.lean` become documented import
shims.  This keeps downstream source compatibility without presenting those
filenames as the canonical chapter organization.

## Imports and interfaces

The chapter aggregator imports canonical modules only.  The main Chapter 19
interface test also imports canonical modules, while a small legacy-import test
ensures all three old paths continue to expose representative declarations.
The book root imports the compatibility modules solely to include their
registered pages in Verso's module set; reader-sidebar pruning still hides
section descendants.  No theorem is renamed or restated merely for the move.

## Website structure

`literate.toml` lists 19.1, 19.2, 19.3, and 19.4 as direct Chapter 19 children.
The amortized-cost module is a child of 19.3.  Compatibility modules remain
registered below 19.1 so site-consistency checks account for every Lean file,
but the existing sidebar-pruning policy keeps implementation children out of
the reader-facing chapter navigation.

Chapter prose, the proof map, the source index, and the progress CSV name the
canonical modules.  The CSV represented-section field changes from `19.1;19.4`
to `19.1;19.2;19.3;19.4`; theorem counts and completion status do not change.

## Verification and deployment

Development uses a red-green check: the interface and literate-config tests
first require the new module paths and fail because those paths are absent.
After migration, verify canonical and legacy imports, Chapter 19 compilation,
site consistency, progress metadata, and repository checks.

Because this request explicitly includes the website, build
`:literateHtml`, assemble the optimized `_site`, and run freshness/rendering
checks.  Generated HTML remains uncommitted.  After merging the source change
to `main`, manually dispatch `.github/workflows/pages.yml` and wait for the
GitHub Pages deployment job to succeed.

## Non-goals

- No theorem statement, proof, namespace, or cost model changes.
- No generated HTML committed to Git.
- No switch away from Verso or GitHub Pages.
- No removal of legacy imports in this change.
