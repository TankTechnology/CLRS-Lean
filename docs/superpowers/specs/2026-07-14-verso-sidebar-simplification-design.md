# Verso site-wide sidebar simplification design

Date: 2026-07-14

Status: Design approved in conversation, awaiting written spec review

## Background

The CLRS-Lean Verso site renders the Lean module hierarchy directly in the sidebar. As proofs are split into smaller modules, the reader's table of contents begins to expose implementation structure. For example, Chapter 22's `22.3. Depth-First Search` shows five proof-helper pages underneath it, and `22.5. Strongly Connected Components` shows `Merge-Sort Congruence`. Other chapters, `Proof Patterns`, and `Probability` have the same problem.

These pages have audit value on their own and should not be deleted; the problem is only that they occupy the main reading table of contents, making the CLRS chapter and section structure hard to recognize.

## Goals

1. Keep the current top-level entries and their order, without adding new navigation groups.
2. All Chapters continue to expand by default.
3. Each chapter's sidebar shows only the chapter page and its direct CLRS `Section_*` pages.
4. `Proof Patterns` and `Probability` keep their top-level entries, but hide their submodules.
5. Hidden pages continue to be generated and retain search, sitemap, direct URLs, source, and parent-page entries.
6. When visiting a hidden page, the sidebar highlights the nearest visible parent page.
7. The rule automatically covers helper modules added later, avoiding a per-page blacklist to maintain.

## Non-goals

- Do not move or rename Lean files or modules.
- Do not modify import structure or theorem interfaces.
- Do not use Verso `exclude`; it would delete the page itself.
- Do not change top-level entry order, chapter default-expansion policy, body styles, or search ordering.
- Do not migrate the site into a standalone frontend application.

## Navigation visibility rules

Navigation links are keyed by the full Lean module name in the `title` attribute. A module appears in the sidebar only if it satisfies any of the following conditions:

1. The module is the site root, `CLRSLean`;
2. The module is a direct submodule of `CLRSLean`, e.g. `CLRSLean.Chapter_22`, `CLRSLean.ProofPatterns`, `CLRSLean.Progress`;
3. The module is a direct `Section_*` submodule of some `CLRSLean.Chapter_NN`, e.g. `CLRSLean.Chapter_22.Section_22_3_DFS`.

All other, deeper modules are pruned from the sidebar. If a navigation node has no recognizable full module name, the optimizer adopts a "keep" policy to avoid accidental deletion, while the rendering check treats the node as an unclassified error and blocks deployment.

Empty expand controls are not kept after children are pruned. Sections, `Proof Patterns`, or `Probability` that were rendered as `<details>` because of helper modules are converted to plain `.leaf` links once they no longer have visible children.

### Modules hidden under the current rules

The current rules hide 22 modules:

- `CLRSLean.ProofPatterns.{Boundary,Exchange,Fiber,Interval}`
- `CLRSLean.Probability.FiniteExpectation`
- `CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability`
- `CLRSLean.Chapter_08.Section_08_2_Counting_Sort.{CountTables,MutableOutputArray}`
- `CLRSLean.Chapter_09.Section_09_3_Deterministic_Select.Randomized_Select`
- `CLRSLean.Chapter_17.Section_17_1_Amortized_Framework.Section_17_2_Stack_And_Counter`
- `CLRSLean.Chapter_17.Section_17_4_Dynamic_Tables.Section_17_4_Mutable_Array_Tables`
- `CLRSLean.Chapter_21.Section_21_4_Analysis.{CostedExecution,InverseAckermann}`
- `CLRSLean.Chapter_22.Section_22_3_DFS.{S1_WhitePath,S2_Intervals,S3_Bridge,S4_SCC,S5_EdgeClassification}`
- `CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components.MergeSortCongr`
- `CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.{S1_UnionFindBridge,S2_StatefulKruskal,S3_ExecutablePrim}`

This list is for reviewing the current impact; it is not a runtime blacklist.

## Build architecture

The deployment pipeline stays as:

```text
Lean source
  -> Verso literate HTML
  -> optimize_literate_html.py
       1. existing long-page optimizations
       2. sidebar navigation tree pruning
       3. navigation-state and parent-highlight script injection
  -> rendered HTML checks
  -> sitemap
  -> GitHub Pages
```

Add a reusable navigation-visibility decision function that the optimizer, rendering checks, and tests all call, avoiding multiple scripts duplicating the rules.

Sidebar pruning only parses the `.module-tree` subtree. It removes invisible nodes by full module name, preserves the original order, and downgrades `<details>` elements with no visible children to `.leaf`. Body content, code blocks, asset references, and other navigation structures are not part of the pruning.

The navigation state storage key is bumped by one version so that the first visit after the change does not inherit state inconsistent with the old tree structure. The new version still defaults to "all Chapters expanded" and continues to persist the user's manual expand and collapse actions and the sidebar scroll position.

## Parent locating for hidden pages

Verso adds `.current` to the navigation node corresponding to the current page. If that node is hidden by the policy, the runtime navigation script compares the current URL with the normalized paths of all visible navigation links, chooses the longest directory prefix as the nearest visible parent, and applies `.current` to that parent's `.leaf` or `<summary>`.

This logic runs only when no visible `.current` exists after pruning; it does not override Verso's native highlighting for ordinary chapter and section pages.

## Implementation details entries

Parent modules that contain hidden subpages get a uniform `## Implementation details` section in their module-level documentation, using relative links that point to each hidden page. Currently affected:

- `CLRSLean/ProofPatterns.lean`
- `CLRSLean/Probability.lean`
- Chapter 7's 7.3 page
- Chapter 8's 8.2 page
- Chapter 9's 9.3 page
- Chapter 17's 17.1–17.3 and 17.4 pages
- Chapter 21's 21.4 page
- Chapter 22's 22.3 and 22.5 pages
- Chapter 23's 23.2 page

Existing plain-text module-name descriptions will be converted to clickable page links. Hidden pages remain reachable through search, sitemap, direct URLs, and these parent-page links. Previous/next page navigation keeps Verso's current behavior.

## Fault tolerance

- Missing or unparseable `title` module name: the optimizer keeps the node, and the rendering check reports an unclassified error and fails.
- Visible children remain after pruning: keep the `<details>` and its original expansion state.
- No visible children after pruning: convert to `.leaf`, and do not show an invalid collapse arrow.
- The hidden page does not exist: the parent-page link and site-integrity check fail, blocking deployment.
- The optimizer script is run repeatedly: the output must remain unchanged.

## Verification and acceptance criteria

### Unit tests

- Visibility decision covers root, top-level entries, direct Sections, Section descendants, and non-Chapter submodules.
- Navigation pruning preserves the original order and deletes all invisible nodes.
- Empty `<details>` correctly degrades to `.leaf`.
- Nodes without a module name are not accidentally deleted.
- Ordinary Sections keep their native `.current`; hidden pages use the nearest visible parent.
- Running the optimizer repeatedly stays idempotent.

### Generated-site checks

- Each generated page's `.module-tree` contains only module links that satisfy the visibility rules.
- The Chapter 22 sidebar contains only 22.1–22.5, not the six proof-helper pages.
- The HTML files for the current 22 hidden modules still exist and are included in the sitemap.
- All 11 parent pages' `Implementation details` links resolve to existing pages.
- Search assets still cover hidden pages.

### Browser checks

- No empty collapse arrows or leftover blank hierarchy on either desktop or mobile.
- All Chapters expand by default, and manual state and scroll position continue to persist.
- Parent highlighting is correct for both ordinary Sections and hidden pages.
- Parent-page links reach hidden pages, and breadcrumbs allow returning to the chapter and section reading path.

### Verification commands

```bash
python3 -m unittest scripts.test_optimize_literate_html scripts.test_literate_config
python3 scripts/check_repository.py
lake build :literateHtml
python3 scripts/optimize_literate_html.py <generated-site>
python3 scripts/check_literate_rendering.py <generated-site>
python3 scripts/generate_sitemap.py <generated-site> --base-url "https://tanktechnology.github.io/CLRS-Lean/"
```

## Expected changes

- A navigation-visibility helper module or an equivalent shared function
- `scripts/optimize_literate_html.py`
- `scripts/test_optimize_literate_html.py`
- `scripts/check_literate_rendering.py` and related tests
- Documentation links in the above 11 parent `.lean` pages
- Reader-navigation notes in `docs/site-architecture.md`

No proof declarations, proof terms, module paths, or deployment triggers will be modified.
