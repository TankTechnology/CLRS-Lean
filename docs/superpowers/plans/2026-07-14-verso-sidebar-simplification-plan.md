# Verso Sidebar Simplification Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Keep CLRS chapters and direct sections in the Verso sidebar while hiding deeper proof-support modules without deleting their pages.

**Architecture:** A shared Python module will own the reader-visible module predicate and deterministic rewrite of Verso's generated `.module-tree`. The existing HTML optimizer will apply that rewrite and inject parent-highlighting behavior; the rendering checker will reuse the same policy to reject unpruned or unlinked output. Source-level module docs will expose hidden pages through explicit `Implementation details` links.

**Tech Stack:** Python 3 standard library (`html.parser`, `re`, `unittest`), Lean 4/Verso literate HTML, GitHub Pages workflow, Playwright browser verification.

---

## Baseline and file map

The worktree is based on `main` commit `c14a957` with the approved design cherry-picked as `d870c58`.

Fresh baseline evidence:

- `python3 -m unittest scripts.test_optimize_literate_html scripts.test_literate_config`: 10 tests pass.
- `lake build CLRSLean`: succeeds (8714 jobs).
- `python3 scripts/check_repository.py`: fails before this feature because five existing `sorry` terms remain in `CLRSLean/Chapter_20/Section_20_3_Recursive_VEB.lean`. This plan does not modify that proof file; the final report must distinguish this pre-existing policy failure from feature regressions.

Files and responsibilities:

- Create `scripts/literate_navigation.py`: module visibility policy, module-tree rewrite, inspection results.
- Create `scripts/test_literate_navigation.py`: visibility and rewrite unit tests.
- Modify `scripts/optimize_literate_html.py`: apply rewrite, count changes, inject navigation state v7 and hidden-page parent highlighting.
- Modify `scripts/test_optimize_literate_html.py`: optimizer integration, idempotence, and script behavior tests.
- Modify `scripts/check_literate_rendering.py`: reject hidden sidebar nodes, unclassified links, empty disclosure nodes, missing parent links, and missing hidden pages.
- Create `scripts/test_check_literate_rendering.py`: generated-site validation tests.
- Modify `scripts/check_repository.py`: run the two new Python test files in the fast check suite.
- Modify 11 parent `.lean` modules: add reader-facing links to hidden proof pages.
- Modify `docs/site-architecture.md`: document the reader-visible navigation rule and retained implementation pages.

### Task 1: Centralize the reader-visible module policy

**Files:**

- Create: `scripts/literate_navigation.py`
- Create: `scripts/test_literate_navigation.py`

- [ ] **Step 1: Write failing visibility tests**

Create `scripts/test_literate_navigation.py` with these cases:

```python
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.literate_navigation import is_reader_sidebar_module


class ReaderSidebarModuleTests(unittest.TestCase):
    def test_keeps_root_and_top_level_pages(self) -> None:
        self.assertTrue(is_reader_sidebar_module("CLRSLean"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.ProofPatterns"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.Chapter_22"))
        self.assertTrue(is_reader_sidebar_module("CLRSLean.Progress"))

    def test_keeps_direct_chapter_sections(self) -> None:
        self.assertTrue(
            is_reader_sidebar_module("CLRSLean.Chapter_22.Section_22_3_DFS")
        )

    def test_hides_nonchapter_children_and_section_descendants(self) -> None:
        hidden = [
            "CLRSLean.ProofPatterns.Boundary",
            "CLRSLean.Probability.FiniteExpectation",
            "CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath",
            "CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim.S3_ExecutablePrim",
        ]
        self.assertTrue(all(not is_reader_sidebar_module(name) for name in hidden))

    def test_rejects_unrelated_or_malformed_names(self) -> None:
        self.assertFalse(is_reader_sidebar_module("Other.Root"))
        self.assertFalse(is_reader_sidebar_module("CLRSLean.Chapter_22.Helper"))


if __name__ == "__main__":
    unittest.main()
```

- [ ] **Step 2: Run the tests and confirm the missing-module failure**

Run:

```bash
python3 -m unittest scripts.test_literate_navigation
```

Expected: `ERROR` with `ModuleNotFoundError: No module named 'scripts.literate_navigation'`.

- [ ] **Step 3: Implement the minimal visibility predicate**

Create `scripts/literate_navigation.py` with this public function:

```python
from __future__ import annotations

import re


CHAPTER_MODULE_RE = re.compile(r"Chapter_[0-9][0-9]")


def is_reader_sidebar_module(module_name: str) -> bool:
    parts = module_name.split(".")
    if parts == ["CLRSLean"]:
        return True
    if len(parts) == 2 and parts[0] == "CLRSLean":
        return True
    return (
        len(parts) == 3
        and parts[0] == "CLRSLean"
        and CHAPTER_MODULE_RE.fullmatch(parts[1]) is not None
        and parts[2].startswith("Section_")
    )
```

- [ ] **Step 4: Run the visibility tests**

Run:

```bash
python3 -m unittest scripts.test_literate_navigation
```

Expected: 4 tests pass.

- [ ] **Step 5: Commit the policy**

```bash
git add scripts/literate_navigation.py scripts/test_literate_navigation.py
git commit -m "test(site): define reader-visible sidebar modules"
```

### Task 2: Prune the generated module tree and flatten empty disclosures

**Files:**

- Modify: `scripts/literate_navigation.py`
- Modify: `scripts/test_literate_navigation.py`

- [ ] **Step 1: Add failing rewrite tests**

Extend `scripts/test_literate_navigation.py` with a representative Verso tree. The test input must contain:

```html
<nav class="module-tree">
  <details open><summary><a href="CLRSLean/ProofPatterns/" title="CLRSLean.ProofPatterns">Patterns</a></summary>
    <div class="leaf"><a href="CLRSLean/ProofPatterns/Boundary/" title="CLRSLean.ProofPatterns.Boundary">Boundary</a></div>
  </details>
  <details open><summary><a href="CLRSLean/Chapter_22/" title="CLRSLean.Chapter_22">Chapter 22</a></summary>
    <details open><summary class="current"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/" title="CLRSLean.Chapter_22.Section_22_3_DFS">22.3</a></summary>
      <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/" title="CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath">White Path</a></div>
    </details>
    <div class="leaf"><a href="CLRSLean/Chapter_22/Section_22_4_Topological_Sort/" title="CLRSLean.Chapter_22.Section_22_4_Topological_Sort">22.4</a></div>
  </details>
</nav>
```

Assert that `prune_reader_sidebar()`:

- removes `Boundary` and `White Path`;
- returns their two module names in `removed_modules`;
- converts `ProofPatterns` and `22.3` to `.leaf` nodes;
- preserves `current` on the converted `22.3` leaf;
- keeps Chapter 22 as an open `<details>` containing 22.3 and 22.4 in order;
- returns unchanged output and zero removals/flattenings when invoked a second time;
- keeps an anchor without `title` and records its href in `unclassified_hrefs`.

Use this API in the test:

```python
result = prune_reader_sidebar(source)
self.assertEqual(result.removed_modules, (...))
self.assertIn('<div class="leaf current">', result.html)
self.assertEqual(prune_reader_sidebar(result.html).html, result.html)
```

- [ ] **Step 2: Run the rewrite tests and confirm the import failure**

Run:

```bash
python3 -m unittest scripts.test_literate_navigation
```

Expected: `ImportError` because `prune_reader_sidebar` is not defined.

- [ ] **Step 3: Implement the deterministic Verso tree rewrite**

Add these public result types and API to `scripts/literate_navigation.py`:

```python
from dataclasses import dataclass


@dataclass(frozen=True)
class SidebarRewrite:
    html: str
    removed_modules: tuple[str, ...]
    flattened_modules: tuple[str, ...]
    unclassified_hrefs: tuple[str, ...]


def prune_reader_sidebar(document: str) -> SidebarRewrite:
    """Prune one generated `.module-tree` without changing the rest of the page."""
```

Implement the rewrite against Verso's generated structure, not arbitrary page markup:

1. Locate the single `<nav class="module-tree">...</nav>` fragment.
2. Parse its nested `<details>`, `<summary>`, `.leaf`, and `<a>` elements with a dedicated `HTMLParser` tree whose serializer HTML-escapes attribute values and text.
3. For each `.leaf` or `<details>` owner, read the direct anchor's `title`.
4. Remove the complete owner subtree when the title is recognized and `is_reader_sidebar_module(title)` is false.
5. Keep owners with missing titles and append their href to `unclassified_hrefs`.
6. After child removal, convert a visible `<details>` with no remaining `.leaf` or `<details>` children into `<div class="leaf">ANCHOR</div>`; carry `current` from `<summary class="current">` to the new div.
7. Preserve visible node order, anchor attributes, nav-title markup, and the `open` attribute on remaining details.
8. Return the original document byte-for-byte when no rewrite is required.

The internal element type must be concrete and fully owned by this module:

```python
@dataclass
class _Element:
    tag: str
    attrs: list[tuple[str, str | None]]
    children: list["_Element | _Text"]
    self_closing: bool = False


@dataclass
class _Text:
    value: str
    raw: bool = False
```

Use `_ModuleTreeParser(HTMLParser)` to build this tree, `_rewrite_owner()` to remove or flatten navigation owners, and `_render()` to serialize the result. Do not add an HTML parsing dependency to the project.

- [ ] **Step 4: Run the rewrite tests**

Run:

```bash
python3 -m unittest scripts.test_literate_navigation
```

Expected: all visibility and rewrite tests pass.

- [ ] **Step 5: Commit the static rewrite**

```bash
git add scripts/literate_navigation.py scripts/test_literate_navigation.py
git commit -m "feat(site): prune proof modules from Verso sidebar"
```

### Task 3: Integrate pruning and hidden-page parent highlighting

**Files:**

- Modify: `scripts/optimize_literate_html.py`
- Modify: `scripts/test_optimize_literate_html.py`

- [ ] **Step 1: Write failing optimizer integration tests**

Add tests that optimize an HTML file containing the Task 2 navigation fixture and assert:

```python
self.assertNotIn("S1_WhitePath", text)
self.assertIn('title="CLRSLean.Chapter_22.Section_22_3_DFS"', text)
self.assertIn('<div class="leaf current">', text)
self.assertEqual(stats.removed_nav_modules, 1)
self.assertEqual(stats.flattened_nav_details, 1)
```

Extend the navigation-script test to require:

```python
self.assertIn('clrs.nav.state.v7', text)
self.assertIn('clrs.nav.scroll.v7', text)
self.assertIn('window.location.href', text)
self.assertIn('bestParent', text)
self.assertNotIn('clrs.nav.state.v6', text)
```

Keep the existing idempotence test and add an assertion that the second optimization removes zero modules and flattens zero details.

- [ ] **Step 2: Run the optimizer tests and confirm failure**

Run:

```bash
python3 -m unittest scripts.test_optimize_literate_html
```

Expected: failures for missing `PageStats` fields and state version v7.

- [ ] **Step 3: Apply the sidebar rewrite in `optimize_file`**

Import `prune_reader_sidebar`. After the streaming optimizer writes its temporary file and before script/meta injection, execute:

```python
text = tmp.read_text(encoding="utf-8", errors="replace")
sidebar = prune_reader_sidebar(text)
text = sidebar.html
text, injected_nav_scripts = inject_nav_state_script(text)
text, injected_verification_meta = inject_google_site_verification(text)
if (
    sidebar.removed_modules
    or sidebar.flattened_modules
    or injected_nav_scripts
    or injected_verification_meta
):
    tmp.write_text(text, encoding="utf-8", newline="")
```

Add `removed_nav_modules` and `flattened_nav_details` integer fields to `PageStats`, include them in `changed`, construct them from the tuple lengths, and print them in the CLI statistics.

Because `optimize_literate_html.py` is both imported by tests and executed directly by CI, insert the repository root into `sys.path` before importing the shared module:

```python
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.literate_navigation import prune_reader_sidebar
```

- [ ] **Step 4: Upgrade the navigation state and add nearest-visible-parent highlighting**

Change both storage keys to v7. Refactor path normalization into:

```javascript
function stablePath(raw) {
  if (!raw) return "";
  try {
    const path = new URL(raw, document.baseURI).pathname
      .replace(/\/(?:index\.html)?$/, "")
      .replace(/^.*\/CLRSLean\//, "/CLRS-Lean/")
      .replace(/^.*\/CLRS-Lean\//, "/CLRS-Lean/");
    return path || raw;
  } catch (_err) {
    return raw;
  }
}

function stableNavPath(link) {
  return stablePath(link?.getAttribute("href"));
}
```

Immediately before opening current ancestors, use a mutable `current` and select the longest visible path prefix only when Verso's `.current` is absent:

```javascript
let current = nav.querySelector(".current");
if (!current) {
  const pagePath = stablePath(window.location.href);
  let bestParent = null;
  let bestLength = -1;
  for (const link of nav.querySelectorAll("a[title]")) {
    const candidate = stableNavPath(link);
    if (
      candidate &&
      (pagePath === candidate || pagePath.startsWith(`${candidate}/`)) &&
      candidate.length > bestLength
    ) {
      bestParent = link.closest("summary, .leaf");
      bestLength = candidate.length;
    }
  }
  if (bestParent) {
    bestParent.classList.add("current");
    current = bestParent;
  }
}
```

Leave the existing default `details.open = true`, saved disclosure state, scroll restoration, and summary-link click handling unchanged.

- [ ] **Step 5: Run optimizer and navigation tests**

Run:

```bash
python3 -m unittest scripts.test_literate_navigation scripts.test_optimize_literate_html
```

Expected: all tests pass.

- [ ] **Step 6: Commit optimizer integration**

```bash
git add scripts/optimize_literate_html.py scripts/test_optimize_literate_html.py
git commit -m "feat(site): integrate simplified sidebar navigation"
```

### Task 4: Enforce the reader navigation contract in generated output

**Files:**

- Modify: `scripts/check_literate_rendering.py`
- Create: `scripts/test_check_literate_rendering.py`
- Modify: `scripts/check_repository.py`

- [ ] **Step 1: Write failing rendered-site contract tests**

Refactor the checker around `check_site(site_root: Path) -> list[str]`. In a temporary site, create:

- `CLRSLean/Chapter_22/Section_22_3_DFS/index.html` with a visible parent sidebar node;
- `CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/index.html` as the retained hidden page;
- a parent page that initially lacks the implementation href.

Add tests asserting that `check_site()` reports:

1. a forbidden sidebar module when `S1_WhitePath` remains in `.module-tree`;
2. an unclassified sidebar link when an `<a>` lacks `title`;
3. a missing parent-page link when the hidden page exists but the parent lacks `href="CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/"`;
4. success after the sidebar is pruned and the exact parent href is present;
5. the existing raw Markdown table error.

End `scripts/test_check_literate_rendering.py` with `if __name__ == "__main__": unittest.main()` so `check_repository.py` can execute it directly.

- [ ] **Step 2: Run checker tests and confirm failure**

Run:

```bash
python3 -m unittest scripts.test_check_literate_rendering
```

Expected: import or assertion failures because `check_site` does not exist.

- [ ] **Step 3: Implement generated-site validation**

In `check_literate_rendering.py`:

- retain `RAW_MARKDOWN_TABLE_RE`;
- import `is_reader_sidebar_module` and `prune_reader_sidebar`;
- derive module names from `CLRSLean/**/index.html` path components joined with `.`;
- for each page, fail if `prune_reader_sidebar(text)` would remove or flatten anything, or if it reports unclassified hrefs;
- for every generated module that `is_reader_sidebar_module` hides, find the nearest visible parent by repeatedly removing the final module component;
- require both the hidden page file and the visible parent `index.html` to exist;
- require the parent HTML to contain the site-root href `href="{module_name.replace('.', '/')}/"`.

Use the same repository-root `sys.path` bootstrap as the optimizer before importing `scripts.literate_navigation`; this keeps both `python3 scripts/check_literate_rendering.py` and module-based unit tests working.

Keep CLI behavior stable: print every failure, exit 1 on any failure, otherwise print `literate rendering OK: <site_root>`.

- [ ] **Step 4: Register new fast tests**

Add these entries to `CHECK_SCRIPTS` in `scripts/check_repository.py` before the placeholder scan:

```python
"scripts/test_literate_navigation.py",
"scripts/test_check_literate_rendering.py",
```

- [ ] **Step 5: Run all Python site tests**

Run:

```bash
python3 -m unittest \
  scripts.test_literate_navigation \
  scripts.test_optimize_literate_html \
  scripts.test_literate_config \
  scripts.test_check_literate_rendering
```

Expected: all tests pass.

- [ ] **Step 6: Commit the deployment guard**

```bash
git add scripts/check_literate_rendering.py scripts/test_check_literate_rendering.py scripts/check_repository.py
git commit -m "test(site): enforce simplified rendered navigation"
```

### Task 5: Add Implementation details links to every affected parent page

**Files:**

- Modify: `CLRSLean/ProofPatterns.lean`
- Modify: `CLRSLean/Probability.lean`
- Modify: `CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort.lean`
- Modify: `CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean`
- Modify: `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean`
- Modify: `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean`
- Modify: `CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables.lean`
- Modify: `CLRSLean/Chapter_21/Section_21_4_Analysis.lean`
- Modify: `CLRSLean/Chapter_22/Section_22_3_DFS.lean`
- Modify: `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean`
- Modify: `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean`

- [ ] **Step 1: Run the rendered-site checker against an optimized build and capture missing-link failures**

Run:

```bash
SITE=$(lake query :literateHtml)
python3 scripts/optimize_literate_html.py "$SITE"
python3 scripts/check_literate_rendering.py "$SITE"
```

Expected: failure listing the hidden modules whose visible parent pages do not yet contain implementation links.

- [ ] **Step 2: Add exact site-root links to module-level docs**

Add a `## Implementation details` section before each module doc comment closes. Use these exact targets:

| Parent file | Link targets |
|---|---|
| `CLRSLean/ProofPatterns.lean` | `CLRSLean/ProofPatterns/Boundary/`, `Exchange/`, `Fiber/`, `Interval/` with the full `CLRSLean/ProofPatterns/` prefix on every href |
| `CLRSLean/Probability.lean` | `CLRSLean/Probability/FiniteExpectation/` |
| Chapter 7 section 7.3 | `CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort/Comparison_Probability/` |
| Chapter 8 section 8.2 | `.../CountTables/`, `.../MutableOutputArray/` using the full `CLRSLean/Chapter_08/Section_08_2_Counting_Sort/` prefix |
| Chapter 9 section 9.3 | `CLRSLean/Chapter_09/Section_09_3_Deterministic_Select/Randomized_Select/` |
| Chapter 17 section 17.1–17.3 | `CLRSLean/Chapter_17/Section_17_1_Amortized_Framework/Section_17_2_Stack_And_Counter/` |
| Chapter 17 section 17.4 | `CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables/Section_17_4_Mutable_Array_Tables/` |
| Chapter 21 section 21.4 | `.../CostedExecution/`, `.../InverseAckermann/` using the full `CLRSLean/Chapter_21/Section_21_4_Analysis/` prefix |
| Chapter 22 section 22.3 | `.../S1_WhitePath/` through `.../S5_EdgeClassification/` using the full `CLRSLean/Chapter_22/Section_22_3_DFS/` prefix |
| Chapter 22 section 22.5 | `CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components/MergeSortCongr/` |
| Chapter 23 section 23.2 | `.../S1_UnionFindBridge/`, `.../S2_StatefulKruskal/`, `.../S3_ExecutablePrim/` using the full `CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim/` prefix |

Use ordinary Verso Markdown links, for example:

```markdown
## Implementation details

The following proof-support pages remain available outside the main sidebar:

* [White-Path Theorem](CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/)
* [Intervals and Timestamps](CLRSLean/Chapter_22/Section_22_3_DFS/S2_Intervals/)
```

Use each child module's title from `literate.toml` as its link label. Do not change imports, namespaces, declarations, or proofs.

- [ ] **Step 3: Rebuild the literate site and run the checker**

Run:

```bash
SITE=$(lake query :literateHtml)
python3 scripts/optimize_literate_html.py "$SITE"
python3 scripts/check_literate_rendering.py "$SITE"
```

Expected: `literate rendering OK` and no missing implementation-page links.

- [ ] **Step 4: Build the Lean library**

Run:

```bash
lake build CLRSLean
```

Expected: exit 0. Existing linter warnings are allowed; new Lean errors are not.

- [ ] **Step 5: Commit reader links**

```bash
git add CLRSLean/ProofPatterns.lean CLRSLean/Probability.lean \
  CLRSLean/Chapter_07/Section_07_3_Randomized_Quicksort.lean \
  CLRSLean/Chapter_08/Section_08_2_Counting_Sort.lean \
  CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean \
  CLRSLean/Chapter_17/Section_17_1_Amortized_Framework.lean \
  CLRSLean/Chapter_17/Section_17_4_Dynamic_Tables.lean \
  CLRSLean/Chapter_21/Section_21_4_Analysis.lean \
  CLRSLean/Chapter_22/Section_22_3_DFS.lean \
  CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components.lean \
  CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
git commit -m "docs(site): link hidden proof implementation pages"
```

### Task 6: Document the rule and perform full deployment verification

**Files:**

- Modify: `docs/site-architecture.md`
- Modify: `docs/superpowers/plans/2026-07-14-verso-sidebar-simplification-plan.md` (check completed steps)

- [ ] **Step 1: Update site architecture**

Document these facts in `docs/site-architecture.md`:

- the reader sidebar retains top-level pages and direct chapter sections only;
- deeper modules are still generated and reached from `Implementation details`, search, sitemap, and direct URLs;
- the optimizer flattens visible nodes that lose all visible children;
- hidden pages highlight their nearest visible parent;
- all chapter disclosures still default open and retain saved state.

- [ ] **Step 2: Run the complete Python site suite**

```bash
python3 -m unittest \
  scripts.test_literate_navigation \
  scripts.test_optimize_literate_html \
  scripts.test_literate_config \
  scripts.test_check_literate_rendering
```

Expected: all tests pass with zero failures.

- [ ] **Step 3: Build, optimize, check, and generate sitemap from fresh output**

```bash
rm -rf .lake/build/literate-html _site
SITE=$(lake query :literateHtml)
mkdir -p _site
cp -r "$SITE"/* _site/
cp docs/literate/clrs-literate.css _site/clrs-literate.css
python3 scripts/optimize_literate_html.py _site
python3 scripts/check_literate_rendering.py _site
python3 scripts/generate_sitemap.py _site --base-url "https://tanktechnology.github.io/CLRS-Lean/"
```

Expected: fresh Verso build succeeds, rendering check passes, and sitemap generation reports URLs.

- [ ] **Step 4: Verify the original Chapter 22 symptom and retained pages**

Run exact assertions:

```bash
rg -L 'title="CLRSLean.Chapter_22.Section_22_3_DFS.S1_WhitePath"' _site/CLRSLean/Chapter_22/Section_22_3_DFS/index.html
test -f _site/CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/index.html
test -f _site/CLRSLean/Chapter_22/Section_22_5_Strongly_Connected_Components/MergeSortCongr/index.html
rg 'CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/' _site/CLRSLean/Chapter_22/Section_22_3_DFS/index.html
rg 'CLRSLean/Chapter_22/Section_22_3_DFS/S1_WhitePath/' _site/sitemap.xml
```

Expected: no hidden sidebar title, both hidden HTML files exist, and parent page plus sitemap contain the retained White-Path URL.

- [ ] **Step 5: Run the repository checker and record only the known baseline exception**

```bash
python3 scripts/check_repository.py
```

Expected on base `c14a957`: site-related scripts pass, followed by the same five pre-existing Chapter 20 `sorry` findings. Any new failure is a regression and must be fixed.

- [ ] **Step 6: Perform desktop and mobile browser verification**

Serve `_site` locally and use Playwright to check:

- homepage sidebar keeps the existing flat top-level ordering;
- all chapters initially render open;
- Chapter 22 shows only 22.1–22.5;
- 22.3 and 22.5 have no empty disclosure arrows;
- a direct visit to `S1_WhitePath/` highlights 22.3;
- a 390×844 viewport opens the hamburger sidebar without overflow or blank nesting.

Capture screenshots for the homepage, Chapter 22, hidden White-Path page, and mobile Chapter 22 page.

- [ ] **Step 7: Commit architecture documentation and checked plan**

```bash
git add docs/site-architecture.md docs/superpowers/plans/2026-07-14-verso-sidebar-simplification-plan.md
git commit -m "docs(site): record simplified sidebar architecture"
```

- [ ] **Step 8: Run final diff and history checks**

```bash
git diff --check main...HEAD
git status --short
git log --oneline --decorate main..HEAD
```

Expected: no whitespace errors, clean worktree, and only sidebar-design/implementation commits on the feature branch.
