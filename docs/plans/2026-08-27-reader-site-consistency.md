# Reader-Site Consistency and Deployment Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Publish the current proof state through a fourth-edition-first site whose audit data, labels, landing page, mobile header, and sidebar defaults agree with the repository.

**Architecture:** Keep Lean, Verso, the HTML optimizer, and the GitHub Pages workflow as the existing boundaries. Add one strict-CSV helper shared by the edition-map and online-material loaders, update labels and Literate prose at their current sources, and limit browser behavior changes to the injected sidebar script and mobile breadcrumb CSS.

**Tech Stack:** Lean 4 Literate modules, Python 3 `unittest`, TOML, CSS, browser JavaScript, GitHub Actions/Pages.

---

### Task 1: Reject malformed audit CSV rows

**Files:**
- Create: `scripts/csv_contract.py`
- Modify: `scripts/check_edition_map.py:22-64`
- Modify: `scripts/online_material.py:20-39`
- Modify: `scripts/test_check_edition_map.py:103-108`
- Modify: `docs/clrs-fourth-edition-map.csv:2-68`

- [ ] **Step 1: Write failing overflow-field tests**

Add to `EditionMapTests`:

```python
    def test_rejects_extra_edition_map_field_with_line_number(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-fourth-edition-map.csv"
        lines = path.read_text(encoding="utf-8").splitlines()
        lines[1] = f"{lines[1]},unexpected"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        self.assertIn(
            "clrs-fourth-edition-map.csv line 2: unexpected extra fields: unexpected",
            validate_repository(root),
        )

    def test_rejects_extra_online_ledger_field_with_line_number(self) -> None:
        root = self.make_repo()
        path = root / "docs" / "clrs-online-material.csv"
        lines = path.read_text(encoding="utf-8").splitlines()
        lines[1] = f"{lines[1]},unexpected"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        self.assertIn(
            "clrs-online-material.csv line 2: unexpected extra fields: unexpected",
            validate_repository(root),
        )
```

- [ ] **Step 2: Verify RED**

Run `uv run python scripts/test_check_edition_map.py`.

Expected: both new tests fail because overflow fields remain under a `None`
key without an audit error.

- [ ] **Step 3: Add the strict loader**

Create `scripts/csv_contract.py`:

```python
"""Strict helpers for machine-readable repository CSV contracts."""

from __future__ import annotations

import csv
from pathlib import Path


def load_strict_dict_rows(
    path: Path, expected_header: list[str]
) -> list[dict[str, str]]:
    """Load a CSV and reject header mismatches and overflow fields."""
    if not path.is_file():
        raise ValueError(f"missing file: {path.name}")
    with path.open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if reader.fieldnames != expected_header:
            raise ValueError(
                f"unexpected header in {path.name}: {reader.fieldnames}; "
                f"expected {expected_header}"
            )
        rows: list[dict[str, str]] = []
        for line, raw_row in enumerate(reader, start=2):
            extras = raw_row.pop(None, None)
            if extras is not None:
                rendered = ", ".join(value for value in extras if value is not None)
                raise ValueError(
                    f"{path.name} line {line}: unexpected extra fields: {rendered}"
                )
            rows.append({field: raw_row[field] or "" for field in expected_header})
        return rows
```

- [ ] **Step 4: Route both ledgers through the helper**

In `check_edition_map.py`, import `load_strict_dict_rows`, remove the local
`load_csv`, and use:

```python
    try:
        map_rows = load_strict_dict_rows(map_path, MAP_HEADER)
    except ValueError as error:
        return [str(error)]
```

In `online_material.py`, import the helper and use:

```python
def load_online_rows(root: Path = ROOT) -> list[dict[str, str]]:
    return load_strict_dict_rows(
        root / "docs" / "clrs-online-material.csv", ONLINE_HEADER
    )
```

- [ ] **Step 5: Repair and verify the real map**

Wrap each of the nine overflow-producing `coverage_note` fields in CSV double
quotes, preserving its full prose. Run:

```bash
uv run python - <<'PY'
import csv
from pathlib import Path
with Path("docs/clrs-fourth-edition-map.csv").open(newline="", encoding="utf-8") as handle:
    for line, row in enumerate(csv.DictReader(handle), start=2):
        if None in row:
            print(line, row[None])
PY
uv run python scripts/test_check_edition_map.py
uv run python scripts/check_edition_map.py
git diff --check
```

Expected: the probe is silent and both checks pass.

- [ ] **Step 6: Commit**

```bash
git add scripts/csv_contract.py scripts/check_edition_map.py scripts/online_material.py scripts/test_check_edition_map.py docs/clrs-fourth-edition-map.csv
git commit -m "fix(audit): reject malformed ledger rows"
```

### Task 2: Correct fourth-edition reader titles

**Files:**
- Modify: `scripts/test_literate_config.py:94-125`
- Modify: `literate.toml:3121-3150`
- Modify: `literate.toml:3366-3390`

- [ ] **Step 1: Add the failing title contract**

Add this method to `LiterateConfigTest`:

```python
    def test_completed_fourth_edition_sections_have_canonical_titles(self) -> None:
        titles = parse_module_titles(LITERATE_TOML.read_text(encoding="utf-8"))
        expected = {
            "CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp":
                "24.2. The Edmonds-Karp Algorithm",
            "CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.Ford_Fulkerson_Augmentation":
                "Ford-Fulkerson Augmentation Foundation",
            "CLRSLean.FourthEdition.Chapter_24.Section_24_3_Bipartite_Matching":
                "24.3. Maximum Bipartite Matching",
            "CLRSLean.FourthEdition.Chapter_24.Section_24_6_MaxFlow_MinCut":
                "Theorem 24.6. Max-Flow Min-Cut",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality": "29.3. Duality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.Definitions":
                "29.3. Dual Feasibility",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.WeakDuality":
                "29.3. Weak Duality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.Optimality":
                "29.3. Primal and Dual Optimality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.ComplementarySlackness":
                "29.3. Complementary-Slackness Gap Identity",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.TerminalCertificate":
                "29.3. Terminal Dual Certificates",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.DictionaryBridge":
                "29.3. Dictionary/Primal Bridge",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.StrongDuality":
                "29.3. Strong Duality",
            "CLRSLean.FourthEdition.Chapter_29.Section_29_3_Duality.ComplementarySlacknessTheorem":
                "29.3. Complementary-Slackness Theorem",
        }
        self.assertEqual(expected, {module: titles.get(module) for module in expected})
```

- [ ] **Step 2: Verify RED**

Run `uv run python scripts/test_literate_config.py`.

Expected: four stale `(partial)` labels and nine stale `29.4` prefixes fail.

- [ ] **Step 3: Correct the metadata**

Remove `(partial)` from the four named Chapter 24 titles and replace `29.4.`
with `29.3.` in the nine named Chapter 29 titles. Do not edit unqualified
`CLRSLean.Chapter_*` metadata.

- [ ] **Step 4: Verify and commit**

```bash
uv run python scripts/test_literate_config.py
uv run python scripts/check_literate_config.py
git diff --check
git add scripts/test_literate_config.py literate.toml
git commit -m "fix(site): align fourth-edition section titles"
```

Expected: both configuration checks pass.

### Task 3: Use compact navigation defaults

**Files:**
- Modify: `scripts/test_optimize_literate_html.py:103-132,195-219`
- Modify: `scripts/optimize_literate_html.py:69-188`
- Modify: `scripts/test_prepare_literate_site.py:32-40`
- Modify: `docs/literate/clrs-literate.css:625-637`

- [ ] **Step 1: Require collapsed defaults and a new state version**

Replace the relevant optimizer assertions with:

```python
        self.assertIn("details.open = false", text)
        self.assertNotIn("details.open = true", text)
        self.assertIn("parent.open = true", text)
        self.assertIn("clrs.nav.state.v8", text)
        self.assertIn("clrs.nav.scroll.v8", text)
        self.assertNotIn("clrs.nav.state.v7", text)
        self.assertNotIn("clrs.nav.scroll.v7", text)
```

Update `test_nav_state_script_replaces_stale_version` to require `v8` and
reject `v4`.

- [ ] **Step 2: Require one mobile breadcrumb**

Rename the first `PrepareLiterateSiteTests` method to
`test_mobile_stylesheet_keeps_only_the_root_breadcrumb` and use:

```python
        self.assertIn(".breadcrumbs li:not(:first-child)", stylesheet)
        self.assertNotIn(
            ".breadcrumbs li:last-child:not(:first-child)", stylesheet
        )
        self.assertIn(".breadcrumbs li:not(:last-child)::after", stylesheet)
```

- [ ] **Step 3: Verify RED**

```bash
uv run python scripts/test_optimize_literate_html.py
uv run python scripts/test_prepare_literate_site.py
```

Expected: the old open-all script and old breadcrumb selector fail.

- [ ] **Step 4: Implement the sidebar policy**

Change both navigation storage keys from `v7` to `v8`. Replace the unsaved
branch with:

```javascript
      } else {
        details.open = false;
      }
```

Keep current-page detection before the existing ancestor loop:

```javascript
    let parent = current?.closest("details");
    while (parent) {
      parent.open = true;
      parent = parent.parentElement?.closest("details");
    }
```

- [ ] **Step 5: Implement the breadcrumb policy**

Use this mobile CSS:

```css
    .breadcrumbs li:not(:first-child) {
        display: none;
    }

    .breadcrumbs li:not(:last-child)::after {
        display: none;
    }
```

- [ ] **Step 6: Verify and commit**

```bash
uv run python scripts/test_optimize_literate_html.py
uv run python scripts/test_prepare_literate_site.py
git diff --check
git add scripts/test_optimize_literate_html.py scripts/optimize_literate_html.py scripts/test_prepare_literate_site.py docs/literate/clrs-literate.css
git commit -m "fix(site): compact reader navigation defaults"
```

Expected: both suites pass.

### Task 4: Add the fourth-edition reader entry point

**Files:**
- Modify: `scripts/test_literate_config.py:68-95`
- Modify: `CLRSLean/FourthEdition.lean:37-48`

- [ ] **Step 1: Add a failing route-coverage test**

```python
    def test_fourth_edition_landing_links_every_reader_route(self) -> None:
        source = (ROOT / "CLRSLean" / "FourthEdition.lean").read_text(
            encoding="utf-8"
        )
        modules = [
            *(f"CLRSLean.FourthEdition.Chapter_{chapter:02d}" for chapter in range(1, 36)),
            "CLRSLean.Progress",
            "CLRSLean.Status",
            "CLRSLean.OnlineMaterial",
        ]
        for module in modules:
            with self.subTest(module=module):
                self.assertIn(f"]({module.replace('.', '/')}/)", source)
```

- [ ] **Step 2: Verify RED**

Run `uv run python scripts/test_literate_config.py`.

Expected: all 38 reader-route assertions fail.

- [ ] **Step 3: Expand the Literate docstring**

Keep the imports unchanged. Preserve the compatibility explanation under
`## Maintainer compatibility note`. Add Start Reading, Progress, Status, and
Online Material links, followed by these explicit chapter groups:

```markdown
## Foundations and sorting — Chapters 1--9

* [1](CLRSLean/FourthEdition/Chapter_01/), [2](CLRSLean/FourthEdition/Chapter_02/),
  [3](CLRSLean/FourthEdition/Chapter_03/), [4](CLRSLean/FourthEdition/Chapter_04/),
  [5](CLRSLean/FourthEdition/Chapter_05/), [6](CLRSLean/FourthEdition/Chapter_06/),
  [7](CLRSLean/FourthEdition/Chapter_07/), [8](CLRSLean/FourthEdition/Chapter_08/),
  [9](CLRSLean/FourthEdition/Chapter_09/).

## Data structures and design — Chapters 10--19

* [10](CLRSLean/FourthEdition/Chapter_10/), [11](CLRSLean/FourthEdition/Chapter_11/),
  [12](CLRSLean/FourthEdition/Chapter_12/), [13](CLRSLean/FourthEdition/Chapter_13/),
  [14](CLRSLean/FourthEdition/Chapter_14/), [15](CLRSLean/FourthEdition/Chapter_15/),
  [16](CLRSLean/FourthEdition/Chapter_16/), [17](CLRSLean/FourthEdition/Chapter_17/),
  [18](CLRSLean/FourthEdition/Chapter_18/), [19](CLRSLean/FourthEdition/Chapter_19/).

## Graphs and optimization — Chapters 20--29

* [20](CLRSLean/FourthEdition/Chapter_20/), [21](CLRSLean/FourthEdition/Chapter_21/),
  [22](CLRSLean/FourthEdition/Chapter_22/), [23](CLRSLean/FourthEdition/Chapter_23/),
  [24](CLRSLean/FourthEdition/Chapter_24/), [25](CLRSLean/FourthEdition/Chapter_25/),
  [26](CLRSLean/FourthEdition/Chapter_26/), [27](CLRSLean/FourthEdition/Chapter_27/),
  [28](CLRSLean/FourthEdition/Chapter_28/), [29](CLRSLean/FourthEdition/Chapter_29/).

## Advanced topics — Chapters 30--35

* [30](CLRSLean/FourthEdition/Chapter_30/), [31](CLRSLean/FourthEdition/Chapter_31/),
  [32](CLRSLean/FourthEdition/Chapter_32/), [33](CLRSLean/FourthEdition/Chapter_33/),
  [34](CLRSLean/FourthEdition/Chapter_34/), [35](CLRSLean/FourthEdition/Chapter_35/).
```

Use these exact links:

```markdown
[Progress Dashboard](CLRSLean/Progress/)
[Proof Status](CLRSLean/Status/)
[Online Material](CLRSLean/OnlineMaterial/)
```

Do not duplicate theorem counts.

- [ ] **Step 4: Verify and commit**

```bash
uv run python scripts/test_literate_config.py
lake env lean CLRSLean/FourthEdition.lean
git diff --check
git add scripts/test_literate_config.py CLRSLean/FourthEdition.lean
git commit -m "docs(site): add fourth-edition reader routes"
```

Expected: the route test and focused Lean compilation pass.

### Task 5: Run the bounded verification gate

**Files:**
- Verify all files changed in Tasks 1--4.

- [ ] **Step 1: Run focused suites**

```bash
uv run python scripts/test_check_edition_map.py
uv run python scripts/test_literate_config.py
uv run python scripts/test_optimize_literate_html.py
uv run python scripts/test_prepare_literate_site.py
```

Expected: all focused tests pass.

- [ ] **Step 2: Run repository-native checks**

```bash
uv run python scripts/check_repository.py
lake env lean CLRSLean/FourthEdition.lean
git diff --check
git status --short
```

Expected: repository checks and Lean pass, diff check is silent, and the tree is
clean after the four implementation commits.

### Task 6: Record excluded performance boundaries

**Files:**
- External: issues in `TankTechnology/CLRS-Lean`

- [ ] **Step 1: Check for duplicates**

Run:

```bash
gh issue list --repo TankTechnology/CLRS-Lean --state all --limit 200 --json number,title,url
```

Expected: neither performance boundary already has an equivalent issue.

- [ ] **Step 2: Create the search issue**

Run:

```bash
gh issue create --repo TankTechnology/CLRS-Lean \
  --title "site: avoid loading the full search index on every page" \
  --body '## Evidence

The deployed `_verso-search/searchIndex.js` is approximately 36 MB raw and
6.3 MB gzip, and it is referenced by ordinary reader pages.

## Boundary

Preserve Verso search semantics while preventing chapter navigation from
downloading and parsing the full index before the reader opens search.

## Acceptance

- Chapter pages do not request the full index during initial load.
- Search returns the same representative results.
- Desktop and 390-pixel mobile browser checks have no console errors.'
```

Expected: one new issue URL.

- [ ] **Step 3: Create the deployment issue**

Run:

```bash
gh issue create --repo TankTechnology/CLRS-Lean \
  --title "site: reduce full Pages build latency" \
  --body '## Evidence

The previous successful Pages run took approximately 2 hours 27 minutes; the
`lake build :literate` preparation step accounted for approximately 2 hours 2
minutes.

## Boundary

Keep immutable Literate JSON inputs and the sharded renderer while making
source-local changes reuse valid work across commits.

## Acceptance

- Cache identity contains every input that affects each reusable unit.
- A source-local change demonstrates a materially shorter successful Pages run.
- Fresh-cache behavior renders and validates every expected page.'
```

Expected: one new issue URL.

### Task 7: Fast-forward main, deploy, and verify live output

**Files:**
- Integrate: `codex/reader-site-consistency` into `main`
- External: `origin/main`, Pages workflow, deployed site

- [ ] **Step 1: Confirm clean ancestry**

```bash
git status --short --branch
git fetch origin
git merge-base --is-ancestor origin/main HEAD
```

Expected: clean tree and exit status 0.

- [ ] **Step 2: Fast-forward and recheck main**

```bash
git switch main
git merge --ff-only codex/reader-site-consistency
uv run python scripts/check_repository.py
lake env lean CLRSLean/FourthEdition.lean
```

Expected: fast-forward and both checks pass.

- [ ] **Step 3: Push and trigger Pages**

```bash
git push origin main
gh workflow run pages.yml --repo TankTechnology/CLRS-Lean --ref main
gh run list --repo TankTechnology/CLRS-Lean --workflow pages.yml --branch main --event workflow_dispatch --limit 1 --json databaseId,headSha,status,conclusion,url
```

Expected: the listed `headSha` equals `git rev-parse HEAD`.

- [ ] **Step 4: Monitor the exact run**

Run `gh run watch RUN_ID --repo TankTechnology/CLRS-Lean --exit-status` for the
ID from Step 3 and report meaningful workflow-stage changes.

Expected: prepare, four render shards, merge, and deploy succeed.

- [ ] **Step 5: Check all chapter routes and labels**

```bash
uv run python - <<'PY'
from urllib.request import urlopen
base = "https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition"
for chapter in range(1, 36):
    url = f"{base}/Chapter_{chapter:02d}/"
    with urlopen(url, timeout=30) as response:
        if response.status != 200:
            raise SystemExit(f"{url}: HTTP {response.status}")
print("35/35 fourth-edition chapter routes returned HTTP 200")
PY
curl -fsSL https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Progress/ | rg "470"
curl -fsSL https://tanktechnology.github.io/CLRS-Lean/CLRSLean/FourthEdition/Chapter_29/ | rg "29\.3\. Duality"
```

Additionally require no `Edmonds-Karp Algorithm (partial)` or
`Maximum Bipartite Matching (partial)` in the Chapter 24 page.

- [ ] **Step 6: Run clean-browser desktop/mobile checks**

Open root, Fourth Edition, Chapters 24, 29, and 34. At desktop width require only
the current branch and ancestors open. At 390 px require usable menu/search, no
intermediate `C` breadcrumb, no global horizontal overflow, and zero console
errors.

- [ ] **Step 7: Confirm final Git equality**

```bash
git status --short --branch
test "$(git rev-parse HEAD)" = "$(git rev-parse origin/main)"
```

Expected: clean `main` exactly equal to `origin/main`.
