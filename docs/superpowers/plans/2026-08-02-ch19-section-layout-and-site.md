# Chapter 19 Section Layout and Site Deployment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Reorganize the completed Chapter 19 implementation into canonical textbook section modules without breaking old imports, then build and deploy the updated Verso site.

**Architecture:** Move the three theorem-bearing S1/S2/S3 files to 19.2, 19.3, and a 19.3 amortized-cost child module. Leave documented compatibility imports at the old paths. Make canonical modules reader-visible through the chapter aggregator and `literate.toml`, while retaining the same namespaces and theorem declarations.

**Tech Stack:** Lean 4, Lake, Verso literate HTML, Python repository/site checks, GitHub Actions Pages.

---

### Task 1: Specify the canonical module and navigation surface

**Files:**
- Modify: `Tests/Chapter_19_Interface.lean`
- Create: `Tests/Chapter_19_Legacy_Imports.lean`
- Modify: `scripts/test_literate_config.py`

- [ ] **Step 1: Change the main interface imports to canonical modules**

```lean
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model
import CLRSLean.Chapter_19.Section_19_2_Mergeable_Heap_Operations
import CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node
import CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.Amortized_Costs
import CLRSLean.Chapter_19.Section_19_4_Bounding_Maximum_Degree
```

- [ ] **Step 2: Add a legacy-import compile test**

```lean
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts
import CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts

#check CLRS.Chapter19.FH.extractMin_correct
#check CLRS.Chapter19.FH.cascadingCutRaw_correct
#check CLRS.Chapter19.FH.Costed.run_amortized_le_bound
```

- [ ] **Step 3: Extend the literate-config test with the four direct section modules and the amortized-cost child**

Add these entries to `test_support_pages_are_nested`:

```python
"CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model": [
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S1_ExecutableFibHeap",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S2_CascadingCuts",
    "CLRSLean.Chapter_19.Section_19_1_Fibonacci_Heap_Model.S3_AmortizedCosts",
],
"CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node": [
    "CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.Amortized_Costs",
],
```

The chapter-import ordering test will additionally require the Chapter 19
direct-child order `19.1`, `19.2`, `19.3`, `19.3.Amortized_Costs`, `19.4` once
the aggregator imports canonical modules.

- [ ] **Step 4: Run the tests and observe the expected red state**

Run:

```bash
lake env lean Tests/Chapter_19_Interface.lean
uv run python -m unittest scripts.test_literate_config
```

Expected: failure because the canonical 19.2/19.3 Lean modules and navigation
entries do not exist yet.

### Task 2: Move theorem-bearing modules and preserve legacy imports

**Files:**
- Create: `CLRSLean/Chapter_19/Section_19_2_Mergeable_Heap_Operations.lean`
- Create: `CLRSLean/Chapter_19/Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.lean`
- Create: `CLRSLean/Chapter_19/Section_19_3_Decreasing_A_Key_And_Deleting_A_Node/Amortized_Costs.lean`
- Modify: the three old S1/S2/S3 files into compatibility imports

- [ ] **Step 1: Move S1 to the canonical Section 19.2 path**

Preserve all declarations and update its heading/import description.  Replace
the old S1 file with:

```lean
import CLRSLean.Chapter_19.Section_19_2_Mergeable_Heap_Operations

/-!
# Chapter 19 legacy import: executable mergeable-heap operations

This module preserves the pre-section-layout import path.
-/
```

- [ ] **Step 2: Move S2 to the canonical Section 19.3 path**

Change its dependency to Section 19.2 and replace the old S2 file with a
documented import of the canonical Section 19.3 module.

- [ ] **Step 3: Move S3 below Section 19.3**

Change its dependency to the canonical Section 19.3 parent and replace the old
S3 file with a documented import of the canonical amortized-cost module.

- [ ] **Step 4: Compile canonical and legacy module surfaces**

Run:

```bash
lake build CLRSLean.Chapter_19.Section_19_3_Decreasing_A_Key_And_Deleting_A_Node.Amortized_Costs
lake env lean Tests/Chapter_19_Interface.lean
lake env lean Tests/Chapter_19_Legacy_Imports.lean
```

Expected: all commands exit successfully; existing linter warnings are allowed.

### Task 3: Wire the chapter and website navigation

**Files:**
- Modify: `CLRSLean/Chapter_19.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/chapters/chapter-19.md`
- Modify: `docs/proof-map.md`
- Modify: `docs/clrs-proof-progress.csv`
- Regenerate: `CLRSLean/Progress.lean`

- [ ] **Step 1: Import canonical modules from the chapter aggregator**

Remove direct S1/S2/S3 imports and import 19.2, 19.3, and the amortized-cost
child instead.

- [ ] **Step 2: Register the canonical navigation tree and titles**

Make the four textbook sections direct Chapter 19 children.  Register the
three compatibility modules under 19.1 and the amortized-cost module under
19.3 so every source remains represented.

- [ ] **Step 3: Replace old source paths in reader and maintainer docs**

Describe the legacy modules only as compatibility paths.  Change the CSV
represented sections to `19.1;19.2;19.3;19.4` without changing its 214/214
theorem count.

- [ ] **Step 4: Regenerate the progress dashboard and verify metadata**

Run:

```bash
uv run python scripts/check_progress_csv.py --write-dashboard
uv run python scripts/check_site_consistency.py
uv run python -m unittest scripts.test_literate_config
```

Expected: 35 chapters, 1638/1638 tracked entries, and a consistent site tree.

### Task 4: Verify and commit the source reorganization

**Files:** all files from Tasks 1--3.

- [ ] **Step 1: Run focused Lean verification**

```bash
lake env lean Tests/Chapter_19_Interface.lean
lake env lean Tests/Chapter_19_Legacy_Imports.lean
lake env lean CLRSLean/Chapter_19.lean
```

- [ ] **Step 2: Run repository hygiene checks**

```bash
rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_19 Tests/Chapter_19_Interface.lean Tests/Chapter_19_Legacy_Imports.lean
uv run python scripts/check_repository.py
git diff --check
```

- [ ] **Step 3: Commit the reorganization**

```bash
git add CLRSLean Tests literate.toml docs scripts/test_literate_config.py
git commit -m "refactor(ch19): align modules with textbook sections"
```

### Task 5: Build, merge, and deploy the website

**Files:** generated output only; do not commit `.lake/build/literate-html` or `_site`.

- [ ] **Step 1: Build the complete Verso site**

```bash
lake build :literateHtml
```

- [ ] **Step 2: Assemble and validate the deployable site**

```bash
VERSO_OUT="$(lake query :literateHtml)"
python3 scripts/check_literate_html_freshness.py "$VERSO_OUT"
python3 scripts/prepare_literate_site.py "$VERSO_OUT" _site --base-url "https://tanktechnology.github.io/CLRS-Lean/"
```

- [ ] **Step 3: Push, create a PR, and merge it into `main`**

Use the GitHub CLI, preserving the source commits.  Confirm the merged commit is
present in `origin/main`.

- [ ] **Step 4: Dispatch and monitor the Pages workflow**

```bash
gh workflow run pages.yml --ref main
gh run watch <run-id> --exit-status
```

Expected: both build and deploy jobs succeed and the deployment reports the
GitHub Pages URL.
