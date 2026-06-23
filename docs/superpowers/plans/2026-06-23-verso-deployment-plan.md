# Verso Deployment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Migrate CLRSLean from hand-written static HTML to Verso literate programming — same book-quality web rendering as `teorth/analysis`.

**Architecture:** Convert `lakefile.toml` to `lakefile.lean` with `doc.verso` option and Verso dependency, create `literate.toml` for section ordering, update `.lean` files with Verso-compatible `/-!` module doc blocks, replace static HTML in `docs/site/` with Verso-generated `_site/`, update CI to build and deploy literate HTML.

**Tech Stack:** Lean 4.29.1, Mathlib v4.29.1, Verso `main`, doc-gen4 `main`, GitHub Actions, GitHub Pages.

---

## File Structure

| File | Action | Purpose |
|------|--------|---------|
| `lakefile.lean` | Create | Lean DSL build config with Verso |
| `lakefile.toml` | Delete | Replaced by lakefile.lean |
| `literate.toml` | Create | Verso module ordering + titles |
| `CLRSLean.lean` | Rewrite | Verso landing page |
| `CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean` | Update | Add `namespace CLRS` layer |
| `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean` | Update | Wrap in `namespace CLRS` |
| `.github/workflows/pages.yml` | Rewrite | Add Verso build steps |
| `docs/site/` | Delete | Replaced by Verso output |

No changes needed for Chapter 23 files — they already have `namespace CLRS.MST` and `/-!` blocks.

---

### Task 1: Create lakefile.lean

**Files:**
- Create: `lakefile.lean`
- Delete: `lakefile.toml`

- [ ] **Step 1: Delete lakefile.toml**

```bash
rm lakefile.toml
```

- [ ] **Step 2: Create lakefile.lean**

Write `lakefile.lean`:

```lean
import Lake
open Lake DSL

package «clrs-lean» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`doc.verso, true⟩
  ]
  moreLeanArgs := #[
    "-Dwarn.sorry=false"
  ]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

require verso from git
  "https://github.com/leanprover/verso" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «CLRSLean» where
```

- [ ] **Step 3: Update lake-manifest.json**

```bash
lake update
```

Expected: downloads Verso and doc-gen4 dependencies, updates manifest.  May take several minutes.

- [ ] **Step 4: Verify lake build**

```bash
lake build
```

Expected: all Lean files compile successfully (exit code 0).

- [ ] **Step 5: Commit**

```bash
git add lakefile.lean lake-manifest.json && git rm lakefile.toml
git commit -m "feat: convert lakefile.toml to lakefile.lean with Verso support

Add doc.verso option, Verso and doc-gen4 dependencies.

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

### Task 2: Create literate.toml

**Files:**
- Create: `literate.toml`

- [ ] **Step 1: Create literate.toml**

```toml
landing_page = "CLRSLean"

[order_children]
"CLRSLean" = [
  "CLRSLean.Chapter_02.Section_02_1_Insertion_Sort",
  "CLRSLean.Chapter_16.Section_16_3_Huffman_Codes",
  "CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees",
  "CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim",
]

[modules."CLRSLean.Chapter_02.Section_02_1_Insertion_Sort"]
title = "2.1. Insertion Sort"

[modules."CLRSLean.Chapter_16.Section_16_3_Huffman_Codes"]
title = "16.3. Huffman Codes"

[modules."CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees"]
title = "23.1. Growing a Minimum Spanning Tree"

[modules."CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim"]
title = "23.2. Kruskal and Prim"
```

- [ ] **Step 2: Commit**

```bash
git add literate.toml
git commit -m "feat: add literate.toml for Verso section ordering

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

### Task 3: Rewrite CLRSLean.lean as Verso landing page

**Files:**
- Modify: `CLRSLean.lean`

- [ ] **Step 1: Rewrite CLRSLean.lean**

The current file has imports for files that don't exist yet (Section_02_2, Section_02_3).  Replace with only existing modules plus a `/-!` landing-page doc block:

```lean
import CLRSLean.Chapter_02.Section_02_1_Insertion_Sort
import CLRSLean.Chapter_16.Section_16_3_Huffman_Codes
import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees
import CLRSLean.Chapter_23.Section_23_2_Kruskal_And_Prim

/-!
# CLRS-lean

A Lean 4 companion for *Introduction to Algorithms* (CLRS), formalizing
algorithm correctness proofs chapter by chapter.

## What is this?

Each section in CLRS that presents an algorithm proof is rendered as a
standalone Lean module.  The proofs are faithful to the textbook arguments
but expressed in Lean's dependent type theory, using Mathlib for
mathematical infrastructure.

## Proof status

| Chapter | Section | Status |
|---------|---------|--------|
| 2 | 2.1 Insertion Sort | ✅ proved |
| 16 | 16.3 Huffman Codes | ✅ proved |
| 23 | 23.1 Growing an MST | ⚠️ partial |
| 23 | 23.2 Kruskal and Prim | ⚠️ partial |

## Conventions

- **Zero-indexed**: sequences and lists use 0-based indexing for Mathlib compatibility
- **Total functions**: partial operations return junk values rather than `Option`
- **Unfinished proofs**: marked with `sorry` and an explanatory comment
- **Module = section**: one `.lean` file per CLRS section, rendered as one web page

## Build

```bash
lake build
lake build :literateHtml   # → _site/
```

## Repository

[https://github.com/TankTechnology/CLRSLean](https://github.com/TankTechnology/CLRSLean)
-/
```

- [ ] **Step 2: Verify lake build still passes**

```bash
lake build
```

Expected: exit code 0.

- [ ] **Step 3: Commit**

```bash
git add CLRSLean.lean
git commit -m "feat: rewrite CLRSLean.lean as Verso landing page

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

### Task 4: Wrap Chapter 16 in namespace CLRS

**Files:**
- Modify: `CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean`

- [ ] **Step 1: Add opening namespace CLRS after the /-! block**

The file currently starts:
```lean
import Mathlib

set_option linter.unusedSimpArgs false
...
/-!
# CLRS Section 16.3 - Huffman codes
...
-/

open List

namespace HuffmanV2
```

Change to:
```lean
import Mathlib

set_option linter.unusedSimpArgs false
...
/-!
# CLRS Section 16.3 - Huffman codes
...
-/

open List

namespace CLRS
namespace HuffmanV2
```

Edit: insert `namespace CLRS` on a new line before `namespace HuffmanV2`.

- [ ] **Step 2: Add closing end CLRS**

The file currently ends:
```lean
end HuffmanV2
```

Change to:
```lean
end HuffmanV2
end CLRS
```

- [ ] **Step 3: Verify lake build**

```bash
lake build
```

Expected: exit code 0.  The fully-qualified name is now `CLRS.HuffmanV2.optimum_huffman_freqs` — since nothing outside this file references it by qualified name, this is safe.

- [ ] **Step 4: Commit**

```bash
git add CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
git commit -m "refactor: wrap HuffmanV2 in namespace CLRS for consistency

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

### Task 5: Update pages.yml with Verso build steps

**Files:**
- Modify: `.github/workflows/pages.yml`

- [ ] **Step 1: Rewrite pages.yml**

Replace the entire file content:

```yaml
name: Build and deploy Verso site

on:
  push:
    branches: [main]
  workflow_dispatch:

permissions:
  contents: read
  pages: write
  id-token: write

concurrency:
  group: pages
  cancel-in-progress: true

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - uses: leanprover/lean-action@v1
        with:
          build: false
          test: false
          use-mathlib-cache: true

      - name: Build project
        run: lake build

      - name: Build doc-gen4 docs
        run: lake -R -Kenv=dev build CLRSLean:docs

      - name: Build Verso literate HTML
        run: lake build :literateHtml

      - name: Assemble _site
        run: |
          VERSO_OUT=$(lake query :literateHtml)
          echo "Verso output: $VERSO_OUT"
          mkdir -p _site
          cp -r "$VERSO_OUT"/* _site/
          cp -r .lake/build/doc _site/docs 2>/dev/null || echo "No doc-gen4 output"

      - uses: actions/upload-pages-artifact@v3
        with:
          path: _site

  deploy:
    needs: build
    if: github.ref == 'refs/heads/main'
    environment:
      name: github-pages
      url: ${{ steps.deployment.outputs.page_url }}
    runs-on: ubuntu-latest
    steps:
      - id: deployment
        uses: actions/deploy-pages@v4
```

- [ ] **Step 2: Commit**

```bash
git add .github/workflows/pages.yml
git commit -m "feat: add Verso literate HTML build to Pages workflow

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

### Task 6: Remove old static HTML

**Files:**
- Delete: `docs/site/` (entire directory)

- [ ] **Step 1: Remove the old static site**

```bash
git rm -r docs/site/
```

- [ ] **Step 2: Commit**

```bash
git commit -m "chore: remove old static HTML site (replaced by Verso)

Co-Authored-By: Claude <noreply@anthropic.com>"
```

---

### Task 7: Local end-to-end verification

- [ ] **Step 1: Clean build from scratch**

```bash
lake clean && lake build
```

Expected: all modules compile, exit code 0.

- [ ] **Step 2: Build Verso literate HTML**

```bash
lake build :literateHtml
```

Expected: exit code 0, Generates `_site/` directory.

- [ ] **Step 3: Verify _site/ contents**

```bash
ls -la _site/
```

Expected: contains `index.html` (landing page) and subdirectories for each section.

- [ ] **Step 4: Inspect a rendered page**

```bash
head -50 _site/index.html
```

Expected: valid HTML with CLRSLean title and navigation.

---

### Task 8: Push and verify remote deployment

- [ ] **Step 1: Push everything**

```bash
git push
```

- [ ] **Step 2: Watch CI runs**

```bash
sleep 30 && gh run list --repo TankTechnology/CLRSLean --limit 5
```

Expected: `Build and deploy Verso site` workflow queued or running.

- [ ] **Step 3: Wait for deploy to complete**

```bash
# Check periodically (~2-3 minutes)
gh run list --repo TankTechnology/CLRSLean --limit 5
```

Expected: `Build and deploy Verso site` → `completed success`.

- [ ] **Step 4: Verify live site**

```bash
curl -s -o /dev/null -w "%{http_code}" https://tanktechnology.github.io/CLRSLean/
```

Expected: `200`.

- [ ] **Step 5: Verify page content**

Visit `https://tanktechnology.github.io/CLRSLean/` and confirm:
- Landing page shows project title, status table, conventions
- Section pages are navigable (prev/next)
- Chapter 2.1, 16.3, 23.1, 23.2 each have their own page
- Math expressions render correctly
