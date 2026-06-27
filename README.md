# CLRS-Lean

`CLRS-Lean` is a Lean 4 companion project for CLRS-style algorithm
correctness proofs.  The project is organized as a chapter-by-chapter online
book: each represented CLRS chapter has a guide page, selected sections have
literate Lean proof pages, and the site includes public progress and proof
status ledgers.

- Website: <https://tanktechnology.github.io/CLRS-Lean/>
- Progress dashboard: <https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Progress/>
- Proof status ledger: <https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Status/>
- Workflow guide: <https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Workflow/>
- Sitemap: <https://tanktechnology.github.io/CLRS-Lean/sitemap.xml>

The public project name is `CLRS-Lean`.  The Lean library root remains
`CLRSLean`, because Lean module names and import paths should be simple
identifiers.

## Current Scope

The repository currently represents a growing subset of CLRS.  The public
progress dashboard is generated from `docs/clrs-proof-progress.csv`; at the
current snapshot it tracks 35 CLRS chapters, 21 represented Lean chapters, and
816 proved reader-facing theorem entries.

Highlights include:

- Chapter 2: insertion sort, merge sort, and recurrence/cost wrappers.
- Chapter 4: maximum subarray, Strassen 2 by 2 algebra, recursion trees, and
  substantial Master-theorem infrastructure.
- Chapter 6: heaps, `MAX-HEAPIFY`, `BUILD-MAX-HEAP`, heapsort, and priority
  queue operations for the current array/functional models.
- Chapters 7-9: quicksort, linear-time sorting, and selection theorem layers,
  including deterministic median-of-medians correctness and recurrence bounds.
- Chapters 10-15: selected data-structure and dynamic-programming models,
  including BSTs, red-black-tree local certificates, order-statistic trees, rod
  cutting, matrix-chain multiplication, and LCS.
- Chapter 16: activity selection and Huffman coding.
- Chapters 17-20 and 23: first-pass amortized-analysis, B-tree, Fibonacci-heap,
  vEB, and MST theorem surfaces.

See `docs/proof-map.md` for the detailed theorem-by-theorem map and
`docs/proof-status-board.md` for the high-level planning board.

## Repository Layout

Lean source files follow CLRS chapter and section numbers:

```text
CLRSLean.lean
CLRSLean/Chapter_02.lean
CLRSLean/Chapter_02/Section_02_1_Insertion_Sort.lean
CLRSLean/Chapter_06/Section_06_4_Heapsort.lean
CLRSLean/Chapter_09/Section_09_3_Deterministic_Select.lean
CLRSLean/Chapter_15/Section_15_1_Rod_Cutting.lean
CLRSLean/Chapter_16/Section_16_3_Huffman_Codes.lean
CLRSLean/Chapter_23/Section_23_2_Kruskal_And_Prim.lean
CLRSLean/Progress.lean
CLRSLean/Status.lean
CLRSLean/Workflow.lean
```

Maintainer-facing documents live under `docs/`:

```text
docs/clrs-proof-progress.csv
docs/proof-map.md
docs/proof-status-board.md
docs/site-architecture.md
docs/workflows/chapter-workflow.md
docs/status/blocked-and-deferred.md
```

Website and deployment helpers live in:

```text
literate.toml
docs/literate/clrs-literate.css
scripts/optimize_literate_html.py
scripts/generate_sitemap.py
.github/workflows/pages.yml
```

## Build

Build and verify the Lean library:

```bash
lake build CLRSLean
```

Generate the Verso literate HTML site locally:

```bash
lake build :literateHtml
```

Run the repository consistency checks used before website changes:

```bash
python3 scripts/check_progress_csv.py
python3 scripts/test_literate_config.py
python3 scripts/test_optimize_literate_html.py
python3 scripts/check_literate_html_freshness.py .lake/build/literate-html
```

Generate a sitemap for a built site directory:

```bash
python3 scripts/generate_sitemap.py .lake/build/literate-html \
  --base-url "https://tanktechnology.github.io/CLRS-Lean/"
```

## Website Deployment

GitHub Actions builds the Verso site and deploys the generated `_site` artifact
to GitHub Pages.  During deployment it:

1. Builds the literate HTML with `lake query :literateHtml`.
2. Checks generated-page freshness.
3. Copies the generated pages into `_site`.
4. Optimizes generated HTML for faster reading.
5. Generates `_site/sitemap.xml`.
6. Uploads the Pages artifact.

The generated sitemap is meant to be submitted in Google Search Console as:

```text
https://tanktechnology.github.io/CLRS-Lean/sitemap.xml
```

The generated HTML also includes the configured Google site-verification meta
tag in the page `<head>` section.

## Contribution Rule

Every theorem-producing change should keep the proof ledger synchronized:

1. Update the relevant Lean files.
2. Update `docs/clrs-proof-progress.csv` when reader-facing theorem groups
   change.
3. Regenerate `CLRSLean/Progress.lean` with:

   ```bash
   python3 scripts/check_progress_csv.py --write-dashboard
   ```

4. Run `lake build CLRSLean` and the relevant site checks before submitting.
