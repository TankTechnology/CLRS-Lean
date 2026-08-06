# Chapters 1--29 Milestone Audit

## 1. Decision

Date: 2026-08-05

Chapters 1--29 have completed their advertised proof scopes.  Across this
prefix, all 1,705 tracked theorem entries are kernel-checked and every chapter
row reports zero missing core groups within its stated boundary.

This is a proof-scope milestone, not a claim that every section, exercise,
chapter-end problem, mutable implementation, or RAM-cost refinement in the
textbook has been formalized.  The exact represented sections and optional
refinements remain recorded per chapter in `docs/clrs-proof-progress.csv`.

## 2. Status Distribution

| Status | Chapters | Count |
| --- | --- | ---: |
| `main-proof-complete` | 2, 3, 4, 6, 9, 16, 21, 26, 27, 28, 29 | 11 |
| `main-proof-complete-for-correctness` | 8, 11, 12, 13, 14, 18, 19, 20, 22, 23, 25 | 11 |
| `selected-section-complete` | 5, 7, 10, 15, 17, 24 | 6 |
| `expository` | 1 | 1 |

The six `selected-section-complete` rows deliberately claim completion only
for their represented sections.  Their boundaries are part of the milestone,
not hidden gaps in a stronger whole-chapter claim.

## 3. Source-of-Truth Contract

| Artifact | Responsibility |
| --- | --- |
| `docs/clrs-proof-progress.csv` | Canonical chapter counts, statuses, represented sections, and remaining work |
| `scripts/check_progress_csv.py` | Validates the ledger and generates the reader-facing progress dashboard |
| `CLRSLean/Progress.lean` | Generated full progress table and Chapters 1--29 aggregate |
| `CLRSLean/Status.lean` | Human-readable interpretation of the status labels and current milestone |
| `docs/proof-map.md` | Detailed theorem and proof-boundary ledger |
| `docs/proof-status-board.md` | Compact maintainer-facing milestone and priorities |
| `scripts/gen_readme_table.py` | Generates both the README milestone banner and chapter table |

The repository check runs the Progress generator with `--check-dashboard` and
the README generator with `--check`.  A future CSV change therefore cannot
silently leave either generated artifact with stale counts.

## 4. Verification Record

The milestone was verified with the following bounded checks and the complete
Verso site build required for deployment:

```bash
uv run python scripts/check_repository.py
lake build CLRSLean.Progress CLRSLean.Status
lake build :literateHtml
python3 scripts/check_literate_html_freshness.py <literate-output>
python3 scripts/prepare_literate_site.py <literate-output> _site \
  --base-url "https://tanktechnology.github.io/CLRS-Lean/"
git diff --check
```

All commands completed successfully.  The repository check confirmed 35
ledger rows, 1,747 tracked and proved entries across all represented chapters,
32 chapter-guide pages, 273 section files, and 317 literate modules.  The
Chapters 1--29 prefix accounts for 1,705 of those proved entries and zero
remaining core groups.  The larger repository total also includes represented
work after Chapter 29 and must not be confused with this prefix milestone.

## 5. Publication Boundary

The canonical public site is built by `.github/workflows/pages.yml` and
published through GitHub Pages at:

<https://tanktechnology.github.io/CLRS-Lean/>

Deployment remains manually dispatched.  This avoids an expensive full Verso
render on every push while still using the same `:literateHtml`, freshness,
and site-preparation path verified above.
