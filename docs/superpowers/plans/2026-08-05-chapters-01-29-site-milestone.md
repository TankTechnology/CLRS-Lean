# Chapters 1--29 Site Milestone Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Publish an accurate, automatically checked Chapters 1--29 milestone on the CLRS-Lean website.

**Architecture:** Keep `docs/clrs-proof-progress.csv` as the status source of truth. Generate the README milestone summary and chapter table from that CSV, render the same interpretation on the Lean landing/status pages, and preserve the repository's established Verso-to-GitHub-Pages deployment path.

**Tech Stack:** Python 3 standard library, Lean 4 literate documentation, Verso, GitHub Actions, GitHub Pages.

---

### Task 1: Seal the generated milestone summary

**Files:**
- Create: `scripts/test_gen_readme_table.py`
- Modify: `scripts/gen_readme_table.py`
- Modify: `README.md`
- Modify: `scripts/check_repository.py`

- [ ] Add a unit test requiring a generated Chapters 1--29 summary with a computed theorem total, zero missing groups, and an explicit selected-section boundary.
- [ ] Run `uv run python scripts/test_gen_readme_table.py`; expect failure because the milestone generator does not exist.
- [ ] Implement the smallest CSV-driven milestone renderer and register its `--check` command in repository checks.
- [ ] Regenerate README and rerun the unit test; expect all tests to pass.

### Task 2: Reconcile reader-facing status pages

**Files:**
- Modify: `CLRSLean.lean`
- Modify: `CLRSLean/Status.lean`
- Modify: `scripts/check_progress_csv.py`
- Modify: `scripts/test_check_progress_csv.py`

- [ ] Add a failing dashboard-render test for the Chapters 1--29 milestone totals and scope breakdown.
- [ ] Run `uv run python scripts/test_check_progress_csv.py`; expect the new assertion to fail.
- [ ] Generate the milestone section on `CLRSLean/Progress.lean` and replace stale landing-page claims with the current 1--29 boundary.
- [ ] Regenerate the dashboard and rerun focused Python tests.

### Task 3: Record the audit and navigation entry

**Files:**
- Create: `docs/proof-audits/chapters-01-29-milestone-2026-08-05.md`
- Modify: `docs/index.md`

- [ ] Record the 29-chapter status split, 1,705 proved entries, zero missing groups inside the advertised scopes, and the distinction between whole-chapter and selected-section completion.
- [ ] Link the audit from the documentation index.
- [ ] Run repository metadata and Markdown-link checks.

### Task 4: Build and publish the site

**Files:**
- Verify: `.github/workflows/pages.yml`
- Verify: generated Verso output and `_site/`

- [ ] Run `lake build :literateHtml` because this is a deployment milestone.
- [ ] Run the freshness check and `scripts/prepare_literate_site.py` with the production base URL.
- [ ] Verify the generated homepage, progress page, status page, sitemap, and absence of stale 1--26 milestone text.
- [ ] Commit, push, open and merge a PR, dispatch the Pages workflow on `main`, and wait for a successful deployment.
- [ ] Verify the public website returns the new Chapters 1--29 milestone content.
