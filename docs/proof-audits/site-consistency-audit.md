# Site Structure Consistency Audit

This document records how the CLRS-Lean website is organized, what is currently
consistent, and what structural inconsistencies should be fixed.

---

## 1. Intended Architecture

Per `docs/site-architecture.md`, the public site is built from Lean sources as a
book-style Verso site:

```text
CLRSLean.lean                         project landing page
CLRSLean/Chapter_XX.lean              chapter guide page
CLRSLean/Chapter_XX/Section_XX_Y.lean section-level literate proof
CLRSLean/Status.lean                  public proof-status ledger
CLRSLean/Progress.lean                progress dashboard
CLRSLean/Workflow.lean                contributor workflow
literate.toml                         sidebar order and page titles
```

The build path is:

```text
Lean source -> lake build -> lake build :literateHtml
             -> scripts/optimize_literate_html.py -> _site -> GitHub Pages
```

---

## 2. What Is Consistent

- **Landing page**: `CLRSLean.lean` imports all represented chapters and gives a
  high-level overview.
- **Chapter guides**: every represented chapter has a `CLRSLean/Chapter_XX.lean`
  with a module doc listing status and main results.
- **Section files**: every represented section has a `.lean` file with a module
  doc, public theorems, and proofs.
- **Sidebar order**: `literate.toml` lists all represented chapters and sections.
- **Module titles**: every chapter and section module has a `[modules."..."]`
  title entry in `literate.toml`.
- **Status board**: `CLRSLean/Status.lean` mirrors the high-level buckets from
  `docs/proof-status-board.md`.

---

## 3. Inconsistencies Found

### 3.1 `docs/chapters/chapter-XX.md` Pages Are Ad Hoc

Some chapters have extra Markdown narrative pages under `docs/chapters/`:

- Present: 2, 6, 7, 8, 9, 16, 17, 18, 19, 20, 23
- Missing: 1, 3, 4, 5, 10, 11, 12, 13, 14, 15

These Markdown pages are **not referenced in `docs/site-architecture.md`** and
are not listed in `literate.toml`. It is unclear whether they are:

- legacy content that should be removed;
- optional deep-dive pages that should be linked from chapter guides;
- or a duplicate maintenance surface that has drifted from the `.lean` guides.

**Recommendation**: decide on one of the following and apply it globally:

1. **Remove `docs/chapters/` entirely** and rely on `CLRSLean/Chapter_XX.lean`
   module docs as the only chapter guides. This minimizes maintenance.
2. **Keep `docs/chapters/` as canonical deep-dive pages** and create missing
   pages for 1, 3, 4, 5, 10, 11, 12, 13, 14, 15. Also update
   `docs/site-architecture.md` and the chapter guides to link to them.
3. **Auto-generate `docs/chapters/` from the `.lean` guides** during the build,
   eliminating drift.

Current best fit for the project: option 1 (remove or archive) because the
`.lean` module docs already serve the same purpose and are compiled alongside the
proofs.

### 3.2 Section Ordering Anomalies

- **Chapter 8**: `literate.toml` orders `Section_08_2_Counting_Sort` before
  `Section_08_2_Counting_Sort_Array`. The natural textbook order is 8.2 counting
  sort, with the array refinement as a subsection. This is acceptable but should
  be intentional.
- **Chapter 17**: the order is `Framework`, `Stack_And_Counter`, `Dynamic_Tables`.
  The framework module title is "17.1-17.3. Amortized Analysis Framework", which
  overlaps with the stack/counter section. This is confusing for readers.

**Recommendation**: review Chapter 17 `literate.toml` ordering and titles to
match the textbook sections exactly.

### 3.3 Missing Chapters in Navigation

Chapters 21, 22, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35 have no
`CLRSLean/Chapter_XX.lean` file and no `literate.toml` entry. They are correctly
absent from the sidebar because they are not started, but there is no placeholder
page telling readers they are future work.

**Recommendation**: either add a single "Future Chapters" note to
`CLRSLean/Status.lean` or create minimal `CLRSLean/Chapter_XX.lean` files for the
not-started chapters that say "not yet represented".

### 3.4 Status Sources Can Drift

There are at least three places where chapter status is recorded:

1. `docs/clrs-proof-progress.csv`
2. `docs/proof-status-board.md`
3. `CLRSLean/Status.lean`

These can become inconsistent. For example, after Chapter 13 RB-INSERT was
completed, the CSV and `proof-status-board.md` still list the full insertion
composition as a gap.

**Recommendation**: designate one source of truth. The CSV is machine-readable;
the website status page should be generated from it, or at least a CI check
should fail if the three sources disagree.

---

## 4. Recommended Automated Checks

Add a script `scripts/check_site_consistency.py` that verifies:

- [ ] Every `CLRSLean/Chapter_XX.lean` with a `Chapter_XX/` directory has an
      `[order_children]` entry in `literate.toml`.
- [ ] Every section file has a `[modules."..."]` title in `literate.toml`.
- [ ] `literate.toml` does not list files that do not exist.
- [ ] Every represented chapter appears in `CLRSLean.lean` imports.
- [ ] Every represented chapter has a non-empty module doc.
- [ ] `docs/clrs-proof-progress.csv`, `docs/proof-status-board.md`, and
      `CLRSLean/Status.lean` agree on chapter status labels.

Run this script in CI before deploying the site.

---

## 5. Conclusion

The website is structurally sound: the Lean source is the single source of truth
for proofs and section pages, and `literate.toml` correctly drives the sidebar.
The main cleanup work is:

1. Resolve the role of `docs/chapters/` Markdown pages.
2. Align Chapter 17 ordering/titles with the textbook.
3. Add a consistency check to keep status sources in sync.
4. Consider adding placeholders for not-started chapters so readers know the
   book is incomplete rather than missing.
