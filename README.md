# CLRS-Lean

CLRS-Lean is a Lean 4 companion for the mathematical correctness arguments in
*Introduction to Algorithms*.  The repository is both a Lean library and a
book-style Verso site: chapter guides explain the formalization boundary, while
section modules contain executable definitions, theorem interfaces, and proofs.

- [Website](https://tanktechnology.github.io/CLRS-Lean/)
- [Generated progress dashboard](https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Progress/)
- [Reader-facing proof status](https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Status/)
- [Contributor workflow](https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Workflow/)
- [Documentation index](docs/index.md)

The public project name is `CLRS-Lean`.  Lean modules use the import-friendly
root `CLRSLean`.

## Proof Scope

The project formalizes selected CLRS sections, not every exercise or every line
of pseudocode.  A chapter may be complete for its current mathematical model
while still leaving pointer mutation, RAM costs, or imperative refinement for a
later layer.

Current milestones include:

- Chapter 2: insertion sort, merge sort, and selected comparison/recurrence
  results.
- Chapter 6: the current heap, `MAX-HEAPIFY`, `BUILD-MAX-HEAP`, heapsort, and
  priority-queue correctness stack.
- Chapter 8: correctness for the represented counting-sort, radix-sort, and
  bucket-sort models.
- Chapter 16: activity-selection and Huffman optimality for the represented
  finite models.
- Chapter 22: sealed main functional correctness for BFS shortest paths and its
  predecessor tree, DFS theory and edge classification, Kahn and DFS
  topological sorting, and Kosaraju SCC decomposition.

Chapters 3, 4, 7, 9, 11-15, 17-20, and 23 have substantial but intentionally
partial theorem layers.  Chapter 21 and Chapters 24-35 are not represented on
`main` yet.  The live counts and chapter rows are generated from
[`docs/clrs-proof-progress.csv`](docs/clrs-proof-progress.csv); see the
[`proof status board`](docs/proof-status-board.md) for the current scheduling
view and [`proof map`](docs/proof-map.md) for theorem-level detail.

## Repository Architecture

```text
CLRSLean.lean                     library root and website landing page
CLRSLean/Chapter_XX.lean          chapter guide and section aggregator
CLRSLean/Chapter_XX/Section_*.lean
                                  definitions, algorithms, and proofs
CLRSLean/ProofPatterns/           small reusable cross-chapter proof APIs
CLRSLean/Progress.lean            generated public progress dashboard
CLRSLean/Status.lean              concise reader-facing status page
CLRSLean/Workflow.lean            public contribution workflow
Tests/                            stable interface and closure checks
docs/                             maintainer ledgers, design notes, and audits
scripts/                          metadata, site, and repository checks
literate.toml                    Verso navigation and page titles
```

The detailed dependency and ownership rules are in
[`docs/repository-architecture.md`](docs/repository-architecture.md).

## Sources of Truth

| Question | Canonical source |
| --- | --- |
| What Lean modules exist? | `CLRSLean/`, checked against `literate.toml` |
| What is the public theorem interface? | Section `.lean` files and `Tests/` |
| What is the chapter-level progress snapshot? | `docs/clrs-proof-progress.csv` |
| What theorem names and proof boundaries exist? | `docs/proof-map.md` |
| What should be worked on next? | `docs/proof-status-board.md` |
| What is blocked or deliberately deferred? | `docs/status/blocked-and-deferred.md` |
| What appears on the website? | `CLRSLean.lean`, chapter guides, and `literate.toml` |

`CLRSLean/Progress.lean` is generated from the CSV.  It should never be edited
as an independent status ledger.

## Local Setup

Install Lean through [elan](https://github.com/leanprover/elan), then prepare
the repository:

```bash
git clone https://github.com/TankTechnology/CLRS-Lean.git
cd CLRS-Lean
lake exe cache get
uv sync --frozen
```

The Python helper environment is managed by `uv`; it currently has no runtime
dependencies beyond Python 3.11 or newer.

Build the Lean library:

```bash
lake build CLRSLean
```

Run the fast repository metadata and configuration checks:

```bash
uv run python scripts/check_repository.py
```

Build the public site when a reader-facing page or navigation entry changes:

```bash
lake build :literateHtml
```

For proof development, use the narrow-to-wide loop documented in
[`docs/workflows/lean-fast-verification.md`](docs/workflows/lean-fast-verification.md)
before running a full library build.

## Contribution Contract

A theorem-producing change should update code and status together:

1. Change the relevant section module and its focused interface test.
2. Update the chapter guide when the advertised theorem boundary changes.
3. Update `docs/clrs-proof-progress.csv` and `docs/proof-map.md` when coverage
   changes.
4. Regenerate the public dashboard:

   ```bash
   uv run python scripts/check_progress_csv.py --write-dashboard
   ```

5. Run `uv run python scripts/check_repository.py`.
6. Build the changed module, its immediate dependents, and finally
   `lake build CLRSLean` for a milestone or merge.

Status labels describe the proved model precisely:

- `main-proof-complete`: the advertised main theorem stack is complete.
- `main-proof-complete-for-correctness`: correctness is complete; explicit
  work/RAM refinements remain.
- `selected-section-complete`: the represented sections are complete, not the
  whole textbook chapter.
- `partial`: useful proofs exist, but a named central target remains.
- `not-started`: no represented section exists on `main`.
- `expository`: a guide page with no formal theorem target.

## Website Deployment

GitHub Actions builds the Verso HTML, checks freshness and rendering, optimizes
the generated pages, creates the sitemap, and deploys the result to GitHub
Pages.  Generated HTML is build output and is not committed to the repository.
