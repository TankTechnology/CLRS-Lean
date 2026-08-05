# CLRS fourth-edition migration and sharded publishing audit

Date: 2026-08-06  
Branch: `codex/clrs4-primary-migration`  
Audited implementation commit: `6129526`

## Outcome

The repository and generated book now use the 35-chapter CLRS fourth-edition
tree as their canonical reader-facing structure. All 35 canonical guide modules
exist below `CLRSLean.FourthEdition`; 30 chapters have represented content,
including the expository Chapter 1 guide, and Chapters 25, 27, 33, 34, and 35
are explicitly recorded as not started.

This is a structural and accounting migration, not a claim that every reused
source development already covers every fourth-edition theorem obligation.
`docs/clrs-fourth-edition-map.csv` records the represented sections, source
modules, migration state, and known gaps. New fourth-edition chapter content is
the next formalization phase.

The old `CLRSLean.Chapter_*` imports and declaration namespaces remain working
as a compatibility layer. Removal requires all `1.x` releases to have ended,
at least six calendar months to have elapsed since the first release containing
the facades, a `2.0` or later release, and the per-prefix migration gates in
`docs/migrations/clrs4.md`. The layer is transitional and is intended to be
removed once those gates pass.

## Disjoint progress ledgers

The canonical fourth-edition ledger contains 1,326 tracked theorem groups, all
currently proved. The online/supplementary ledger contains 467 groups across 11
topics. These ledgers are disjoint:

- 421 online entries come from the wholly excluded third-edition Fibonacci
  heaps, van Emde Boas trees, and computational-geometry chapters;
- 46 online entries come from moved maximum-subarray, perfect-hashing,
  matroid, task-scheduling, detailed SIMPLEX, iterative-FFT, and
  integer-factorization developments; and
- the 46 moved groups were removed from the affected canonical chapter totals.

`docs/clrs-proof-progress.csv` owns the canonical counts and
`docs/clrs-online-material.csv` owns the supplementary counts. The edition-map
validator requires every online umbrella import to be cataloged and requires
the online map and theorem ledger to agree.

## Publishing design

The manually dispatched Pages workflow now separates preparation, four
parallel render jobs, validated merge, optimization, and deployment. Every
renderer receives the complete immutable module graph but emits a disjoint
module assignment. This preserves cross-references while allowing the expensive
render stage to run concurrently on four CI runners.

The preparation step restores and incrementally updates literate JSON, removes
cached JSON whose Lean source no longer exists, creates a deterministic
content-digested module map, and balances chapter-affine shards by input size.
The merge rejects digest drift, missing or unexpected shard records, duplicate
assignments, missing or unexpected actual module pages, unequal file
collisions, and unequal metadata keys before atomically replacing its output.
The serial `lake build :literateHtml` path remains a diagnostic fallback.

Rendering checks run after sidebar pruning and site optimization. Hidden legacy
implementation pages must be transitively reachable from their visible
fourth-edition or online-material parent. When such a page is opened directly,
the sidebar marks that visible parent as current.

## Measured local validation

The measurements below were taken in the migration worktree on the same host.
They validate the implementation but do not predict GitHub-hosted runner time.

| Stage | Result |
| --- | --- |
| Literate JSON build | 378 modules; 9,536 Lake jobs; 13.87 s incremental wall time |
| Planned shard input sizes | 81,615,909; 82,105,102; 81,616,412; 81,856,414 bytes |
| Maximum planned skew | 489,193 bytes |
| Shard 0 | 78 modules; 61,665,579 output bytes; 12.027 s |
| Shard 1 | 43 modules; 34,736,913 output bytes; 11.017 s |
| Shard 2 | 196 modules; 57,021,744 output bytes; 12.587 s |
| Shard 3 | 61 modules; 39,305,826 output bytes; 11.458 s |
| Four-job local wall time | 12.65 s |
| Serial reference wall time | 22.66 s |
| Local render-stage speedup | 1.79x |
| Validated atomic merge | 0.41 s |
| Optimized site assembly | 18.26 s |

The serial and merged outputs each contained 665 files and exactly the same 378
module `index.html` paths: zero missing and zero extra. The merged raw output
contained 380 HTML pages, occupied 197,985,343 bytes, and had a largest HTML
page of 4,850,166 bytes. The optimized site contained 380 HTML pages and 380
sitemap URLs, occupied 137,729,060 bytes, and had a largest HTML page of
2,754,431 bytes. A direct legacy Chapter 22 page correctly marked canonical
fourth-edition Chapter 20 as the current sidebar entry.

## Verification evidence

The following gates passed on the audited branch:

```text
uv run python scripts/check_repository.py
lake build +CLRSLean.OnlineMaterial +CLRSLean.FourthEdition +CLRSLean.Progress +CLRSLean.Status
lake env lean Tests/FourthEdition_Compatibility.lean
lake build CLRSLean
lake build verso-literate-html
lake build :literate
python3 scripts/prepare_literate_module_map.py ... --prune-orphans
python3 scripts/plan_literate_shards.py ... --shards 4
python3 scripts/render_literate_shards.py ... --jobs 4
python3 scripts/merge_literate_shards.py ...
python3 scripts/check_literate_html_weight.py ...
python3 scripts/check_literate_html_freshness.py ...
python3 scripts/prepare_literate_site.py ...
python3 scripts/check_literate_rendering.py ...
git diff --check main...HEAD
```

The full Lean build completed successfully with 8,958 jobs. Existing Verso
role-specificity and Lean linter warnings remain warnings; no new proof
placeholder or build failure was accepted. No Pages deployment, push, merge,
or release was performed as part of this local audit.
