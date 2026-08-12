# CLRS fourth-edition primary migration design

Date: 2026-08-06

Status: approved for autonomous implementation

## Problem

CLRS-Lean currently uses the third-edition chapter sequence as its public
filesystem, progress, and website skeleton.  Selected developments already use
fourth-edition statements, but the repository does not state that mixed-edition
policy.  Readers can therefore mistake modules such as Chapter 19 (Fibonacci
heaps), Chapter 20 (van Emde Boas trees), Chapter 27 (multithreaded algorithms),
and Chapter 33 (computational geometry) for fourth-edition chapter coverage.

The migration must make the fourth edition the primary reader and contributor
view without immediately breaking the existing Lean import surface.  It must
also avoid making the already slow Verso publishing path worse.  Before the
proof-state suppression patch, the observed publishing baseline was about 24
minutes for raw Verso HTML plus 6--7 minutes for site assembly, with roughly
3.3 GB of raw HTML.  The current renderer is monolithic: any changed literate
JSON file or `literate.toml` causes a serial rerender of every page.

The fourth-edition table of contents and the third-to-fourth-edition change
summary are taken from the official MIT Press documents:

- <https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/4e_toc.pdf>
- <https://mitp-content-server.mit.edu/books/content/sectbyfn/books_pres_0/11599/transition_guide.pdf>

## Goals

1. Make CLRS fourth-edition chapters 1--35 the canonical public organization.
2. Preserve the current third-edition import paths and declaration names during
   a documented compatibility window.
3. Move third-edition-only material out of the primary chapter ledger and into
   an explicit online/supplementary-material catalog.
4. Represent new fourth-edition Chapters 25, 27, and 33 honestly without
   blocking the structural migration on new proof developments.
5. Give contributors one machine-readable edition map and one fourth-edition
   progress source of truth.
6. Parallelize the expensive page-rendering stage while preserving complete
   navigation, cross references, search data, and atomic deployment.
7. Keep ordinary commits and pull requests free of automatic full Lean or site
   builds; publishing remains manually dispatched.

## Non-goals

- Do not formalize the new matching, online-algorithm, or machine-learning
  chapters in this migration.
- Do not rename hundreds of existing declarations in one change.
- Do not delete or silently weaken any kernel-checked theorem.
- Do not claim complete fourth-edition coverage merely because a third-edition
  development can be reused.
- Do not create a permanent full fork of Verso.
- Do not deploy partial shard output or a mixture of pages from different
  commits.

## Chosen architecture

### Transitional public module tree

The transition introduces these public aggregators:

```text
CLRSLean/FourthEdition.lean
CLRSLean/FourthEdition/Chapter_01.lean
...
CLRSLean/FourthEdition/Chapter_35.lean
CLRSLean/OnlineMaterial.lean
```

`CLRSLean.FourthEdition.Chapter_NN` is the canonical chapter-guide import during
the compatibility period.  A guide imports the existing theorem-bearing
module that supplies its current proof content and explicitly records any
section-number mismatch or missing fourth-edition section.  The first pass is
a facade: theorem declarations retain their existing names such as
`CLRS.Chapter21.*` even when the fourth-edition Chapter 19 guide reuses them.

Existing unqualified modules remain available and unchanged as compatibility
imports.  This avoids the impossible transitional ambiguity in which
`CLRSLean.Chapter_19` would need to mean both third-edition Fibonacci heaps and
fourth-edition disjoint sets.

The library landing page, README, progress dashboard, status page, workflow,
and website sidebar use the fourth-edition guide tree.  Legacy proof pages stay
generated and directly reachable during the transition, but are removed from
the primary chapter sidebar and are labeled as compatibility sources.

### Final module tree

Chapter content is migrated after the facade release, one chapter at a time:

1. Move the theorem-bearing source to its fourth-edition location.
2. Rename its declaration namespace where needed.
3. Replace the old module with a small forwarding/alias compatibility module.
4. Update focused interface tests to check both canonical and legacy imports.
5. Remove the old module and aliases only at the cleanup major release.

At that cleanup release, the `FourthEdition` prefix disappears from the
canonical API: unqualified `CLRSLean.Chapter_NN` denotes the fourth edition.
Third-edition-only chapters remain under `CLRSLean.OnlineMaterial`, not under
obsolete chapter numbers.

## Canonical chapter mapping

The structural migration uses the following chapter-level map.  Section-level
differences remain explicit in the machine-readable map and chapter guides.

| Fourth edition | Current proof source | Initial migration state |
| --- | --- | --- |
| 1--2 | current Chapters 1--2 | reusable; title/prose review |
| 3 | current Chapter 3 | reusable with fourth-edition section remap |
| 4 | current Chapter 4 | partial remap; maximum subarray becomes online material; §§4.6--4.7 need review |
| 5--13 | current Chapters 5--13 | mostly reusable; section differences recorded |
| 14 | current Chapter 15, Dynamic Programming | reusable through facade |
| 15 | current Chapter 16, Greedy Algorithms | reusable core; offline caching missing; matroid material supplementary |
| 16 | current Chapter 17, Amortized Analysis | reusable through facade |
| 17 | current Chapter 14, Augmenting Data Structures | reusable through facade |
| 18 | current Chapter 18, B-Trees | reusable |
| 19 | current Chapter 21, Disjoint Sets | reusable through facade |
| 20 | current Chapter 22, Elementary Graph Algorithms | reusable through facade |
| 21 | current Chapter 23, Minimum Spanning Trees | reusable through facade |
| 22 | current Chapter 24, Single-Source Shortest Paths | reusable through facade |
| 23 | current Chapter 25, All-Pairs Shortest Paths | reusable through facade |
| 24 | current Chapter 26, Maximum Flow | reusable through facade |
| 25 | no canonical chapter | `not-started`; related old maximum-matching theorem is cross-linked but not counted as migrated coverage |
| 26 | current Chapter 27, Multithreaded Algorithms | reusable with fourth-edition terminology |
| 27 | no canonical chapter | `not-started` |
| 28--32 | current Chapters 28--32 | reusable with explicit moved/new-section gaps |
| 33 | no canonical chapter | `not-started` |
| 34--35 | no current proof chapters | `not-started` |

The primary supplementary catalog initially includes:

- Fibonacci heaps (third-edition Chapter 19; fourth-edition online material);
- van Emde Boas trees (third-edition Chapter 20; fourth-edition online material);
- computational geometry (third-edition Chapter 33; fourth-edition online material);
- maximum subarray, perfect hashing, matroid/task-scheduling material, detailed
  simplex, iterative FFT, and integer factorization where the repository has
  theorem-bearing third-edition content that the fourth edition moved online or
  out of the corresponding main chapter.

## Metadata and status ownership

`docs/clrs-fourth-edition-map.csv` is the canonical edition bridge.  Each row
records:

- fourth-edition chapter and section;
- fourth-edition title;
- current source module(s);
- legacy third-edition location;
- migration state (`native`, `facade`, `partial`, `not-started`, or
  `online-material`);
- exact coverage note.

`docs/clrs-proof-progress.csv` remains the chapter-level progress source, but
its rows and titles switch to fourth-edition Chapters 1--35.  Reused theorem
counts remain visible, while status text distinguishes native fourth-edition
coverage from compatibility-facade reuse.  Online-material theorem counts are
reported separately so the library total remains auditable without inflating
fourth-edition chapter coverage.

Repository checks validate:

1. exactly 35 fourth-edition chapter rows and guides exist;
2. every progress row has at least one edition-map row;
3. every mapped source module exists;
4. all `not-started` chapters have zero canonical tracked theorems;
5. fourth-edition titles agree across the map, progress CSV, guides, and
   navigation;
6. every legacy source is either mapped into a fourth-edition chapter or listed
   as online material.

## Compatibility and deprecation policy

The facade release starts the deprecation window but does not emit thousands
of declaration warnings.  Deprecation is communicated through module
docstrings, README, the migration guide, and contributor workflow.  Focused
tests lock the old imports and representative old declaration names.

Compatibility is guaranteed through all `1.x` releases and for at least six
months after the facade release.  Removal may occur only in the next major
release (`2.0` or later), with a release note that lists every removed import
prefix.  The cleanup release performs the final switch:

- `CLRSLean.Chapter_NN` becomes fourth-edition canonical;
- `CLRSLean.FourthEdition.Chapter_NN` becomes a temporary forwarder, then is
  removed in a later major release;
- obsolete third-edition chapter imports are removed;
- retained online material uses stable content names rather than old chapter
  numbers.

## Parallel Verso publishing design

### Why cache-only is insufficient

Caching `.lake/build/literate` avoids repeated Lean extraction, but the Verso
package facet hashes all planned JSON plus `literate.toml` into one HTML target.
Any content or navigation change therefore invokes one serial `emitDir` over
the whole site.  Caching raw HTML can skip a no-change deployment, but it does
not accelerate the normal case where a chapter changed.

### Sharded renderer

The repository keeps the existing narrow Verso compatibility-patch model and
adds a second small patch that lets `verso-literate-html` receive:

- the complete module map, used to construct the full navigation tree,
  cross-reference domains, and link targets;
- a deterministic emit list, used only to choose which module pages this
  process writes;
- a shard-output path for hover/document metadata;
- a flag selecting the single coordinator that emits landing, search, xref,
  and shared assets.

Every shard therefore sees the full site graph.  Page links and navigation do
not depend on which shard rendered the page.

`scripts/plan_literate_shards.py` partitions modules deterministically using
the literate JSON byte size as the initial render-cost estimate.  A greedy
largest-first assignment balances four default shards while keeping all
modules in a chapter together when doing so does not create a severe skew.
The shard count is configurable; local and hosted defaults never exceed four
until measurements show that memory and artifact transfer remain safe.

Each shard runs in a separate GitHub Actions matrix job.  A preparation job
builds/restores the 285-MiB literate JSON tree once and uploads it as an
artifact.  Shards download the same immutable input, render disjoint page
sets, run local raw-page guards, and upload disjoint outputs.  The merge job:

1. verifies all artifacts have the same source/config/dependency digest;
2. rejects missing, duplicate, or unexpected module pages;
3. unions shard hover/document JSON and rejects unequal duplicate keys;
4. adds coordinator-generated search/xref/shared assets;
5. runs the full raw-weight, freshness, navigation, rendering, and preparation
   checks;
6. uploads one Pages artifact only after every check passes.

No shard deploys independently.  GitHub Pages sees one atomic merged site.

### Local publishing

`scripts/build_literate_site.py --jobs N` exposes the same orchestration
locally.  It defaults to at most four renderer processes, reuses existing
literate JSON, records per-shard durations and bytes, and supports `--jobs 1`
as the reference fallback.  The existing unsharded `lake build
:literateHtml` remains a correctness oracle and emergency fallback.

### Performance acceptance

The first production run records preparation, per-shard rendering, merge, and
site-assembly durations.  The target is a warm manually dispatched deployment
under 10 minutes and a cold deployment under 20 minutes.  Runner variance is
reported rather than used as a correctness failure.  Correctness failures,
digest mismatches, missing pages, duplicate pages, stale output, and residual
proof states are hard failures.

The workflow remains `workflow_dispatch` only.  Fast unit tests for planning,
merging, digest checks, and workflow policy run locally and in explicit review;
ordinary commits do not acquire an automatic full site build.

## Error handling

- Missing mapped module: repository check fails with the exact CSV row.
- Duplicate fourth-edition chapter/section: map validation fails.
- Fourth-edition facade imports a missing legacy source: focused Lean build
  fails before site work.
- Verso patch drift: patch application fails before literate extraction and
  prints the pinned Verso revision.
- Failed shard: matrix and merge jobs fail; no Pages artifact is uploaded.
- Shard digest mismatch: merge fails before copying page output.
- Missing/duplicate page: merge reports the module and contributing shard.
- Metadata merge conflict: merge reports the conflicting key and values.
- Parallel path regression: the unsharded fallback remains available for one
  release cycle and is used to compare module-page inventories.

## Verification

### Fast repository checks

- edition-map schema and source existence tests;
- 35-guide/progress/title consistency tests;
- compatibility-import interface tests;
- shard planner determinism, completeness, disjointness, and balance tests;
- shard merger digest, duplicate, missing-page, and metadata-conflict tests;
- workflow-policy tests preserving manual-only triggers and atomic deployment.

### Lean checks

- build the new fourth-edition and online-material aggregators;
- run representative old-import compatibility tests;
- run `lake build CLRSLean`;
- search changed theorem-bearing sources for unfinished proof markers.

### Publishing checks

- compare sharded and unsharded module-page inventories;
- run raw HTML weight and freshness checks;
- run optimized navigation/rendering tests;
- perform one deliberate full sharded build because this task explicitly
  changes publishing and website behavior;
- record total output size, largest page, shard skew, and wall-clock duration.

## Rollout

1. Land the edition map, fourth-edition facade guides, online-material guide,
   and compatibility contract.
2. Switch public status/navigation/documentation to the fourth-edition view.
3. Land the sharded renderer patch and local orchestration with unit tests.
4. Switch the manual Pages workflow to prepare, render four shards, merge, and
   deploy atomically.
5. Run the first measured manual-equivalent local build and keep the serial
   fallback documented.
6. Begin per-chapter source/namespace migrations as separate proof projects.

## Acceptance criteria

- README and the website state that CLRS-Lean is fourth-edition primary.
- Public chapter navigation contains fourth-edition Chapters 1--35 in official
  order and titles.
- `CLRSLean.FourthEdition` builds and imports all 35 guides.
- Existing unqualified chapter imports and representative declaration names
  continue to compile.
- New Chapters 25, 27, and 33 are visible and honestly marked `not-started`.
- Third-edition-only chapters are absent from the primary chapter ledger and
  present in the online-material catalog.
- The edition map and fourth-edition progress data pass repository checks.
- The Pages workflow renders disjoint shards in parallel and deploys only the
  fully validated merge.
- Serial and sharded outputs have identical expected module-page inventories.
- `uv run python scripts/check_repository.py`, `lake build CLRSLean`, and the
  publishing-specific validation commands pass.
