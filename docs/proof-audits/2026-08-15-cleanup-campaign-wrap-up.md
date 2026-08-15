# Cleanup campaign wrap-up (2026-08-15)

This is the Phase 5 retrospective for the book-wide cleanup campaign that ran
on 2026-08-15.  It covers the four execution phases — planning/issue-seeding,
facade source migration, ledger reconciliation, and publication-gate repair —
plus the two successful Pages deployments that closed the campaign.  It is the
narrative companion to [`facade-source-migration-plan.md`](../migrations/facade-source-migration-plan.md)
(the *how*) and [`clrs4.md`](../migrations/clrs4.md) (the *what*).

The campaign objective was **source-location re-homing only**: migrate the 47
non-`Ch34` compatibility-facade rows to native fourth-edition source, then
reconcile the completion ledger and clear the publication gate for a live
Verso deploy.  Every facade chapter was already theorem-bearing on `main`; the
campaign removed migration debt, not theorem gaps.

## Hard constraint (held throughout)

**Chapter 34 (NP-Completeness) was excluded from all proof and migration work.**
Its `34.1`–`34.3` rows are `facade` because that facade masks real coverage
gaps, not source location — a source move would confuse the two (the first
"known failed route" in issue #229).  The only touches to Chapter 34 were
infrastructure, not proofs:

- **PR #284** registered the five §34.4 `PolyBuilder` support modules in site
  navigation (`literate.toml` + `docs/index.md` + `Chapter_34.lean` imports),
  unblocking `check_repository.py`.
- **PR #290** de-duplicated three file-local private theorems that collided on
  a Verso search-index ID (see Phase 4).

No Chapter 34 theorem, lemma, or bound was added, changed, or weakened.  Its
ledger state is unchanged: `34.1`–`34.3` `facade`, `34.4` `partial`, `34.5`
`not-started`.

## Phase 1 — Planning and issue seeding

Issue **#229** (migrate the remaining facade rows to native source) was
delivered as a plan document, not proofs:

- **PR #249** (`docs/migrations/facade-source-migration-plan.md`, squash
  `9524831b`).  The plan inventories the 47 non-`Ch34` facade rows across 14
  legacy prefixes, groups them by chapter, and fixes the per-chapter procedure
  (§5: compatibility-test-first, native move, legacy forwarding shim, atomic
  edition-map flip).
- **14 follow-up issues opened** — one per facade chapter (#250–#263), labeled
  `chapter-NN` + `fourth-edition` + `infrastructure`, each carrying the §4
  mapping, §5 gates, and a plan-doc reference.  `Ch34` was excluded.

Key plan facts: the facade chapters share their 3e/4e chapter number, so the
migration is **source-location re-homing only, no declaration-namespace
rename** (namespace renames belong to the already-native shifted chapters,
a separate track).

## Phase 2 — Facade source migration execution

All 14 facade chapters (Ch1–Ch13, Ch18) were migrated to native
fourth-edition source.  Each migration followed the plan's §5 gates: a
compatibility test first, the native move, a legacy forwarding shim, and an
atomic `facade` → `native` flip in `docs/clrs-fourth-edition-map.csv`.

| Chapter | PR | Scope |
| --- | --- | --- |
| Ch1 | #264 | prose-only guide re-point (§1.1–1.2) |
| Ch2 | #265 | §2.1–2.3 |
| Ch3 | #266 | §3.1–3.3 |
| Ch4 | #267 | §4.2–4.5 |
| Ch5 | #268 | §5.1–5.4 |
| Ch6 | #270 | §6.1–6.5 |
| Ch7 | #269 | §7.1–7.4 |
| Ch8 | #272 | §8.1–8.4 |
| Ch9 | #271 | §9.1–9.3 |
| Ch10 | #274 | §10.1–10.3 |
| Ch11 | #273 | §11.1–11.5 |
| Ch12 | #276 | §12.1–12.3 |
| Ch13 | #275 | §13.1 |
| Ch18 | #277 | §18.1–18.3 |

Execution was parallelized across two "machines" (odd chapters sequential,
even chapters concurrent), each rebasing onto the advancing `main`.  Conflicts
were confined to `docs/clrs-fourth-edition-map.csv` and `literate.toml`, both
resolved by keeping both chapters' rows/entries.

A pre-existing test staleness was fixed in the same sweep: **PR #278**
relocated the Chapter 11 perfect-hashing `#check` from the stale
`CLRSLean.OnlineMaterial` path to the canonical `CLRSLean.Chapter_11` path
(§11.5 perfect hashing had been promoted to canonical `§11.5` earlier).

**Outcome:** the edition map now has **132 native rows**; the only non-native
rows are Chapter 34 (`facade`/`partial`/`not-started`).  Follow-up issues
#250–#263 are all closed.

## Phase 3 — Ledger reconciliation and closure

**PR #279** (`bbb259e8`) swept the completion ledger and check-suite:

- **Ch21** (Minimum Spanning Trees) flipped
  `main-proof-complete-for-correctness` → `main-proof-complete`: the
  O(E log E) Kruskal and O(E log V) Prim cost bounds are proved
  (`totalWork_le_forty_mul_edge_log`, `binaryHeapWork_le_edge_log`).
- Stale `facade` / "reuses legacy source" prose was swept to `native` across
  the proof-progress CSV; `Progress.lean` and `README` were regenerated.
- **Ch12** and **Ch20** stay `main-proof-complete-for-correctness` (Ch12
  missing the §12.4 ancestor probability + expected-depth bound; Ch20 missing
  the O(V+E) BFS/DFS running-time bounds) — not silently promoted.
- Three `FourthEdition` support-page links (Ch05/07/09) and the
  `prepare_literate_site` fixture were fixed.

## Phase 4 — Publication-gate repair and branch hygiene

Two Chapter 34 *infrastructure* fixes cleared the Pages publication gate:

- **PR #284** registered the five §34.4 `PolyBuilder` support modules in
  `literate.toml` + `docs/index.md` + `Chapter_34.lean`, unblocking
  `check_repository.py` (the gate for `pages.yml`).
- **PR #290** fixed the cold-deploy failure: the first deploy (run
  `31875225174`) died on "Duplicate document ID" because three
  `private theorem evalBundle_of_evalCfgBits_eq` (each the first private decl
  of its file, all doc-commented, same `CLRS.Chapter34.Turing.CookLevin`
  namespace) produced the same Verso search-index ID.  They were renamed to
  unique file-local names (`transitionEvalBundle_…`, `dispatchEvalBundle_…`,
  `statementEvalBundle_…`); a corrected scan over every doc-commented private
  declaration confirmed no remaining (namespace, index, name) collision.

**Branch hygiene:** deleted 8 superseded remote branches (`codex/ch15`,
`codex/ch19`, `codex/ch27`, `feat/ch32-rabin-karp`, `feat/ch35-2/3/4`,
`feat/merge-caiwei-pr85`).  Kept `backup/pre-identity-rewrite` (backup) and
`fix/ch34-site-nav` (unmerged Ch34 machine-repair work, off-limits).

## The two deployments

| Run | Pages run ID | Commit | Result |
| --- | --- | --- | --- |
| cold deploy (#216) | `31875225174` | pre-#290 | **failed** — Duplicate document ID |
| deploy (#217) | `31880183982` | `63d1aa27` (= #290, incl. #285–#288) | **success** |
| redeploy (#218) | `31882041140` | `a092fbac` (= #291) | **success** |

The **first successful deployment** (#217) shipped at `63d1aa27`, which
already included the parallel proof PRs #285 (ch22), #286 (ch16), #287
(ch05), and #288 (ch31) that merged concurrently with the campaign.

The **redeploy** (#218) was re-triggered on latest `main` `a092fbac` (PR #291,
§31.4/§31.7/§31.8) to pick up everything merged after the #217 build.  All
seven jobs green (prepare ~30m, render shards 0–3 in parallel ~5m, merge
2m46s, deploy 8s; ~38m total).  Site verified HTTP 200, homepage carrying
§31.8 Primality content.  **#218 is the authoritative live build.**

Site: <https://tanktechnology.github.io/CLRS-Lean/>.

## Final state

- **132 native rows** in `docs/clrs-fourth-edition-map.csv` (of 147 total);
  the only non-native rows are Chapter 34 (`34.1`–`34.3` `facade`, `34.4`
  `partial`, `34.5` `not-started`).
- All 14 facade chapters migrated; follow-up issues #250–#263 closed; the
  facade migration campaign is complete.
- Ledger reconciled; Ch21 promoted; Ch12/Ch20 explicitly retained at
  `main-proof-complete-for-correctness`.
- Publication gate cleared; live Verso site deployed and re-verified.

No `sorry`/`admit`/project axiom entered the tree during the campaign; the
work was source re-homing, ledger bookkeeping, site-navigation configuration,
and one search-index de-duplication.
