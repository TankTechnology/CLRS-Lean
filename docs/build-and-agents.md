# Build & parallel-agent infrastructure

How to run many agents (or your own worktrees) against CLRS-Lean **fast** and
**safely**. Read this before fanning out parallel Lean work.

## The problem

Lean + Mathlib builds are heavy. A fresh git worktree has no `.lake`, so its
first build either unpacks ~7.4G of Mathlib oleans (`lake exe cache get`,
minutes) or compiles Mathlib from source (hours). Two failure modes bit us:

- **Build waits** — every agent paying the cache-get cost before doing any work.
- **A concurrency OOM** — 9 worktree agents each ran `lake exe cache get`
  concurrently. The machine is **~30G RAM / 32 cores**, so RAM (not CPU) blew
  up; OOM kills corrupted the *shared* `.lake` (the worktrees had symlinked
  `.lake/packages` back to the main repo). Recovery took ~20 min.

## The model: one golden build, isolated writable copies

1. **Golden packages.** Build Mathlib + deps once in the main repo; snapshot
   `.lake/packages` to `$CLRS_GOLDEN_LAKE`. Do this with
   [`scripts/refresh-golden.sh`](../scripts/refresh-golden.sh).
2. **Per-worktree isolation.** Each worktree gets its **own writable copy** of
   the golden packages plus a copy of the CLRS `build`/`config`. It never runs
   `cache get`; `lake build` is a warm, incremental compile of only what changed.
   Do this with [`scripts/setup-worktree.sh`](../scripts/setup-worktree.sh) (one)
   or [`scripts/provision-fleet.sh`](../scripts/provision-fleet.sh) (many).

Why a *writable copy* and not a read-only symlink: 11 of 13 deps use
`inputRev = main/master`, so `lake build` runs `git` in each dep (writing
`FETCH_HEAD`); a read-only shared `.lake/packages` makes that fail. (Pinning
those deps to fixed revs would enable zero-copy read-only sharing — a planned
follow-up.)

## Provisioning

```bash
# once (or after a Mathlib bump / a corrupted .lake):
scripts/refresh-golden.sh

# one isolated worktree:
scripts/setup-worktree.sh my-feature-branch
cd "$CLRS_WORKTREE_ROOT/my-feature-branch" && lake build CLRSLean   # seconds

# a batch (race-safe: serial adds, parallel copies):
scripts/provision-fleet.sh iss-a iss-b iss-c iss-d
```

Env config (defaults shown): `CLRS_WORKTREE_ROOT=$HOME/clrs-lean-worktrees`,
`CLRS_GOLDEN_LAKE=$CLRS_WORKTREE_ROOT/golden-packages`. Put the worktree root on
the largest disk; a reflink-capable FS (xfs/btrfs) makes the copies instant.

## Rules for parallel agents

- **Never run `lake exe cache get` in a provisioned worktree** — Mathlib is
  already there; concurrent cache-gets are what caused the OOM.
- **Build concurrency ≤ 3–4.** The limit is RAM (~30G), not CPU. One `lake build`
  already saturates the cores; more concurrent agents only add memory pressure.
- **Agents commit early/often.** An interrupted agent loses only *uncommitted*
  work; the branch survives.
- Keep each agent strictly inside its own worktree; never touch the main repo's
  working tree.

## Verifying agent proof work before merge

For a full pre-merge / pre-deploy QA pass — format consistency, proof soundness,
and rendered-nav/TOC correctness — dispatch the **`clrs-qa-reviewer`** agent
(`.claude/agents/clrs-qa-reviewer.md`); it builds the site and inspects the
actual Verso navigation, not just the static `literate.toml`.

`lakefile.lean` sets `-Dwarn.sorry=false`, so **a clean build does not imply
sorry-free.** Before merging any agent's branch:

1. `grep -rnE '\b(sorry|admit|native_decide)\b'` on the changed `.lean` files → zero.
2. `#print axioms <headline theorem>` (via a scratch `lake env lean` file) → only
   `propext / Classical.choice / Quot.sound`, never `sorryAx`. This also forces
   loading the real compiled artifact, so it doubles as a build-integrity check.
3. Confirm key definitions are **non-vacuous** and the theorem statement is
   meaningful (a cost function defined as `0` makes any bound trivially true).
4. Regression: no existing public declaration removed/renamed/weakened
   (`comm -23` on sorted decl-name lists vs `origin/main`).
5. Shared status files conflict on every merge — resolve `docs/*.md`/CSV by
   per-chapter union and **regenerate** `CLRSLean/Progress.lean` from the CSV
   (`python3 scripts/check_progress_csv.py --write-dashboard`); never hand-merge it.

## Single-file proof development (fast feedback)

When iterating on a proof in a single `.lean` file, do **not** run a full
`lake build CLRSLean` after every edit.  Use the following instead, from
fastest to most thorough:

### Tier 1 — elaborate one file (fastest)

```bash
lake lean CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean
```

This builds the file's dependencies once, then elaborates only the target
file.  It does **not** produce a cached `.olean`, so downstream modules are
unaffected (and unchecked).  Typical latency: ~5 s.

Use this for the inner loop of proof writing — checking whether a single
lemma compiles.

### Tier 2 — build a single module

```bash
lake build CLRSLean.Chapter_25.Section_25_2_Floyd_Warshall
```

Same as Tier 1 but also writes the `.olean` and `.ilean`.  Equally fast, and
leaves the build cache up-to-date so a later full build starts warm.

### Tier 3 — skip transitive dependencies

```bash
lake build --old CLRSLean
```

Rebuilds **only** the modules whose source files changed, ignoring transitive
downstream dependents.  This catches syntax/elaboration errors in the edited
file without waiting for the whole library to relink.  ~3–4 s.

**Caveat:** `--old` does not check that downstream modules still import
correctly; use Tier 4 before pushing.

### Tier 4 — full incremental build

```bash
lake build CLRSLean
```

The standard build.  Only re-elaborates modules whose transitive dependencies
changed.  ~6 s after a single-file edit.

### Tier 5 — cold / verification build

```bash
lake build --reconfigure CLRSLean   # if lakefile.lean changed
lake build --rehash CLRSLean        # if build traces are suspect
```

### Decision table for agents

| Situation | Command |
|---|---|
| Checking a single proof compiles | `lake lean <file>` |
| Checking a file + caching its olean | `lake build +<Module.Path>` |
| Quick re-check after a small edit | `lake build --old CLRSLean` |
| Full check before committing | `lake build CLRSLean` |
| Lakefile / dependency changes | `lake build --reconfigure CLRSLean` |
| Suspect stale trace / weird error | `lake build --rehash CLRSLean` |

## Recovery runbook (corrupted `.lake`)

If Mathlib is deleted/emptied (e.g., an interrupted re-clone):
`scripts/refresh-golden.sh` handles it — it `rm -rf`s the broken
`.lake/packages/mathlib` and re-fetches oleans from the machine-global cache
`~/.cache/mathlib`, then rebuilds. Agent git commits are unaffected (they live on
branches, independent of the build env).
