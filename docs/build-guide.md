# Build Guide: Fast Compilation for CLRS-Lean

This document explains how to build CLRS-Lean efficiently on any machine.
Reading time: 5 minutes.

## Quick Start (First-Time Setup)

```bash
# 1. Install Lean (one-time)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 2. Clone and set up
git clone <repo-url> && cd CLRS-Lean
lake update                  # Fetch mathlib and dependencies
lake exe cache get           # Download pre-built mathlib (3 seconds instead of 3 hours!)
lake build                   # Compile CLRSLean (46 seconds on a modern CPU)
```

**The critical step is `lake exe cache get`.**  Mathlib contains over 8,000
modules.  Without the cache, your machine will spend hours compiling them from
source.  With the cache, they are downloaded pre-compiled in seconds.

## Prerequisites

| Tool | Minimum Version | Check Command |
|------|----------------|---------------|
| elan  | any | `elan --version` |
| Lean  | `4.32.0-rc1` (pinned by `lean-toolchain`) | `lean --version` |
| Lake  | `5.0.0` (bundled with Lean) | `lake --version` |

**No other dependencies are required.**  Lean and Lake are installed together
via `elan`.  The Python helper scripts (`scripts/`) require `uv` but are only
needed for repository checks, not for compilation.

## Everyday Build Commands

### The Fast Path (development loop)

```bash
# After editing one .lean file — fastest rebuild
lake build --old
```

`--old` rebuilds only the modified module, skipping transitive dependency
checks.  **Use this when you are iterating on a proof** and know your changes
don't affect downstream modules.  If a downstream module breaks later, run a
normal `lake build` to fix it.

### Normal Build

```bash
lake build
```

Full correctness check: rebuilds modified modules **and** everything that
depends on them.  Safe for any kind of change.

### Build a Single Module

```bash
lake build +CLRSLean.Chapter_22.Section_22_2_BFS
```

Only compiles the named module and its dependencies.  Much faster than a full
build when you are focused on one section.

### Build with Pre-built Cache Download

```bash
lake update && lake exe cache get && lake build
```

Run this after pulling from `main` or switching branches that may have updated
mathlib.  The order matters: `update` refreshes dependencies, `cache get`
fetches matching pre-built oleans, and `build` compiles your code.

### Full Clean Build (rarely needed)

```bash
lake clean && lake exe cache get && lake build
```

Use only when the build cache is corrupted or you suspect stale artifacts.
`lake exe cache get` will restore the mathlib cache in seconds.

## How Long Does It Take?

Measured on a 32-core AMD Ryzen 9 7950X, 30 GB RAM:

| Scenario | Wall Time | CPU | What Happens |
|----------|-----------|-----|--------------|
| Nothing changed | 2–7 s | ~2 cores | Lake replays traces, no compilation |
| One section edited (`--old`) | 5–15 s | ~1 core | Single module recompiled |
| One section edited (normal) | 20–50 s | ~14 cores | Module + transitive dependents |
| All user code rebuilt | ~46 s | ~14 cores | 105 modules in parallel |
| Mathlib from source | **3+ hours** | 16 cores | 8,000+ modules — **use cache instead!** |

Lake automatically uses up to 16 parallel Lean processes.  You do not need to
pass `-j` or configure anything; Lake detects your core count and scales
accordingly.

## Workflows

### Edit → Compile → Fix Loop

```bash
# Terminal 1: edit your .lean file, then
lake build --old

# Terminal 2 (optional): watch for type errors on save
# Your editor's Lean LSP does this automatically
```

### Pulling Updates

```bash
git pull
lake update              # Update mathlib if lean-toolchain changed
lake exe cache get       # Re-sync pre-built oleans
lake build               # Recompile user code
```

### Adding a New Chapter

```bash
# 1. Create the .lean file
# 2. Build just that chapter to catch errors fast
lake build +CLRSLean.Chapter_NN

# 3. Once it compiles, do the full build to check downstream impact
lake build
```

### Switching Branches

```bash
git switch other-branch
lake update && lake exe cache get && lake build
```

## Performance Tips

### 1. Keep mathlib cache up to date

```bash
lake exe cache get
```

Run this after any `lake update` or toolchain change.  It is the single biggest
performance win — hours of compilation avoided every time.

### 2. Use `--old` during proof development

```bash
lake build --old
```

When you are deep in a proof and recompiling frequently, `--old` cuts build
time from 30–50 seconds to 5–15 seconds.  Just remember to run a normal build
before pushing.

### 3. Build the specific module you need

```bash
lake build +CLRSLean.Chapter_08.Section_08_3_Radix_Sort
```

Lake will only compile that module and its dependencies, skipping unrelated
chapters.

### 4. Avoid `lake clean` unless necessary

The build cache is your friend.  `lake clean` deletes all pre-built artifacts,
including mathlib oleans, and a full rebuild takes hours.  If you accidentally
run it, restore with:

```bash
lake exe cache get && lake build
```

### 5. C caching (optional, small gain)

If you have `ccache` installed, exported as follows to cache C compilation:

```bash
export LEAN_CC="ccache gcc"
```

The C files generated by Lean are small; this saves a few seconds on a full
rebuild at most.

## How the Cache Works

```
┌─────────────┐     ┌──────────────────┐     ┌─────────────────────┐
│  You type   │────▶│ lake exe cache   │────▶│ Azure (mathlib CI)  │
│  cache get  │     │ get              │    │ stores pre-built     │
└─────────────┘     └──────────────────┘     │ .olean.ltar files   │
                                             └─────────────────────┘
                                                        │
                    ┌────────────────────────────────────┘
                    ▼
┌─────────────┐     ┌──────────────────┐     ┌─────────────────────┐
│ lake build  │◀────│ Local .lake/     │◀────│ 8,564 decompressed  │
│ (7 seconds) │     │ packages/mathlib │     │ .olean files        │
└─────────────┘     └──────────────────┘     └─────────────────────┘
```

- **cache get** contacts the mathlib CI Azure storage, finds the olean archive
  matching your Lean toolchain version, and downloads only the missing files.
- **cache pack** (optional) compresses your local oleans into the same format —
  useful if you contribute to mathlib itself.
- There is nothing to configure; the cache tool reads the mathlib origin URL
  from git automatically.

## Troubleshooting

### `lake build` fails with "unknown module"

Your `.lake` directory may be stale.  Run:

```bash
lake update && lake exe cache get && lake build
```

### `lake exe cache get` fails or isn't found

Make sure you are inside the CLRS-Lean directory and mathlib is present:

```bash
cd /path/to/CLRS-Lean
lake update   # ensures mathlib is cloned
lake exe cache get
```

### Build is slow even with cache

Check how many modules are actually being compiled (not replayed):

```bash
lake build -v 2>&1 | grep -v Replayed | grep "Built"
```

If many mathlib modules are being built, the cache may be incomplete.  Run
`lake exe cache get` again.

### `--old` causes downstream errors later

This is expected occasionally.  Run a normal `lake build` to fix transitive
dependencies, then continue with `--old`.

### Disk space: `.lake/` is large

The `.lake/` directory is ~10 GB, mostly from mathlib.  It is in `.gitignore`
(not committed).  You can safely delete it and restore:

```bash
rm -rf .lake
lake update && lake exe cache get && lake build
```

## See Also

- [CLAUDE.md](../CLAUDE.md) — coding conventions for contributors
- [Repository Architecture](repository-architecture.md) — how the repo is organized
- [Contributor Workflow](https://tanktechnology.github.io/CLRS-Lean/CLRSLean/Workflow/) — proof status and contribution guidelines
