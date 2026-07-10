# Lean Fast Verification Workflow

This guide is for agents working on CLRS-Lean proof files.  Its goal is to keep
the edit-check loop fast while still leaving a reliable path to full
verification before handoff.

## Rule 0: Do Not Start With `lake build CLRSLean`

`CLRSLean` is the root module.  It imports every chapter, including large
in-progress graph proofs.  Running the root target after every edit turns a
local proof step into a whole-project build.

Use the root target only at milestone points:

- before claiming that a cross-chapter change is complete;
- before committing a broad refactor;
- after the narrow target and chapter target already pass.

## The Three-Level Loop

### 1. Current File

After a local edit, build the module you touched:

```bash
lake --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC
```

For a source path instead of a module name:

```bash
lake --log-level=error build CLRSLean/Chapter_22/Section_22_3_DFS_SCC.lean
```

This is the default inner loop.  It catches elaboration errors, failed tactics,
and theorem statement mismatches without rebuilding unrelated chapters.

### 2. Immediate Dependents

When the current file passes, build the next module that imports it.

For Chapter 22 DFS/SCC work, the dependency shape is:

```text
Section_22_3_DFS
  -> Section_22_3_DFS_WhitePath
  -> Section_22_3_DFS_Intervals
  -> Section_22_3_DFS_Bridge
  -> Section_22_3_DFS_SCC
  -> Section_22_5_Strongly_Connected_Components
  -> Chapter_22
  -> CLRSLean
```

Examples:

```bash
lake --log-level=error build CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components
lake --log-level=error build CLRSLean.Chapter_22
```

Do not jump straight to `CLRSLean` unless the chapter-level target already
passes.

### 3. Full Library

Only after the current module and chapter module pass:

```bash
lake --log-level=error build CLRSLean
```

If this fails outside your edited area, record the first failing module and stop.
Do not chase unrelated chapters unless the task explicitly asks for it.

## Use `--old` For Local Iteration

Lake normally rebuilds transitive dependents when an upstream module changes.
That is correct for final verification but expensive during proof surgery.

For quick local feedback:

```bash
lake --old --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC
```

Use `--old` only for the inner loop.  Before handoff, rerun without `--old` on
the current module and the chapter target.

## Keep Logs Small

The repository enables documentation and linter messages.  A successful build
can still print many warnings from imported modules.

Prefer:

```bash
lake --log-level=error build TARGET
```

When you need a clean log file:

```bash
lake --log-level=error build TARGET > /tmp/clrs-lean-build.log 2>&1
```

Then inspect only the useful lines:

```bash
rg -n "^error:|unsolved goals|Tactic|declaration uses" /tmp/clrs-lean-build.log
```

## Time The Target Before Scaling Up

If a module feels slow, measure the narrow target once:

```bash
/usr/bin/time -p lake --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC
```

If the narrow target takes more than a minute, keep the proof split small and
avoid repeatedly building the chapter.  Finish one lemma, build the file, then
move on.

## Use Lean Profiling For Hot Definitions

When one file is unusually slow and already passes, profile that file directly:

```bash
lake env lean --profile CLRSLean/Chapter_22/Section_22_3_DFS_SCC.lean \
  > /tmp/dfs-scc-profile.log 2>&1
```

Look for definitions or theorems with the largest elaboration time.  Common
fixes are:

- replace broad `simp` with `simp only [...]`;
- split one large theorem into named helper lemmas;
- avoid repeatedly unfolding large recursive definitions;
- move expensive `by_cases`/`rcases` work into small lemmas;
- reduce giant goals before calling `omega`, `linarith`, or `aesop`.

## Chapter 22 Specific Advice

Chapter 22 is sealed for main functional correctness, but remains one of the
heaviest dependency areas.  When maintaining or refining it, treat it as
several smaller build islands:

- Basic graph model: `Section_22_1_Representing_Graphs`
- BFS: `Section_22_2_BFS`
- DFS core: `Section_22_3_DFS`
- DFS intervals/white path: `Section_22_3_DFS_WhitePath`,
  `Section_22_3_DFS_Intervals`
- DFS/SCC bridge: `Section_22_3_DFS_Bridge`, `Section_22_3_DFS_SCC`
- DFS edge classification: `Section_22_3_DFS_EdgeClassification`
- Topological sorting: `Section_22_4_Topological_Sort`
- SCC algorithm: `Section_22_5_Strongly_Connected_Components`

If you are editing `Section_22_3_DFS_SCC`, the usual validation ladder is:

```bash
lake --old --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC
lake --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC
lake --log-level=error build CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components
lake --log-level=error build CLRSLean.Chapter_22
```

Run `lake --log-level=error build CLRSLean` only after this ladder passes.

## Handoff Checklist

Before handing work back:

- `git status --short` shows only the files you intentionally changed.
- The current module passes without `--old`.
- The nearest dependent module passes.
- The chapter module passes if you changed a public theorem, import, or shared
  lemma.
- The final response reports the exact commands run and whether root
  `CLRSLean` was skipped or passed.

If root `CLRSLean` is skipped because another in-progress module is failing,
say that explicitly and name the failing module.

## Command Cheat Sheet

```bash
# Fastest useful local loop
lake --old --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC

# Honest local module check
lake --log-level=error build CLRSLean.Chapter_22.Section_22_3_DFS_SCC

# Next dependent for SCC work
lake --log-level=error build CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components

# Chapter-level check
lake --log-level=error build CLRSLean.Chapter_22

# Full library check, for milestones only
lake --log-level=error build CLRSLean

# Extract useful failures from a noisy log
rg -n "^error:|unsolved goals|Tactic|declaration uses" /tmp/clrs-lean-build.log
```
