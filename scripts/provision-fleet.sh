#!/usr/bin/env bash
#
# provision-fleet.sh — provision several isolated worktrees at once, race-safe.
#
# `git worktree add` writes to the shared .git and RACES under concurrency
# (observed: 3 of 4 parallel adds failed). So we SERIALIZE the worktree adds,
# then PARALLELIZE the heavy .lake copies.
#
# Usage:
#   scripts/provision-fleet.sh <branch1> <branch2> ...
#
# Config: same env vars as setup-worktree.sh.
#
# NB: this only provisions. Recommended concurrency for AGENTS that then *build*
# is <= 4 (the machine is RAM-bound ~30G; one `lake build` already uses all cores).
#
set -euo pipefail

MAIN="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ROOT="${CLRS_WORKTREE_ROOT:-$HOME/clrs-lean-worktrees}"
GOLDEN="${CLRS_GOLDEN_LAKE:-$ROOT/golden-packages}"

[ $# -ge 1 ] || { echo "usage: scripts/provision-fleet.sh <branch>..." >&2; exit 2; }
[ -d "$GOLDEN/mathlib/.lake/build/lib" ] || { echo "ERROR: golden missing; run scripts/refresh-golden.sh" >&2; exit 1; }

# Step 1 — serial worktree creation (safe against .git lock races).
for b in "$@"; do
  echo "[fleet] git worktree add $b"
  git -C "$MAIN" worktree add "$ROOT/$b" -b "$b" origin/main
done

# Step 2 — parallel .lake provisioning (disk-bound, RAM-light).
pids=()
for b in "$@"; do
  (
    wt="$ROOT/$b"; mkdir -p "$wt/.lake"
    cp -a --reflink=auto "$GOLDEN" "$wt/.lake/packages"; chmod -R u+w "$wt/.lake/packages"
    cp -a "$MAIN/.lake/build" "$wt/.lake/build"
    cp -a "$MAIN/.lake/config" "$wt/.lake/config"
    echo "[fleet] provisioned $wt"
  ) &
  pids+=($!)
done
rc=0
for p in "${pids[@]}"; do wait "$p" || rc=1; done
[ $rc -eq 0 ] && echo "[fleet] all provisioned (agents: keep build concurrency <= 4)." || { echo "[fleet] some copies failed" >&2; exit 1; }
