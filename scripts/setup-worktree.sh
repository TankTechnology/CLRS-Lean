#!/usr/bin/env bash
#
# setup-worktree.sh — provision an isolated, pre-built worktree for parallel Lean work.
#
# Gives a new git worktree a warm, ISOLATED .lake (Mathlib already built) so an
# agent can `lake build` in seconds instead of running `lake exe cache get`
# (minutes, and OOM-prone when run concurrently — see docs/build-and-agents.md).
#
# Usage:
#   scripts/setup-worktree.sh <branch> [--base <ref>]
#
# Config (env vars, with sensible defaults — no machine paths hardcoded):
#   CLRS_WORKTREE_ROOT   where worktrees live   (default: $HOME/clrs-lean-worktrees)
#   CLRS_GOLDEN_LAKE     prebuilt packages dir  (default: $CLRS_WORKTREE_ROOT/golden-packages)
#
set -euo pipefail

MAIN="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ROOT="${CLRS_WORKTREE_ROOT:-$HOME/clrs-lean-worktrees}"
GOLDEN="${CLRS_GOLDEN_LAKE:-$ROOT/golden-packages}"

BRANCH="${1:-}"
[ -n "$BRANCH" ] || { echo "usage: scripts/setup-worktree.sh <branch> [--base <ref>]" >&2; exit 2; }
shift
BASE="origin/main"
while [ $# -gt 0 ]; do
  case "$1" in
    --base) BASE="${2:?}"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

WT="$ROOT/$BRANCH"

if [ ! -d "$GOLDEN/mathlib/.lake/build/lib" ]; then
  echo "ERROR: golden packages missing/incomplete at $GOLDEN" >&2
  echo "       run  scripts/refresh-golden.sh  first." >&2
  exit 1
fi
if [ ! -d "$MAIN/.lake/build" ]; then
  echo "ERROR: main repo has no .lake/build — run  scripts/refresh-golden.sh  first." >&2
  exit 1
fi

echo "[setup-worktree] git worktree add $WT  (branch $BRANCH off $BASE)"
git -C "$MAIN" worktree add "$WT" -b "$BRANCH" "$BASE"

echo "[setup-worktree] provisioning isolated .lake (writable packages copy + build/config)"
mkdir -p "$WT/.lake"
# --reflink=auto: instant CoW copy on xfs/btrfs, silent full copy on ext3.
cp -a --reflink=auto "$GOLDEN" "$WT/.lake/packages"
chmod -R u+w "$WT/.lake/packages"
cp -a "$MAIN/.lake/build" "$WT/.lake/build"
cp -a "$MAIN/.lake/config" "$WT/.lake/config"

echo "[setup-worktree] ready:"
echo "    cd $WT && lake build CLRSLean     # warm incremental build"
echo "    DO NOT run 'lake exe cache get' here — Mathlib is already provisioned."
