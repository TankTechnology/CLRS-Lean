#!/usr/bin/env bash
#
# refresh-golden.sh — build main's .lake and snapshot it as the "golden" packages
# used to provision worktrees. Also the RECOVERY runbook for a corrupted .lake
# (deleted/empty Mathlib after an OOM — see docs/build-and-agents.md).
#
# Usage:
#   scripts/refresh-golden.sh
#
# Config (env vars):
#   CLRS_WORKTREE_ROOT   default: $HOME/clrs-lean-worktrees
#   CLRS_GOLDEN_LAKE     default: $CLRS_WORKTREE_ROOT/golden-packages
#
set -euo pipefail

MAIN="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ROOT="${CLRS_WORKTREE_ROOT:-$HOME/clrs-lean-worktrees}"
GOLDEN="${CLRS_GOLDEN_LAKE:-$ROOT/golden-packages}"
cd "$MAIN"

# --- recover a corrupted/missing Mathlib build from the machine-global cache ---
if [ ! -e ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]; then
  echo "[refresh-golden] Mathlib build missing/corrupt — recovering from ~/.cache/mathlib"
  rm -rf .lake/packages/mathlib
  lake exe cache get
fi

echo "[refresh-golden] building CLRSLean (warm; only changed modules recompile)"
lake build CLRSLean

echo "[refresh-golden] snapshotting .lake/packages -> $GOLDEN"
mkdir -p "$ROOT"
rm -rf "$GOLDEN.tmp"
cp -a --reflink=auto "$MAIN/.lake/packages" "$GOLDEN.tmp"
rm -rf "$GOLDEN"
mv "$GOLDEN.tmp" "$GOLDEN"

n="$(find "$GOLDEN/mathlib/.lake/build/lib" -name '*.olean' 2>/dev/null | wc -l)"
echo "[refresh-golden] golden ready: $GOLDEN ($n mathlib oleans)"
