#!/usr/bin/env bash
# scripts/check.sh — fast single-file proof check for CLRS-Lean
#
# Usage:
#   scripts/check.sh <file>               tier 1: elaborate only  (~5s)
#   scripts/check.sh --build <file>        tier 2: build .olean    (~5s)
#   scripts/check.sh --old                 tier 3: skip trans deps (~3s)
#   scripts/check.sh                       tier 4: full build     (~6s)
#   scripts/check.sh --reconfigure         tier 5: cold build
#
# The script normalises the file path so you can pass either
#   scripts/check.sh CLRSLean/Chapter_25/Section_25_2_Floyd_Warshall.lean
# or
#   scripts/check.sh Chapter_25/Section_25_2_Floyd_Warshall
# or just a module name.

set -euo pipefail

cd "$(dirname "$0")/.."

# Ensure elan + uv are on PATH
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

mode="lean"
file=""

while [[ $# -gt 0 ]]; do
  case "$1" in
    --build)   mode="build"; shift ;;
    --old)     mode="old"; shift ;;
    --cold)    mode="cold"; shift ;;
    --rehash)  mode="rehash"; shift ;;
    *)         file="$1"; shift ;;
  esac
done

case "$mode" in
  lean)
    if [[ -z "$file" ]]; then
      echo "Usage: scripts/check.sh [--build|--old|--cold|--rehash] <file.lean>"
      exit 1
    fi
    # Normalise: strip CLRSLean/ prefix if present, then re-add
    file="${file#CLRSLean/}"
    file="CLRSLean/${file}"
    echo "→ lake lean $file"
    exec lake lean "$file"
    ;;
  build)
    if [[ -z "$file" ]]; then
      echo "→ lake build CLRSLean (full)"
      exec lake build CLRSLean
    fi
    # Turn file path into module path
    module="${file#CLRSLean/}"
    module="${module%.lean}"
    module="${module//\//.}"
    echo "→ lake build $module"
    exec lake build "$module"
    ;;
  old)
    echo "→ lake build --old CLRSLean"
    exec lake build --old CLRSLean
    ;;
  cold)
    echo "→ lake build --reconfigure CLRSLean"
    exec lake build --reconfigure CLRSLean
    ;;
  rehash)
    echo "→ lake build --rehash CLRSLean"
    exec lake build --rehash CLRSLean
    ;;
esac
