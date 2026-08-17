#!/usr/bin/env bash
# extract_chapter.sh — extract one chapter's text from the reference corpus PDF.
# Usage: extract_chapter.sh <chapter_no>
# Config: ~/.config/clrs-audit/config — line 1 = absolute corpus directory.
# Output: writes <corpus>/chNN.txt; prints its path on stdout.
set -euo pipefail

parse_config() {
  local cfg="$HOME/.config/clrs-audit/config"
  if [[ ! -f "$cfg" ]]; then
    echo "missing config: $cfg (line 1 = corpus directory)" >&2
    return 1
  fi
  head -n1 "$cfg" | tr -d '[:space:]'
}

find_pdf() {
  local dir="$1" pdf
  pdf=$(find "$dir" -maxdepth 1 -iname '*.pdf' 2>/dev/null | head -n1)
  if [[ -z "$pdf" ]]; then
    echo "no PDF found in $dir" >&2
    return 1
  fi
  printf '%s' "$pdf"
}

cache_fulltext() {
  local pdf="$1" corpus="$2" txt="$corpus/book.txt"
  if [[ ! -f "$txt" || "$pdf" -nt "$txt" ]]; then
    pdftotext -layout "$pdf" "$txt"
  fi
  printf '%s' "$txt"
}

# Line number (1-based) where chapter N starts as a bare-number line, or empty.
chapter_start_line() {
  local txt="$1" n="$2"
  grep -n -E "^[[:space:]]*${n}[[:space:]]*$" "$txt" | head -n1 | cut -d: -f1
}

split_chapter() {
  local txt="$1" n="$2" start end
  start=$(chapter_start_line "$txt" "$n")
  if [[ -z "$start" ]]; then
    echo "chapter $n not found in $txt" >&2
    return 3
  fi
  end=$(chapter_start_line "$txt" "$((n + 1))")
  if [[ -z "$end" ]]; then
    sed -n "${start},\$p" "$txt"
  else
    sed -n "${start},$((end - 1))p" "$txt"
  fi
}

main() {
  local n="$1" corpus pdf txt out
  corpus=$(parse_config)
  pdf=$(find_pdf "$corpus")
  txt=$(cache_fulltext "$pdf" "$corpus")
  out="$corpus/ch$(printf '%02d' "$n").txt"
  split_chapter "$txt" "$n" > "$out"
  echo "$out"
}

if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
  if [[ $# -ne 1 ]]; then
    echo "usage: extract_chapter.sh <chapter_no>" >&2
    exit 2
  fi
  main "$1"
fi
