#!/usr/bin/env bash
# Unit tests for extract_chapter.sh. Run: bash tests/test_extract_chapter.sh
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SKILL_SCRIPT="$SCRIPT_DIR/scripts/extract_chapter.sh"
PASS=0; FAIL=0
ok()   { PASS=$((PASS+1)); }
bad()  { FAIL=$((FAIL+1)); echo "FAIL: $1"; }
assert_eq() { [[ "$1" == "$2" ]] && ok || bad "$3: got [$1] want [$2]"; }

source "$SKILL_SCRIPT"  # guarded by BASH_SOURCE check, defines functions only

# --- parse_config ---
OLD_HOME="$HOME"
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT

HOME="$T"  # no config file
if out=$(parse_config 2>&1); then rc=0; else rc=$?; fi
[[ $rc -eq 1 ]] && ok || bad "missing config should exit 1, got $rc"
echo "$out" | grep -q "missing config" && ok || bad "missing config should print message"

mkdir -p "$T/.config/clrs-audit"
printf '/tmp/my corpus/\n' > "$T/.config/clrs-audit/config"
out=$(parse_config)
assert_eq "$out" "/tmp/mycorpus/" "parse_config should trim whitespace"

# --- find_pdf ---
if out=$(find_pdf "$T" 2>&1); then rc=0; else rc=$?; fi
[[ $rc -eq 1 ]] && ok || bad "no pdf should exit 1"
touch "$T/a.pdf"
assert_eq "$(find_pdf "$T")" "$T/a.pdf" "find_pdf should return first pdf"

# --- split_chapter: bare-number style with header noise ---
cat > "$T/book.txt" <<'EOF'
Contents
1 The Role of Algorithms
2 Getting Started
1
The Role of Algorithms
intro text
2
Getting Started
2.1 Insertion sort
algo text
3
Growth of Functions
more
EOF
out=$(split_chapter "$T/book.txt" 2)
echo "$out" | grep -q "^Getting Started" && ok || bad "ch2 should start at title line"
echo "$out" | grep -q "algo text" && ok || bad "ch2 should include body"
echo "$out" | grep -q "Growth of Functions" && bad "ch2 should exclude ch3" || ok

# --- split_chapter: last chapter goes to EOF ---
out=$(split_chapter "$T/book.txt" 3)
echo "$out" | grep -q "more" && ok || bad "last chapter should reach EOF"

# --- split_chapter: missing chapter ---
if out=$(split_chapter "$T/book.txt" 9 2>&1); then rc=0; else rc=$?; fi
[[ $rc -eq 3 ]] && ok || bad "missing chapter should exit 3, got $rc"

# --- main end-to-end with stubbed pdftotext ---
mkdir -p "$T/bin" "$T/corpus"
cat > "$T/bin/pdftotext" <<'EOF'
#!/bin/bash
# stub: write fixture text to the last argument
cat > "${@: -1}" <<'INNER'
1
The Role of Algorithms
2
Getting Started
algo text
INNER
EOF
chmod +x "$T/bin/pdftotext"
printf "$T/corpus\n" > "$T/.config/clrs-audit/config"
touch "$T/corpus/book.pdf"
PATH="$T/bin:$PATH" HOME="$T" out=$(bash "$SKILL_SCRIPT" 2)
assert_eq "$out" "$T/corpus/ch02.txt" "main should print output path"
grep -q "algo text" "$T/corpus/ch02.txt" && ok || bad "main should extract ch2"

# --- main: usage error ---
HOME="$T" bash "$SKILL_SCRIPT" >/dev/null 2>&1; rc=$?
[[ $rc -eq 2 ]] && ok || bad "no args should exit 2, got $rc"

echo "PASS=$PASS FAIL=$FAIL"
[[ $FAIL -eq 0 ]]
