# Verso Proof-State Size Reduction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stop Verso from expanding inline tactic proof states into raw CLRS-Lean HTML while preserving the existing reader-visible site and manual-only GitHub Actions policy.

**Architecture:** Keep a one-line upstream compatibility patch under `patches/verso/`, apply it idempotently after dependency setup, and reject raw HTML that still contains tactic-state DOM or exceeds 25 MiB per page. Retain the existing postprocessor as defense in depth and validate the change with fast Python tests plus one focused single-module render.

**Tech Stack:** Python 3 standard library, Git unified patches, Lean/Lake, Verso literate HTML, GitHub Actions YAML, `unittest`.

---

## File map

- Create `patches/verso/disable-inline-proof-states.patch`: the isolated one-line Verso renderer change.
- Create `scripts/apply_verso_patch.py`: idempotent, fail-fast compatibility-patch application.
- Create `scripts/test_apply_verso_patch.py`: CLI-level red/green tests against real temporary Git repositories.
- Create `scripts/check_literate_html_weight.py`: streaming raw-page guard.
- Create `scripts/test_check_literate_html_weight.py`: CLI-level tactic-state, size, boundary, and ordering tests.
- Create `scripts/test_workflow_policy.py`: manual-trigger and Pages step-order regression tests.
- Modify `.github/workflows/pages.yml`: apply the patch and run the raw HTML guard without changing triggers.
- Modify `docs/site-architecture.md`: document the patched publishing pipeline and local commands.
- Modify `README.md`: document the explicit publishing-only build sequence.
- Modify `CLAUDE.md`: correct the stale automatic-deploy wording and document the publishing gate.

## Task 1: Idempotent Verso compatibility patch

**Files:**

- Create: `scripts/test_apply_verso_patch.py`
- Create: `scripts/apply_verso_patch.py`
- Create: `patches/verso/disable-inline-proof-states.patch`

- [ ] **Step 1: Write failing CLI tests**

Create a temporary Git repository containing the expected upstream file and invoke the not-yet-existing script as a subprocess. Cover first application, second application, source drift, and a missing checkout. The test source must contain the exact renderer context:

```python
UNPATCHED_SOURCE = """private def renderModBody := do
  let emitCtx := { ctx with
    options := {}
    traverseContext := { currentModule := mod.name }
    codeOptions := {}
  }
"""

def run_script(verso_dir: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(SCRIPT),
            "--verso-dir",
            str(verso_dir),
            "--patch",
            str(PATCH),
        ],
        text=True,
        capture_output=True,
        check=False,
    )
```

Assertions:

```python
self.assertEqual(0, first.returncode, first.stderr)
self.assertIn("inlineProofStates := false", source.read_text())
self.assertEqual("applied", first.stdout.strip())

self.assertEqual(0, second.returncode, second.stderr)
self.assertEqual("already-applied", second.stdout.strip())

self.assertEqual(1, drift.returncode)
self.assertIn("incompatible Verso source", drift.stderr)

self.assertEqual(1, missing.returncode)
self.assertIn("Verso checkout does not exist", missing.stderr)
```

- [ ] **Step 2: Run the tests and verify RED**

Run:

```bash
python3 -m unittest scripts.test_apply_verso_patch
```

Expected: FAIL because `scripts/apply_verso_patch.py` does not exist, producing a nonzero subprocess status instead of the expected success.

- [ ] **Step 3: Add the tracked patch**

Create `patches/verso/disable-inline-proof-states.patch` with this complete change:

```diff
diff --git a/src/verso-literate-html/LiterateHtmlMain.lean b/src/verso-literate-html/LiterateHtmlMain.lean
--- a/src/verso-literate-html/LiterateHtmlMain.lean
+++ b/src/verso-literate-html/LiterateHtmlMain.lean
@@ -212,7 +212,7 @@ private def renderModBody (mod : LitMod) (resolved : ResolvedConfig)
   let emitCtx := { ctx with
     options := {}
     traverseContext := { currentModule := mod.name }
-    codeOptions := {}
+    codeOptions := { inlineProofStates := false }
   }
   let hlCtx : HighlightHtmlM.Context Literate := { emitCtx with options := emitCtx.codeOptions }
```

- [ ] **Step 4: Implement minimal patch application**

Implement `scripts/apply_verso_patch.py` with:

```python
#!/usr/bin/env python3
from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_VERSO_DIR = ROOT / ".lake" / "packages" / "verso"
DEFAULT_PATCH = ROOT / "patches" / "verso" / "disable-inline-proof-states.patch"


class PatchError(RuntimeError):
    pass


def git_apply_check(verso_dir: Path, patch: Path, *, reverse: bool = False) -> bool:
    command = ["git", "-C", str(verso_dir), "apply"]
    if reverse:
        command.append("--reverse")
    command.extend(["--check", str(patch)])
    return subprocess.run(command, capture_output=True, text=True, check=False).returncode == 0


def revision(verso_dir: Path) -> str:
    result = subprocess.run(
        ["git", "-C", str(verso_dir), "rev-parse", "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def apply_verso_patch(verso_dir: Path, patch: Path) -> str:
    if not verso_dir.is_dir():
        raise PatchError(f"Verso checkout does not exist: {verso_dir}")
    if not patch.is_file():
        raise PatchError(f"Verso patch does not exist: {patch}")
    if git_apply_check(verso_dir, patch):
        subprocess.run(
            ["git", "-C", str(verso_dir), "apply", str(patch)],
            check=True,
        )
        return "applied"
    if git_apply_check(verso_dir, patch, reverse=True):
        return "already-applied"
    raise PatchError(
        "incompatible Verso source at revision "
        f"{revision(verso_dir)}; review {patch} against the pinned dependency"
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verso-dir", type=Path, default=DEFAULT_VERSO_DIR)
    parser.add_argument("--patch", type=Path, default=DEFAULT_PATCH)
    args = parser.parse_args()
    try:
        print(apply_verso_patch(args.verso_dir.resolve(), args.patch.resolve()))
    except (PatchError, subprocess.CalledProcessError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
```

- [ ] **Step 5: Run the tests and verify GREEN**

Run:

```bash
python3 -m unittest scripts.test_apply_verso_patch
```

Expected: four tests pass with no warnings.

- [ ] **Step 6: Commit Task 1**

```bash
git add patches/verso/disable-inline-proof-states.patch scripts/apply_verso_patch.py scripts/test_apply_verso_patch.py
git commit -m "build(site): disable inline Verso proof states"
```

## Task 2: Streaming raw HTML regression gate

**Files:**

- Create: `scripts/test_check_literate_html_weight.py`
- Create: `scripts/check_literate_html_weight.py`

- [ ] **Step 1: Write failing CLI tests**

Exercise the future script entirely through `subprocess.run`. Create temporary site trees with `index.html` pages and assert:

```python
self.assertEqual(0, clean.returncode, clean.stderr)
self.assertIn("checked 1 raw HTML pages", clean.stdout)

self.assertEqual(1, tactic.returncode)
self.assertIn("inline tactic-state markup", tactic.stderr)

self.assertEqual(1, oversized.returncode)
self.assertIn("exceeds 100 bytes", oversized.stderr)

self.assertLess(
    multiple.stderr.index("a/index.html"),
    multiple.stderr.index("z/index.html"),
)
```

For the boundary case, write 65,530 bytes of ordinary text before `<span class="other tactic-state">` so the tag crosses the guard's 64 KiB input boundary. Expect the same tactic-state failure.

- [ ] **Step 2: Run the tests and verify RED**

Run:

```bash
python3 -m unittest scripts.test_check_literate_html_weight
```

Expected: FAIL because `scripts/check_literate_html_weight.py` does not exist.

- [ ] **Step 3: Implement the streaming guard**

Create `scripts/check_literate_html_weight.py` with a small HTML parser and deterministic violation model:

```python
#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from html.parser import HTMLParser
from pathlib import Path

DEFAULT_MAX_PAGE_BYTES = 25 * 1024 * 1024
READ_CHUNK_BYTES = 64 * 1024
TACTIC_CLASSES = {"tactic-state", "tactic-toggle"}


@dataclass(frozen=True, order=True)
class Violation:
    path: Path
    message: str


class TacticMarkupDetector(HTMLParser):
    def __init__(self) -> None:
        super().__init__(convert_charrefs=False)
        self.found: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._inspect(attrs)

    def handle_startendtag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        self._inspect(attrs)

    def _inspect(self, attrs: list[tuple[str, str | None]]) -> None:
        for name, value in attrs:
            if name.lower() == "class" and value:
                self.found.update(TACTIC_CLASSES.intersection(value.split()))


def inspect_page(path: Path, max_page_bytes: int) -> list[str]:
    size = path.stat().st_size
    messages: list[str] = []
    if size > max_page_bytes:
        messages.append(f"size {size} exceeds {max_page_bytes} bytes")
        return messages
    parser = TacticMarkupDetector()
    with path.open("r", encoding="utf-8", errors="replace") as stream:
        while chunk := stream.read(READ_CHUNK_BYTES):
            parser.feed(chunk)
    parser.close()
    for class_name in sorted(parser.found):
        messages.append(f"inline {class_name} markup")
    return messages


def check_site(root: Path, max_page_bytes: int) -> tuple[int, list[Violation]]:
    pages = sorted(root.rglob("index.html"))
    violations = [
        Violation(page.relative_to(root), message)
        for page in pages
        for message in inspect_page(page, max_page_bytes)
    ]
    if not pages:
        violations.append(Violation(Path("."), "no index.html pages found"))
    return len(pages), sorted(violations)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("site", type=Path)
    parser.add_argument("--max-page-bytes", type=int, default=DEFAULT_MAX_PAGE_BYTES)
    args = parser.parse_args()
    if not args.site.is_dir():
        print(f"error: site directory does not exist: {args.site}", file=sys.stderr)
        return 1
    pages, violations = check_site(args.site.resolve(), args.max_page_bytes)
    if violations:
        for violation in violations:
            print(f"{violation.path}: {violation.message}", file=sys.stderr)
        return 1
    print(f"checked {pages} raw HTML pages; max page size {args.max_page_bytes} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
```

- [ ] **Step 4: Run the tests and verify GREEN**

Run:

```bash
python3 -m unittest scripts.test_check_literate_html_weight
```

Expected: tactic-state, size, boundary, ordering, and clean-page tests all pass.

- [ ] **Step 5: Commit Task 2**

```bash
git add scripts/check_literate_html_weight.py scripts/test_check_literate_html_weight.py
git commit -m "build(site): guard raw literate HTML weight"
```

## Task 3: Wire the manual Pages workflow

**Files:**

- Create: `scripts/test_workflow_policy.py`
- Modify: `.github/workflows/pages.yml`

- [ ] **Step 1: Write the failing workflow-policy test**

The test reads both workflow files as text. It must assert that the trigger header contains `workflow_dispatch:` and excludes `push:`, `pull_request:`, `schedule:`, and `workflow_run:`. It must also assert this ordering in `pages.yml`:

```python
patch_at = pages.index("python3 scripts/apply_verso_patch.py")
build_at = pages.index("lake build :literateHtml")
guard_at = pages.index("python3 scripts/check_literate_html_weight.py")
prepare_at = pages.index("python3 scripts/prepare_literate_site.py")
self.assertLess(patch_at, build_at)
self.assertLess(build_at, guard_at)
self.assertLess(guard_at, prepare_at)
```

- [ ] **Step 2: Run the test and verify RED**

Run:

```bash
python3 -m unittest scripts.test_workflow_policy
```

Expected: FAIL because the Pages workflow does not yet invoke the patch applicator or raw HTML guard.

- [ ] **Step 3: Add the two bounded workflow steps**

After `leanprover/lean-action`, add:

```yaml
      - name: Disable inline Verso proof states
        run: python3 scripts/apply_verso_patch.py
```

After `Build Verso literate HTML`, add:

```yaml
      - name: Check raw Verso HTML weight
        run: python3 scripts/check_literate_html_weight.py "${{ steps.build-site.outputs.path }}"
```

Do not modify either workflow's `on:` block.

- [ ] **Step 4: Run the workflow-policy test and verify GREEN**

Run:

```bash
python3 -m unittest scripts.test_workflow_policy
```

Expected: workflow ordering passes and both workflows remain manual-only.

- [ ] **Step 5: Commit Task 3**

```bash
git add .github/workflows/pages.yml scripts/test_workflow_policy.py
git commit -m "ci(site): gate manual Verso publishing output"
```

## Task 4: Document and verify the publishing path

**Files:**

- Modify: `docs/site-architecture.md`
- Modify: `README.md`
- Modify: `CLAUDE.md`
- Modify: this plan to check completed steps

- [ ] **Step 1: Update publishing documentation**

Document the exact local sequence:

```bash
python3 scripts/apply_verso_patch.py
lake build :literateHtml
VERSO_OUT="$(lake query :literateHtml)"
python3 scripts/check_literate_html_weight.py "$VERSO_OUT"
python3 scripts/check_literate_html_freshness.py "$VERSO_OUT"
python3 scripts/prepare_literate_site.py "$VERSO_OUT" _site
```

Explain that dependency setup or a provisioned worktree must exist before patch application, tactic states are removed before serialization, the optimizer remains a fallback, and both GitHub workflows are manually dispatched only. Correct `CLAUDE.md` so it no longer says Pages deploys automatically on push.

- [ ] **Step 2: Run all fast site tests**

Run:

```bash
python3 -m unittest \
  scripts.test_apply_verso_patch \
  scripts.test_check_literate_html_weight \
  scripts.test_workflow_policy \
  scripts.test_optimize_literate_html \
  scripts.test_prepare_literate_site \
  scripts.test_check_literate_rendering \
  scripts.test_literate_config \
  scripts.test_literate_navigation
```

Expected: all tests pass with zero failures.

- [ ] **Step 3: Run repository and diff checks**

Run:

```bash
python3 scripts/check_repository.py
git diff --check origin/main...HEAD
```

Expected: repository checks succeed and the diff has no whitespace errors.

- [ ] **Step 4: Apply the patch to the pinned real Verso checkout twice**

Provision an isolated `.lake` for this worktree from the repository's golden package/build cache. Then run:

```bash
python3 scripts/apply_verso_patch.py
python3 scripts/apply_verso_patch.py
```

Expected output is `applied` followed by `already-applied`. Confirm the dependency checkout is dirty only at `src/verso-literate-html/LiterateHtmlMain.lean`.

- [ ] **Step 5: Build only the patched Verso HTML executable**

Resolve the package target with `lake query` and build only `verso-literate-html`, not the full CLRS-Lean library or full site. Expected: the executable rebuild exits 0 against the pinned dependency.

- [ ] **Step 6: Render the cached S4 SCC module only**

Create a temporary one-line module map by selecting `CLRSLean.Chapter_22.Section_22_3_DFS.S4_SCC` from the cached `.lake/build/literate-module-map`. Invoke the patched `verso-literate-html` executable with that map and no `literate.toml`, then run:

```bash
python3 scripts/check_literate_html_weight.py "$FOCUSED_OUT"
```

Expected: one raw module page passes, contains the Lean theorem source, contains no tactic-state/tactic-toggle elements, and is below 25 MiB. Record its exact size and render duration; do not run the full site build.

- [ ] **Step 7: Re-run the complete fast verification suite**

Run the commands from Steps 2 and 3 again after integration verification. Read the full output and confirm zero failures before making a completion claim.

- [ ] **Step 8: Mark the plan complete and commit documentation**

Change each checkbox in this plan from `[ ]` to `[x]`, then commit:

```bash
git add README.md CLAUDE.md docs/site-architecture.md docs/superpowers/plans/2026-08-05-verso-proof-state-size.md
git commit -m "docs(site): record proof-state build guard"
```

## Final acceptance audit

- [ ] The compatibility patch is one renderer option change and applies idempotently.
- [ ] Unexpected Verso source fails before the expensive site build.
- [ ] Raw HTML tactic states and pages above 25 MiB fail deterministically.
- [ ] The existing optimizer remains unchanged as defense in depth.
- [ ] Both workflow files remain `workflow_dispatch` only.
- [ ] No full site build runs automatically or during ordinary commit validation.
- [ ] Fast tests, repository checks, focused executable build, and focused S4 render all pass.
