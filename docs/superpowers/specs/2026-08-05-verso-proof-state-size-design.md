# Verso proof-state output size reduction design

Date: 2026-08-05

Status: approved in conversation; written specification pending review

## Problem

The CLRS-Lean Pages build spends most of its time in the Verso literate HTML
stage.  A representative module,
`CLRSLean.Chapter_22.Section_22_3_DFS.S4_SCC`, has the following build sizes:

- Lean source: 69,394 bytes and 1,212 lines;
- Verso literate JSON: 5,660,083 bytes;
- raw Verso HTML: 471,269,572 bytes.

The raw page contains 3,711 rendered proof goals.  Those goal fragments occupy
468,721,796 bytes, or 99.46% of the page.  One 73,387-byte goal is expanded
1,033 times, accounting for 75,808,771 bytes by itself.  The compact literate
JSON shares repeated structures, but HTML rendering expands each tactic state
into a complete syntax-highlighted DOM subtree.

The deployed site does not expose these states.  `scripts/optimize_literate_html.py`
already removes every `.tactic-state` and `.tactic-toggle` while assembling
`_site`.  The current pipeline therefore generates roughly 3.3 GB of raw HTML,
copies it, parses it, and then deletes almost all of the pathological content.

## Goals

1. Prevent inline tactic proof states from entering raw literate HTML.
2. Preserve the reader-visible site: prose, Lean source, declaration anchors,
   navigation, search, and deployed URLs remain unchanged.
3. Keep the project-side change small and isolated instead of copying the
   Verso HTML generator into this repository.
4. Fail clearly when an upstream Verso change makes the local compatibility
   patch stale.
5. Detect future proof-state and page-size regressions before publishing.
6. Preserve manually triggered GitHub Actions so ordinary commits consume no
   Actions minutes.

## Non-goals

- Do not parallelize the Verso renderer in this change.
- Do not maintain a permanent CLRS-Lean fork of Verso.
- Do not change Lean declarations, proofs, module boundaries, or literate
  navigation.
- Do not restore interactive tactic states on the deployed reader site.
- Do not run a full Lean or Verso build on every commit or pull request.
- Do not remove the existing HTML optimizer in the first rollout.

## Chosen approach

Maintain one narrowly scoped patch in the CLRS-Lean repository.  The patch
changes the literate renderer's `HighlightHtmlM.Options` from its default
`inlineProofStates := true` to `inlineProofStates := false` when rendering
module bodies.

The behavioral change is applied before HTML serialization:

```text
Lean source
  -> literate JSON with proof-state data
  -> apply verified Verso compatibility patch
  -> Verso renders code without inline proof-state DOM
  -> raw HTML size gate
  -> existing site optimizer and rendering checks
  -> _site
```

The literate JSON continues to contain proof-state data produced by Lean.  This
change targets the dominant 3.3 GB HTML expansion without redesigning the
SubVerso extraction format.

## Components

### Tracked compatibility patch

`patches/verso/disable-inline-proof-states.patch` contains only the upstream
renderer change.  It is reviewed as normal repository code and remains
separate from project scripts and generated artifacts.

### Idempotent patch application

`scripts/apply_verso_patch.py` locates the checked-out Verso package under
`.lake/packages/verso` and applies the tracked patch with three explicit
outcomes:

1. unpatched expected source: apply successfully;
2. already patched source: report success without modifying it again;
3. neither expected state: fail with the Verso revision and a message that the
   compatibility patch must be reviewed.

The script never performs a package update, fetch, checkout, reset, or other
destructive dependency operation.

### Raw HTML regression gate

`scripts/check_literate_html_weight.py` scans generated `index.html` files and
fails if:

- any file contains `class="tactic-state"` or `class="tactic-toggle"`; or
- any raw HTML page exceeds a documented initial ceiling of 25 MiB.

The proof-state check is the correctness invariant.  The size ceiling is a
secondary guard against a different form of semantic-HTML explosion and can
be adjusted using measured evidence if a legitimate page later exceeds it.
The scan streams files instead of loading the full site into memory.

### Existing optimizer as defense in depth

`scripts/optimize_literate_html.py` initially retains its tactic-state removal
logic.  With the compatibility patch working, it should observe zero tactic
states, but retaining the removal is harmless and protects local or historical
raw output.  Removing that fallback is a separate future cleanup after at
least one successful production deployment.

## GitHub Actions policy

Both `.github/workflows/lean_action_ci.yml` and `.github/workflows/pages.yml`
remain `workflow_dispatch` only.  This work must not add `push`,
`pull_request`, scheduled, or chained automatic triggers.

The Pages workflow adds two bounded steps:

1. apply the Verso compatibility patch after dependency setup;
2. run the raw HTML regression gate after `lake build :literateHtml`.

Fast Python unit tests are intended for local development and explicit review.
The expensive full site build runs only when a maintainer manually starts the
Pages workflow or deliberately runs it locally before release.

## Error handling and maintenance

- Missing Verso checkout: fail and explain that dependency setup must run
  first.
- Patch already applied: succeed idempotently.
- Upstream source drift: fail before the expensive HTML build and print the
  detected revision.
- Residual tactic state: fail before `_site` assembly and artifact upload.
- Oversized page: list its relative path and measured byte count.
- Multiple violations: report all discovered pages in deterministic path
  order so one run gives a complete remediation list.

The dependency remains pinned by `lake-manifest.json`.  When Verso is updated,
the patch test is part of the dependency-update review.  If upstream later
adds a supported literate configuration for `inlineProofStates`, the local
patch should be replaced by that configuration rather than extended.

## Testing

### Fast tests

Unit tests cover:

- applying the patch to an unpatched fixture;
- applying it a second time without change;
- rejecting unexpected upstream source;
- detecting residual tactic-state markup across chunk boundaries;
- detecting a page above the size ceiling;
- accepting a bounded page with normal Lean markup;
- reporting violations in deterministic order;
- confirming both workflow files remain manual-only.

These tests use temporary files and do not build Lean or invoke GitHub Actions.

### Focused integration verification

Before merging, build a representative pathological module or the smallest
available literate target that exercises tactic rendering.  Confirm that raw
HTML contains the theorem source but no tactic-state DOM.  If Verso exposes no
module-level HTML target, perform one deliberate full literate build locally
or through the manually dispatched Pages workflow; do not add an automatic
per-commit build.

### Release verification

For the first deployment after the change, record:

- raw `.lake/build/literate-html` total size;
- largest raw page path and size;
- Verso HTML step duration;
- `_site` assembly duration;
- public-site smoke checks for representative chapter and support pages.

The baseline is approximately 3.3 GB raw output, a 471 MB largest page, about
24 minutes for Verso HTML, and 6–7 minutes for site assembly.  These numbers are
observational baselines, not guaranteed performance targets.

## Rollout and rollback

1. Merge the patch, scripts, tests, workflow wiring, and documentation.
2. Manually dispatch one Pages deployment.
3. Compare recorded size and duration metrics with the baseline.
4. Verify the public site before declaring the rollout successful.

Rollback consists of reverting the workflow patch step and associated files.
The existing optimizer remains capable of producing the prior deployed-site
shape, so rollback does not require content or proof changes.

## Acceptance criteria

- No generated raw page contains inline tactic-state or tactic-toggle markup.
- The raw S4 SCC page is below the 25 MiB guard when included in verification.
- Existing site optimizer, navigation, rendering, and preparation tests pass.
- The published site preserves its current reader-visible content and routes.
- Both GitHub Actions workflows remain manually triggered only.
- No full build is added to ordinary commit or pull-request validation.
