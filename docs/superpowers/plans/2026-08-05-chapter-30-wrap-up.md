# Chapter 30 Wrap-Up Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Consolidate Chapter 30's completed proof architecture, theorem entry points, cost conventions, verification surface, and optional-extension boundary without changing Lean semantics.

**Architecture:** Keep `CLRSLean/Chapter_30.lean` as the canonical reader-facing summary, while `docs/proof-map.md` owns the maintainer closure record and `docs/proof-status-board.md` owns the compact portfolio view. Record the reusable same-execution/same-circuit lesson in the chapter formalization skill. The progress CSV, generated README table, imports, definitions, theorem statements, and proofs remain unchanged.

**Tech Stack:** Lean 4 module documentation with Verso name markup, Markdown status ledgers, repository Python checks, Lake builds, and Git.

---

### Task 1: Consolidate the canonical Chapter 30 guide

**Files:**
- Modify: `CLRSLean/Chapter_30.lean:22-35`

- [ ] **Step 1: Run the reader-guide acceptance check and verify it fails**

Run:

```bash
rg -n '^## Proof architecture|^## Cost conventions|^## Reviewed boundary' \
  CLRSLean/Chapter_30.lean
```

Expected: exit 1 with no matches, proving that the canonical guide does not yet
expose the three required reader sections.

- [ ] **Step 2: Replace the module comment with the consolidated guide**

Keep all imports and namespaces unchanged. Replace only the existing `/-! ...
-/` block with:

```lean
/-! # Chapter 30 - Polynomials and the FFT

Sections 30.1--30.3 are complete within the exact generic-arithmetic
functional boundary. The 46 tracked theorem groups are all kernel checked;
the chapter has no remaining main-text group inside this reviewed model.

## Proof architecture

The development follows the textbook dependency chain. Section 30.1 fixes
coefficient and point-value representations and proves their bridges and
operations. Section 30.2 builds generic DFT algebra on those representations,
proves inversion and convolution, implements the recursive radix-2 FFT, and
uses it for polynomial multiplication. Section 30.3 factors the same transform
into bit-reversal copying and globally ordered iterative stages, then stores
those stages as an evaluated layered circuit whose size and depth are read from
the same syntax.

## Section 30.1 - Representing polynomials

- {name}`CLRS.Chapter30.coeffVector_vectorToPolynomial` and
  {name}`CLRS.Chapter30.vectorToPolynomial_coeffVector` give the fixed-capacity
  coefficient round trips.
- {name}`CLRS.Chapter30.interpolate_pointValues_roundTrip` proves the
  distinct-node interpolation round trip.
- {name}`CLRS.Chapter30.hornerEval_correct` connects Horner evaluation to
  polynomial evaluation.
- {name}`CLRS.Chapter30.schoolbookMul_correct` and
  {name}`CLRS.Chapter30.schoolbookMulWork_exact` prove schoolbook
  multiplication and its exact represented work.

## Section 30.2 - The DFT and recursive FFT

- {name}`CLRS.Chapter30.idft_dft`, {name}`CLRS.Chapter30.dft_idft`, and
  {name}`CLRS.Chapter30.dft_cyclicConvolution` provide the Fourier algebra.
- {name}`CLRS.Chapter30.recursiveFFT_eq_dft` proves the executable recursive
  radix-2 transform computes the generic DFT.
- {name}`CLRS.Chapter30.complexFFTMultiply_correct` gives the unconditional
  automatically padded complex polynomial-multiplication wrapper.
- {name}`CLRS.Chapter30.paddedFFTWork_allInput_bigTheta` and
  {name}`CLRS.Chapter30.fftMultiplyWork_allInput_bigTheta` give the all-input
  {lit}`Theta(n log n)` work bounds.

## Section 30.3 - Iterative FFT and the layered network

- {name}`CLRS.Chapter30.bitReverseEquiv_testBit` and
  {name}`CLRS.Chapter30.bitReverseCopy_involutive` specify bit reversal.
- {name}`CLRS.Chapter30.iterativeRadix2FFT_eq_recursiveFFT` and
  {name}`CLRS.Chapter30.iterativeRadix2FFT_eq_dft` close the iterative
  algorithmic and algebraic bridges.
- {name}`CLRS.Chapter30.iterativeRadix2FFTExec_totalWork` and
  {name}`CLRS.Chapter30.paddedIterativeFFTWork_allInput_bigTheta` attach exact
  and asymptotic work to the executed iterative transform.
- {name}`CLRS.Chapter30.fftNetwork_eval`,
  {name}`CLRS.Chapter30.fftNetwork_butterflyCount`, and
  {name}`CLRS.Chapter30.fftNetwork_primitiveDepth` connect the stored circuit
  to transform semantics, exact size, and exact depth.

## Cost conventions

The functional and circuit models intentionally charge different objects:

- recursive or iterative arithmetic work is {lit}`2 * k * 2^k`;
- iterative total work, including bit-reversal moves, is
  {lit}`2^k + 2 * k * 2^k`;
- the layered circuit contains {lit}`k * 2^(k-1)` butterflies and
  {lit}`3 * k * 2^(k-1)` primitive arithmetic gates; and
- butterfly depth is {lit}`k`, while primitive arithmetic depth is
  {lit}`2 * k`.

Execution charges successive twiddle generation and data movement. Circuit
counting treats fixed twiddle powers as constants and bit reversal as wiring.

## Reviewed boundary

The represented algorithms are pure functions over fixed-length and
power-of-two vectors, over exact generic ring or characteristic-zero field
arithmetic as required by each theorem. Mutable arrays, aliasing, imperative
loops, RAM/cache/allocator and hardware costs, floating-point approximation and
numerical stability, concrete parallel scheduling, number-theoretic-transform
specialization, external code generation, exercises, and Problems 30-1 through
30-6 are optional extension tracks rather than missing core groups.
-/
```

- [ ] **Step 3: Re-run the reader-guide acceptance check**

Run:

```bash
rg -n '^## Proof architecture|^## Cost conventions|^## Reviewed boundary' \
  CLRSLean/Chapter_30.lean
```

Expected: three matches.

- [ ] **Step 4: Compile the canonical guide and resolve every name reference**

Run:

```bash
lake build +CLRSLean.Chapter_30
```

Expected: exit 0 and `Built CLRSLean.Chapter_30`; existing non-blocking linter
or documentation-role warnings may remain, but there must be no unknown-name or
Verso name-resolution error.

- [ ] **Step 5: Verify the change is documentation-only**

Run:

```bash
git diff --word-diff=porcelain -- CLRSLean/Chapter_30.lean
```

Expected: only the module comment changes; imports and namespace declarations
are byte-for-byte unchanged.

- [ ] **Step 6: Commit the canonical guide**

```bash
git add CLRSLean/Chapter_30.lean
git diff --cached --check
git commit -m "docs(ch30): organize the completed proof guide"
```

### Task 2: Add the maintainer completion boundary

**Files:**
- Modify: `docs/proof-map.md` immediately after the Section 30.3 chapter-boundary paragraph
- Modify: `docs/proof-status-board.md` in the Chapter 30 table row

- [ ] **Step 1: Run the completion-entry acceptance check and verify it fails**

Run:

```bash
rg -n '^### Chapter 30 completion boundary$' docs/proof-map.md
```

Expected: exit 1 with no match.

- [ ] **Step 2: Add the proof-map completion subsection**

Insert the following after the existing Section 30.3 chapter-boundary bullet and
before `## Chapter 31`:

```markdown
### Chapter 30 completion boundary

- Status: `main-proof-complete`.
- Progress ledger: 46 tracked theorem groups, 46 proved, zero missing core
  groups.
- Stable interface and closure tests:
  - `Tests/Chapter_30_Interface.lean`
  - `Tests/Chapter_30_DFT_Interface.lean`
  - `Tests/Chapter_30_RecursiveFFT_Interface.lean`
  - `Tests/Chapter_30_PolynomialMultiplication_Interface.lean`
  - `Tests/Chapter_30_Milestone1_Closure.lean`
  - `Tests/Chapter_30_BitReversal_Interface.lean`
  - `Tests/Chapter_30_IterativeFFT_Interface.lean`
  - `Tests/Chapter_30_ParallelFFT_Interface.lean`
  - `Tests/Chapter_30_Milestone2_Closure.lean`
- Closure audits:
  - `docs/proof-audits/chapter-30-milestone-1-2026-08-05.md`
  - `docs/proof-audits/chapter-30-milestone-2-2026-08-05.md`
- The exact generic-arithmetic functional boundary is closed. Mutable and
  in-place arrays, machine-level costs, floating-point analysis, concrete
  scheduling, NTT specialization, code generation, exercises, and Problems
  30-1 through 30-6 are optional new layers, not missing Chapter 30 core work.
```

- [ ] **Step 3: Clarify the proof-status-board row**

Replace the Chapter 30 row with this single Markdown table row:

```markdown
| Chapter 30 | Sections 30.1--30.3: polynomial representations, generic DFT algebra, recursive and iterative radix-2 FFT correctness, FFT multiplication, execution-attached `Theta(n log n)` work, and evaluated layered-circuit size/depth | Optional extensions only (zero missing core groups): mutable/in-place arrays, RAM/cache/hardware costs, floating-point error, concrete scheduling, NTT/code generation, exercises, and Problems 30-1 through 30-6 |
```

- [ ] **Step 4: Verify closure records and count all nine tests**

Run:

```bash
rg -n '^### Chapter 30 completion boundary$|46 tracked theorem groups|zero missing core groups' \
  docs/proof-map.md docs/proof-status-board.md
rg -n '^  - `Tests/Chapter_30_.*\.lean`$' docs/proof-map.md
```

Expected: the completion heading and both zero-gap statements are present; the
second command returns exactly nine test entries.

- [ ] **Step 5: Check generated status sources remain unchanged and current**

Run:

```bash
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
git diff --exit-code -- docs/clrs-proof-progress.csv CLRSLean/Progress.lean README.md
```

Expected: both scripts exit 0 and the three generated/status-source files have
no diff.

- [ ] **Step 6: Commit the maintainer closure record**

```bash
git add docs/proof-map.md docs/proof-status-board.md
git diff --cached --check
git commit -m "docs(ch30): record the final completion boundary"
```

### Task 3: Record the reusable execution-and-circuit lesson

**Files:**
- Modify: `.codex/skills/clrs-chapter-formalization/SKILL.md` in `## Iteration Log`

- [ ] **Step 1: Verify the lesson is absent (RED)**

Run:

```bash
rg -n 'same execution record|same stored circuit syntax' \
  .codex/skills/clrs-chapter-formalization/SKILL.md
```

Expected: exit 1 with no match.

- [ ] **Step 2: Confirm the recorded Chapter 30 failure that motivates the lesson**

Run:

```bash
git show --no-ext-diff 7dcb1ec -- \
  CLRSLean/Chapter_30/Section_30_3_Efficient_FFT_Implementations/ParallelFFT.lean \
  | rg 'circuit : FFTStageCircuit|layer\.circuit\.eval|layer\.circuit\.butterflyCount|layer\.circuit\.butterflyDepth'
```

Expected: four matches showing the repair that attached evaluation, count, and
depth to the stored circuit. This historical defect is the observed failing
baseline for the skill edit; no synthetic subagent pressure test is needed.

- [ ] **Step 3: Add the minimal iteration-log lesson (GREEN)**

Append this bullet after the Chapter 27 completion entry and before
`## Honesty Rules`:

```markdown
- Chapter 30 FFT closure pass: an algorithmic cost theorem should read counters
  from the same execution record whose value is proved correct, rather than a
  detached closed-form recurrence. Likewise, circuit evaluation, gate count,
  and depth should recurse over the same stored circuit syntax; descriptive
  metadata is not a verified circuit bound.
```

- [ ] **Step 4: Run retrieval, application, and counterexample checks**

Run:

```bash
rg -n -C 2 'Chapter 30 FFT closure pass|same execution record|same stored circuit syntax' \
  .codex/skills/clrs-chapter-formalization/SKILL.md
```

Expected: one compact entry that answers all three checks:

1. Retrieval: a future chapter pass can find the rule using `execution record`
   or `circuit syntax`.
2. Application: detached cost formulas and descriptive circuit metadata are
   explicitly rejected.
3. Counterexample: the rule is scoped to claimed execution/circuit bounds and
   does not require every purely mathematical theorem to introduce an
   execution record.

- [ ] **Step 5: Verify skill structure and scope**

Run:

```bash
sed -n '1,8p' .codex/skills/clrs-chapter-formalization/SKILL.md
tail -n 35 .codex/skills/clrs-chapter-formalization/SKILL.md
git diff --check -- .codex/skills/clrs-chapter-formalization/SKILL.md
```

Expected: YAML frontmatter is unchanged; only one iteration-log bullet is
added; no placeholder, new supporting file, or unrelated skill rewrite appears.

- [ ] **Step 6: Commit the reusable lesson**

```bash
git add .codex/skills/clrs-chapter-formalization/SKILL.md
git diff --cached --check
git commit -m "docs(skill): record execution-bound cost discipline"
```

### Task 4: Run Chapter 30 closure verification

**Files:**
- Verify: `CLRSLean/Chapter_30.lean`
- Verify: `CLRSLean/Chapter_30/**`
- Verify: `Tests/Chapter_30_*.lean`
- Verify: repository status and documentation ledgers

- [ ] **Step 1: Verify diff scope and absence of unfinished Lean declarations**

Run:

```bash
git diff --check origin/main...HEAD
git diff --name-only origin/main...HEAD
if rg -n '\b(sorry|admit|axiom)\b' CLRSLean/Chapter_30 -g '*.lean'; then
  exit 1
else
  echo 'Chapter 30 unfinished-proof scan clean'
fi
```

Expected: the diff contains only the approved spec, plan, chapter guide, proof
map, proof-status board, and skill file. The unfinished-proof scan prints the
clean message.

- [ ] **Step 2: Build Chapter 30**

Run:

```bash
lake build +CLRSLean.Chapter_30
```

Expected: exit 0.

- [ ] **Step 3: Run all nine Chapter 30 tests**

Run:

```bash
for test_file in Tests/Chapter_30_*.lean; do
  echo "==> $test_file"
  lake env lean "$test_file" || exit 1
done
```

Expected: nine file banners and nine exit-0 Lean runs.

- [ ] **Step 4: Inspect both closure axiom surfaces**

Run:

```bash
lake env lean Tests/Chapter_30_Milestone1_Closure.lean
lake env lean Tests/Chapter_30_Milestone2_Closure.lean
```

Expected: printed dependencies are limited to `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` or project-defined axiom appears.

- [ ] **Step 5: Run progress and repository consistency checks**

Run:

```bash
uv run python scripts/check_progress_csv.py
uv run python scripts/gen_readme_table.py --check
uv run python scripts/check_repository.py
```

Expected: 35 chapters, 1793 tracked and 1793 proved; README current; repository
checks passed.

- [ ] **Step 6: Run the full proof build**

Run:

```bash
lake build CLRSLean
```

Expected: exit 0. Record pre-existing non-blocking linter/documentation
warnings, but do not run `lake build :literateHtml` or any website command.

- [ ] **Step 7: Verify the final branch state**

Run:

```bash
git status --short
git log --oneline --decorate origin/main..HEAD
```

Expected: clean status and the design, plan, reader-guide, completion-boundary,
and skill-discipline commits in order.
