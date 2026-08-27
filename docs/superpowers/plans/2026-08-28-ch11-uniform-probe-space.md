# Uniform Open-Addressing Probe Space Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove that the existing Chapter 11 probe-tail product and expected-probe bounds arise from an explicit uniform permutation of table slots.

**Architecture:** Add small definitions, counting, and probability modules behind a stable `UniformProbe` facade.  Reuse finite expectation and permutation-counting infrastructure; retain `probeTail` unchanged and prove the equality to it.

**Tech Stack:** Lean 4.32, Mathlib finite permutations/Finsets/factorials, `CLRS.Probability.fintypeExpect`, existing Chapter 11 open-addressing tail bounds.

---

### Task 1: Pin the explicit-model interface

**Files:**
- Modify: the focused Chapter 11 interface test selected by the section facade.

- [ ] Add failing checks for `firstProbesOccupied`,
  `uniformProbeTailProbability_eq_probeTail`,
  `uniformUnsuccessfulProbeCount`,
  `uniformUnsuccessfulExpectedProbes_eq`, and the explicit expectation bound.
- [ ] Run only that interface test and confirm the new names are absent while
  existing Section 11.4 checks remain green.

### Task 2: Define the sample event and probe count

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_11/Section_11_4_Open_Addressing/UniformProbe/Definitions.lean`
- Create: `CLRSLean/FourthEdition/Chapter_11/Section_11_4_Open_Addressing/UniformProbe.lean`

- [ ] Define the occupied-prefix event over `Equiv.Perm (Fin m)`.
- [ ] Define the bounded unsuccessful probe-count variable for non-full tables.
- [ ] Prove its elementary range and tail-characterization lemmas.
- [ ] Elaborate the definitions module independently.

### Task 3: Count occupied prefixes

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_11/Section_11_4_Open_Addressing/UniformProbe/Counting.lean`

- [ ] Prove that every injective prefix assignment extends to `(m-i)!`
  permutations, or prove the equivalent one-step event-cardinality recurrence.
- [ ] Prove the satisfying-event cardinality
  `Nat.descFactorial n i * Nat.factorial (m-i)` under `i ≤ m` and
  `occupied.card = n`.
- [ ] Add small finite examples (`m ≤ 4`) as theorem-level regression tests.
- [ ] Elaborate only the counting module until it is green.

### Task 4: Identify the product probability and expectation

**Files:**
- Create: `CLRSLean/FourthEdition/Chapter_11/Section_11_4_Open_Addressing/UniformProbe/Probability.lean`
- Modify imports as needed without introducing a Section 11.4 cycle.

- [ ] Convert event cardinality divided by `m!` to the existing
  `probeTail m n i` product.
- [ ] Prove `uniformProbeTailProbability_eq_probeTail` without redefining
  `probeTail`.
- [ ] Use the finite tail-sum identity to prove the actual probe-count
  expectation equals `expectedUnsuccessfulProbes`.
- [ ] Transport the unsuccessful, insertion, and successful bounds to the
  explicit sample-space statements.
- [ ] Re-run the focused interface test.

### Task 5: Add native trust evidence and checkpoint

**Files:**
- Modify: `Tests/Trust/Chapter_11.lean`
- Modify: `CLRSLean/FourthEdition/Chapter_11.lean`
- Modify: `docs/clrs-proof-progress.csv`
- Modify: `docs/audits/2026-08-28-whole-book-proof-gap-audit.md`

- [ ] Add native axiom checks for the event probability bridge, expectation
  identity, and explicit upper bound.
- [ ] Replace the deferred permutation-provenance paragraph with the exact
  proved boundary; keep RAM/cache semantics out of scope.
- [ ] Run each focused source module, the interface test, and Chapter 11 trust
  file.
- [ ] Run `python3 scripts/check_repository.py` and `git diff --check`.
- [ ] Commit the Chapter 11 proof batch and close issue #337 only after every
  acceptance target passes.

