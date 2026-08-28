# 3D-IC Affine Connectivity and Line-Load Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove finite-grid same-color bounded-hop connectivity and the modular-period per-chain load bound for parameterized lattice-line defects.

**Execution status:** Tasks 1--5 and the focused trust gate are complete.
Draft-PR integration is the only remaining execution step.

**Architecture:** Build five small research modules. `FiniteGrid` closes geometric boundary facts, `WindowOriginPath` builds an explicit finite Manhattan path, and `AffineFiniteConnectivity` combines them with the existing affine window theorem. `LineDefect` isolates modular progression and period facts, while `LineDefectLoad` proves the finite-range cardinality bound and specializations. Each module has a separate interface test and is committed only after its focused build passes.

**Tech Stack:** Lean 4, Mathlib `Nat`, `Nat.ModEq`, `Nat.gcd`, `Finset.range`, `List.IsChain`, `omega`, `nlinarith`, Lake.

---

### Task 1: Finite-grid window geometry

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/FiniteGrid.lean`
- Create: `Tests/Research_ThreeDIC_FiniteGrid_Interface.lean`

- [x] **Step 1: Write the failing public interface**

```lean
import CLRSLean.Research.ThreeDIC.FiniteGrid

open CLRS.Research.ThreeDIC

#check inGrid
#check validWindowOrigin
#check coverOrigin
#check inWindow_of_validWindowOrigin_inGrid
#check inWindow_coverOrigin
#check gridDistSq_same_window_le
```

- [x] **Step 2: Verify red state**

Run:

```bash
lake env lean Tests/Research_ThreeDIC_FiniteGrid_Interface.lean
```

Expected: nonzero exit because `CLRSLean.Research.ThreeDIC.FiniteGrid` does not yet exist.

- [x] **Step 3: Implement the geometry interface**

Use the following public signatures in `FiniteGrid.lean`:

```lean
def inGrid (N : Nat) (x : Nat × Nat) : Prop :=
  x.1 < N ∧ x.2 < N

def validWindowOrigin (N M : Nat) (a : Nat × Nat) : Prop :=
  a.1 + M ≤ N ∧ a.2 + M ≤ N

def coverOrigin (N M i : Nat) : Nat :=
  min i (N - M)

theorem inWindow_of_validWindowOrigin_inGrid
    {N M : Nat} {a x : Nat × Nat}
    (ha : validWindowOrigin N M a) (hx : inWindow M a.1 a.2 x) :
    inGrid N x

theorem inWindow_coverOrigin
    {N M : Nat} (hM : 0 < M) (hMN : M ≤ N) {x : Nat × Nat}
    (hx : inGrid N x) :
    inWindow M (coverOrigin N M x.1) (coverOrigin N M x.2) x ∧
    validWindowOrigin N M (coverOrigin N M x.1, coverOrigin N M x.2)

theorem gridDistSq_same_window_le
    {M p q : Nat} {x y : Nat × Nat} (hM : 0 < M)
    (hx : inWindow M p q x) (hy : inWindow M p q y) :
    gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2
```

Prove the interval bounds with `omega` after unfolding `inGrid`,
`validWindowOrigin`, `coverOrigin`, `inWindow`, and `Nat.dist`. Finish the
squared-distance theorem with `nlinarith` from the two coordinate bounds
`Nat.dist _ _ ≤ M - 1`.

- [x] **Step 4: Verify green state**

```bash
lake build CLRSLean.Research.ThreeDIC.FiniteGrid
lake env lean Tests/Research_ThreeDIC_FiniteGrid_Interface.lean
```

Expected: both commands exit zero and expose all six public names.

- [x] **Step 5: Commit**

```bash
git add CLRSLean/Research/ThreeDIC/FiniteGrid.lean Tests/Research_ThreeDIC_FiniteGrid_Interface.lean
git commit -m "research: prove finite repair-window geometry"
```

### Task 2: Explicit valid window-origin paths

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/WindowOriginPath.lean`
- Create: `Tests/Research_ThreeDIC_WindowOriginPath_Interface.lean`

- [x] **Step 1: Write the failing interface**

```lean
import CLRSLean.Research.ThreeDIC.WindowOriginPath

open CLRS.Research.ThreeDIC

#check natIntervalPath
#check natIntervalPath_head?
#check natIntervalPath_getLast?
#check natIntervalPath_isChain
#check natIntervalPath_mem_between
#check windowOriginPath
#check windowOriginPath_head?
#check windowOriginPath_getLast?
#check windowOriginPath_isChain
#check windowOriginPath_mem_valid
```

- [x] **Step 2: Verify red state**

```bash
lake env lean Tests/Research_ThreeDIC_WindowOriginPath_Interface.lean
```

Expected: nonzero exit because the module is absent.

- [x] **Step 3: Implement the one-dimensional path**

Define an inclusive monotone path:

```lean
def natIntervalPath (a b : Nat) : List Nat :=
  if a ≤ b then (List.range' a (b - a + 1))
  else (List.range' b (a - b + 1)).reverse
```

Prove its optional head and last are `some a` and `some b`, consecutive
elements have natural distance one, and every member lies between `min a b`
and `max a b`. Use `List.range'`, reverse, membership, and `omega` lemmas rather
than defining a partial recursive function.

- [x] **Step 4: Implement the two-dimensional Manhattan path**

Define the path as the horizontal segment at the source second coordinate,
followed by the vertical segment at the destination first coordinate with its
first element dropped to avoid duplicating the corner:

```lean
def windowOriginPath (a b : Nat × Nat) : List (Nat × Nat) :=
  (natIntervalPath a.1 b.1).map (fun i => (i, a.2)) ++
  ((natIntervalPath a.2 b.2).drop 1).map (fun j => (b.1, j))
```

Prove exact optional endpoints, `List.IsChain windowAdjacent`, and preservation
of `validWindowOrigin N M` when both endpoints are valid. Split the append-chain
proof at the corner `(b.1,a.2)` and use the four disjuncts of `windowAdjacent`
for increasing/decreasing horizontal/vertical steps.

- [x] **Step 5: Verify green state**

```bash
lake build CLRSLean.Research.ThreeDIC.WindowOriginPath
lake env lean Tests/Research_ThreeDIC_WindowOriginPath_Interface.lean
```

Expected: both commands exit zero.

- [x] **Step 6: Commit**

```bash
git add CLRSLean/Research/ThreeDIC/WindowOriginPath.lean Tests/Research_ThreeDIC_WindowOriginPath_Interface.lean
git commit -m "research: construct finite window-origin paths"
```

### Task 3: Main finite-grid connectivity theorem

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/AffineFiniteConnectivity.lean`
- Create: `Tests/Research_ThreeDIC_AffineFiniteConnectivity_Interface.lean`

- [x] **Step 1: Write the failing interface**

```lean
import CLRSLean.Research.ThreeDIC.AffineFiniteConnectivity

open CLRS.Research.ThreeDIC

#check BoundedColorPath
#check BoundedColorPath.head?_eq
#check BoundedColorPath.getLast?_eq
#check BoundedColorPath.mem_inGrid
#check BoundedColorPath.mem_color
#check BoundedColorPath.isChain
#check affineChainColor_finiteGrid_connected
```

- [x] **Step 2: Verify red state**

```bash
lake env lean Tests/Research_ThreeDIC_AffineFiniteConnectivity_Interface.lean
```

Expected: nonzero exit because the module is absent.

- [x] **Step 3: Define the bundled path contract**

```lean
structure BoundedColorPath (N M K c : Nat) (x y : Nat × Nat) where
  points : List (Nat × Nat)
  head?_eq : points.head? = some x
  getLast?_eq : points.getLast? = some y
  mem_inGrid : ∀ z ∈ points, inGrid N z
  mem_color : ∀ z ∈ points, affineChainColor M K z.1 z.2 = c
  isChain : points.IsChain
    (fun u v => gridDistSq u v ≤ M ^ 2 + (M - 1) ^ 2)
```

The generated structure projections provide the five reader-facing wrapper
names listed by the interface.

- [x] **Step 4: Prove the main connectivity theorem**

Use this public signature:

```lean
theorem affineChainColor_finiteGrid_connected
    (N M K c : Nat) (hK : 0 < K) (hKM : K ≤ M * M) (hMN : M ≤ N)
    {x y : Nat × Nat} (hx : inGrid N x) (hy : inGrid N y)
    (hxc : affineChainColor M K x.1 x.2 = c)
    (hyc : affineChainColor M K y.1 y.2 = c) :
    Nonempty (BoundedColorPath N M K c x y)
```

Derive `0 < M` from `hK` and `hKM`. Let `ax` and `ay` be the canonical covering
window origins. Apply `windowOriginPath` and
`affineChainColor_windowPath_bounded` to obtain representatives. Build

```text
x :: representatives ++ [y]
```

and prove the bundled contract. Endpoint-to-representative hops use
`gridDistSq_same_window_le`; representative hops use the existing path theorem;
finite-grid membership follows from `windowOriginPath_mem_valid` and
`inWindow_of_validWindowOrigin_inGrid`.

- [x] **Step 5: Verify green state**

```bash
lake build CLRSLean.Research.ThreeDIC.AffineFiniteConnectivity
lake env lean Tests/Research_ThreeDIC_AffineFiniteConnectivity_Interface.lean
```

Expected: both commands exit zero and the theorem has no additional assumptions.

- [x] **Step 6: Commit**

```bash
git add CLRSLean/Research/ThreeDIC/AffineFiniteConnectivity.lean Tests/Research_ThreeDIC_AffineFiniteConnectivity_Interface.lean
git commit -m "research: close finite affine color connectivity"
```

### Task 4: Lattice-line modular progression and period

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/LineDefect.lean`
- Create: `Tests/Research_ThreeDIC_LineDefect_Interface.lean`

- [x] **Step 1: Write the failing interface**

```lean
import CLRSLean.Research.ThreeDIC.LineDefect

open CLRS.Research.ThreeDIC

#check linePoint
#check lineColorStep
#check lineColorPeriod
#check lineColorPeriod_pos
#check affineChainColor_linePoint
#check lineColor_period
#check lineColor_index_congruent
```

- [x] **Step 2: Verify red state**

```bash
lake env lean Tests/Research_ThreeDIC_LineDefect_Interface.lean
```

Expected: nonzero exit because the module is absent.

- [x] **Step 3: Implement line definitions and progression identity**

```lean
def linePoint (base step : Nat × Nat) (t : Nat) : Nat × Nat :=
  (base.1 + step.1 * t, base.2 + step.2 * t)

def lineColorStep (M : Nat) (step : Nat × Nat) : Nat :=
  step.1 + M * step.2

def lineColorPeriod (M K : Nat) (step : Nat × Nat) : Nat :=
  K / Nat.gcd K (lineColorStep M step)
```

Prove `affineChainColor_linePoint` by unfolding and normalizing the semiring
expression before applying `% K`. Prove `lineColorPeriod_pos` from `0 < K`,
`Nat.gcd_dvd_left`, and positivity of division by a positive divisor.

- [x] **Step 4: Prove exact periodicity and same-color congruence**

`lineColor_period` states that advancing the index by `lineColorPeriod` leaves
the color unchanged. `lineColor_index_congruent` states that if indices `s` and
`t` have the same color, then

```text
s % lineColorPeriod M K step = t % lineColorPeriod M K step.
```

Translate color equality to `Nat.ModEq K` for
`lineColorStep M step * s` and `lineColorStep M step * t`. Divide both the
modulus and multiplier by `gcd`, use coprimality of the quotients, cancel the
multiplier, and translate the resulting `Nat.ModEq` back to equality of
remainders modulo the period.

- [x] **Step 5: Verify green state**

```bash
lake build CLRSLean.Research.ThreeDIC.LineDefect
lake env lean Tests/Research_ThreeDIC_LineDefect_Interface.lean
```

Expected: both commands exit zero, including the zero-step case where period is one.

- [x] **Step 6: Commit**

```bash
git add CLRSLean/Research/ThreeDIC/LineDefect.lean Tests/Research_ThreeDIC_LineDefect_Interface.lean
git commit -m "research: prove affine line-color period"
```

### Task 5: Per-chain line-defect load bound

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/LineDefectLoad.lean`
- Create: `Tests/Research_ThreeDIC_LineDefectLoad_Interface.lean`

- [x] **Step 1: Write the failing interface**

```lean
import CLRSLean.Research.ThreeDIC.LineDefectLoad

open CLRS.Research.ThreeDIC

#check lineColorIndices
#check lineColor_load_le_ceilDiv_period
#check lineColor_horizontal_load_le
#check lineColor_vertical_load_le
#check lineColor_coprime_load_le
#check lineColor_finiteGrid_load_le
```

- [x] **Step 2: Verify red state**

```bash
lake env lean Tests/Research_ThreeDIC_LineDefectLoad_Interface.lean
```

Expected: nonzero exit because the module is absent.

- [x] **Step 3: Define the exact counting universe**

```lean
def lineColorIndices (M K L c : Nat) (base step : Nat × Nat) : Finset Nat :=
  (Finset.range L).filter
    (fun t => affineChainColor M K (linePoint base step t).1
      (linePoint base step t).2 = c)
```

Define the ceiling expression in theorem statements as
`(L + T - 1) / T`, carrying `0 < T` explicitly in private counting helpers.

- [x] **Step 4: Prove the generic residue-class counting lemma**

For positive `T`, prove that a subset `s` of `Finset.range L` whose elements
all have the same remainder modulo `T` satisfies

```text
s.card ≤ (L + T - 1) / T.
```

Map each `t` injectively to `t / T`. Equal quotient and equal remainder imply
equal `t` via `Nat.mod_add_div`. Bound the quotient image inside
`Finset.range ((L + T - 1) / T)` using `t < L` and division arithmetic. Apply
`Finset.card_le_card` after the injective image construction.

- [x] **Step 5: Prove the public load theorem and specializations**

Use `lineColor_index_congruent` to show that all members of
`lineColorIndices` share one remainder when the finset is nonempty; the empty
case is immediate. Derive:

```text
lineColor_load_le_ceilDiv_period
lineColor_horizontal_load_le
lineColor_vertical_load_le
lineColor_coprime_load_le
lineColor_finiteGrid_load_le
```

The finite-grid corollary accepts

```text
∀ t < L, inGrid N (linePoint base step t)
```

and retains the same cardinality bound, making the geometric domain explicit
without changing the counting set.

- [x] **Step 6: Add executable edge examples**

In the interface test, add `by decide` examples for:

```lean
example : (lineColorIndices 3 8 0 0 (0, 0) (1, 0)).card = 0 := by decide
example : (lineColorIndices 3 8 17 0 (0, 0) (1, 0)).card = 3 := by decide
example : lineColorPeriod 3 8 (0, 1) = 8 := by decide
example : lineColorPeriod 2 8 (0, 1) = 4 := by decide
```

- [x] **Step 7: Verify green state**

```bash
lake build CLRSLean.Research.ThreeDIC.LineDefectLoad
lake env lean Tests/Research_ThreeDIC_LineDefectLoad_Interface.lean
```

Expected: both commands exit zero and all four executable edge examples pass.

- [x] **Step 8: Commit**

```bash
git add CLRSLean/Research/ThreeDIC/LineDefectLoad.lean Tests/Research_ThreeDIC_LineDefectLoad_Interface.lean
git commit -m "research: bound affine line-defect chain load"
```

### Task 6: Research documentation, verification, and draft-PR handoff

**Files:**
- Modify: `docs/research/3d-ic-hbt-affine-window-coloring-2026-08-29.md`
- Modify: `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`
- Modify: `docs/superpowers/plans/2026-08-29-3dic-affine-connectivity-line-load.md`

- [x] **Step 1: Update claim boundaries**

Record the finite-grid connectivity theorem and line-load theorem as proved.
Keep simple Hamiltonian ordering, total wire length, mux/spare feasibility,
empirical yield, and publication novelty in the unproved/model-dependent list.

- [x] **Step 2: Run the full focused verification gate**

```bash
lake build \
  CLRSLean.Research.ThreeDIC.WindowDiversity \
  CLRSLean.Research.ThreeDIC.WindowRouting \
  CLRSLean.Research.ThreeDIC.AffineWindowRouting \
  CLRSLean.Research.ThreeDIC.FiniteGrid \
  CLRSLean.Research.ThreeDIC.WindowOriginPath \
  CLRSLean.Research.ThreeDIC.AffineFiniteConnectivity \
  CLRSLean.Research.ThreeDIC.LineDefect \
  CLRSLean.Research.ThreeDIC.LineDefectLoad

for test_file in Tests/Research_ThreeDIC_*_Interface.lean; do
  lake env lean "$test_file"
done

! rg -n "\\bsorry\\b|\\badmit\\b|\\baxiom\\b|native_decide" \
  CLRSLean/Research/ThreeDIC Tests/Research_ThreeDIC_*_Interface.lean

git diff --check
```

Expected: all commands exit zero. The only tolerated warning is the pre-existing
ignored `.lake/packages/verso` local-change warning.

- [x] **Step 3: Commit the documentation and checked plan**

```bash
git add docs/research/3d-ic-hbt-affine-window-coloring-2026-08-29.md \
  docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md \
  docs/superpowers/plans/2026-08-29-3dic-affine-connectivity-line-load.md
git commit -m "docs(research): record affine route A closure"
```

- [ ] **Step 4: Integrate into the existing draft PR branch**

Push the isolated implementation branch, then merge it into
`codex/research-hbt-affine-coloring` without rewriting history. Push the updated
draft-PR branch and add a PR/issue comment containing theorem names, exact
verification commands, remaining claim boundaries, and commit identifiers.
