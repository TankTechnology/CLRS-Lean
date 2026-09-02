# Phase-Aware Strip-Defect Load Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Certify a physical finite-strip load bound for affine repair-chain colors, first by composing single-line bounds and then by exploiting the cross-line color period.

**Architecture:** A focused `StripDefectLoad` module owns the strip geometry, unique physical-point sets, the cross-line phase period, and both load theorems.  Private colored index pairs bridge physical points to quotient-pair injections; the public API exposes only EDA-facing physical sets, periods, bounds, and axis/finite-grid wrappers.

**Tech Stack:** Lean 4, Mathlib `Finset`, `Nat.ModEq`, quotient/remainder arithmetic, existing `LineDefectLoad` and `FiniteGrid` modules.

---

### Task 1: Freeze the public interface and verify RED

**Files:**
- Create: `Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean`

- [x] **Step 1: Write the failing interface test**

```lean
import CLRSLean.Research.ThreeDIC.StripDefectLoad

open CLRS.Research.ThreeDIC

#check stripPoint
#check stripLinePoints
#check stripPoints
#check stripColorPoints
#check stripAcrossColorPeriod
#check stripAcrossColorPeriod_pos
#check stripColor_load_le_sum_lines
#check stripColor_load_le_phase_periods
#check stripColor_horizontal_load_le
#check stripColor_vertical_load_le_phase
#check stripColor_finiteGrid_load_le_phase_periods

example :
    (stripColorPoints 3 8 2 5 3 (0, 0) (1, 0) (0, 1)).card = 2 := by
  decide

example :
    (stripColorPoints 2 8 4 5 0 (0, 0) (0, 1) (1, 0)).card = 3 := by
  decide

example :
    (stripColorPoints 3 8 0 5 0 (0, 0) (1, 0) (0, 1)).card = 0 := by
  decide

example :
    (stripColorPoints 3 8 3 4 0 (0, 0) (0, 0) (0, 0)).card = 1 := by
  decide
```

- [x] **Step 2: Run the narrow test and verify the expected failure**

Run:

```bash
lake env lean Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean
```

Expected: nonzero exit because
`CLRSLean.Research.ThreeDIC.StripDefectLoad` does not exist.  A syntax failure
or an unrelated import failure does not count as RED.

- [x] **Step 3: Commit the RED interface**

```bash
git add Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean
git commit -m "test(research): specify strip-defect load interface"
```

### Task 2: Define physical strips and prove the compositional bound

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/StripDefectLoad.lean`
- Test: `Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean`

- [x] **Step 1: Add physical geometry and unique-point definitions**

Create the module with these imports and definitions:

```lean
import CLRSLean.Research.ThreeDIC.FiniteGrid
import CLRSLean.Research.ThreeDIC.LineDefectLoad
import Mathlib.Algebra.Order.Floor.Div

namespace CLRS.Research.ThreeDIC

def stripPoint
    (base along across : Nat × Nat) (r t : Nat) : Nat × Nat :=
  linePoint (linePoint base across r) along t

def stripLinePoints
    (L : Nat) (base along across : Nat × Nat) (r : Nat) :
    Finset (Nat × Nat) :=
  (Finset.range L).image (stripPoint base along across r)

def stripPoints
    (W L : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).image
    (fun rt => stripPoint base along across rt.1 rt.2)

def stripColorPoints
    (M K W L c : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  (stripPoints W L base along across).filter
    (fun p => affineChainColor M K p.1 p.2 = c)

private def stripColorIndexPairs
    (M K W L c : Nat) (base along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).filter (fun rt =>
    affineChainColor M K (stripPoint base along across rt.1 rt.2).1
      (stripPoint base along across rt.1 rt.2).2 = c)
```

Prove the private bridge by `Finset.filter_image`:

```lean
private theorem stripColorPoints_eq_image_indexPairs
    (M K W L c : Nat) (base along across : Nat × Nat) :
    stripColorPoints M K W L c base along across =
      (stripColorIndexPairs M K W L c base along across).image
        (fun rt => stripPoint base along across rt.1 rt.2) := by
  simp [stripColorPoints, stripPoints, stripColorIndexPairs,
    Finset.filter_image]
```

- [x] **Step 2: Add stable quotient-range and reconstruction helpers**

Keep these private:

```lean
private theorem quotient_lt_add_pred_div
    {x n d : Nat} (hd : 0 < d) (hx : x < n) :
    x / d < (n + d - 1) / d := by
  -- Use Nat.div_lt_iff_lt_mul, ceilDiv_le_iff_le_mul, and
  -- Nat.ceilDiv_eq_add_pred_div as in LineDefectLoad.lean.

private theorem eq_of_div_eq_of_mod_eq
    {a b d : Nat} (hdiv : a / d = b / d) (hmod : a % d = b % d) :
    a = b := by
  calc
    a = a % d + d * (a / d) := (Nat.mod_add_div a d).symm
    _ = b % d + d * (b / d) := by rw [hmod, hdiv]
    _ = b := Nat.mod_add_div b d
```

- [x] **Step 3: Prove the sum-of-lines bound with a quotient-pair injection**

For `T = lineColorPeriod M K along`, map a colored sample `(r,t)` to
`(r,t/T)`.  Membership supplies `r < W` and `t < L`.  If two images agree,
their row indices agree; after rewriting `stripPoint`, invoke
`lineColor_index_congruent` on the common row base to obtain equal remainders
modulo `T`, then use `eq_of_div_eq_of_mod_eq`.

Expose exactly:

```lean
theorem stripColor_load_le_sum_lines
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      W * ((L + lineColorPeriod M K along - 1) /
        lineColorPeriod M K along) := by
  rw [stripColorPoints_eq_image_indexPairs]
  refine Finset.card_image_le.trans ?_
  -- Prove that the quotient-pair image is injective on colored pairs,
  -- bound its image by range W × range (ceil(L/T)), and rewrite card_product.
```

The final proof must use the unique physical-point bridge; proving only a
bound for `stripColorIndexPairs.card` is not sufficient.

- [x] **Step 4: Verify the source module independently**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.StripDefectLoad
```

Expected: exit zero.  The interface test may still fail on phase-aware names,
which are added in the next tasks.

- [x] **Step 5: Commit the physical model and baseline theorem**

```bash
git add CLRSLean/Research/ThreeDIC/StripDefectLoad.lean
git commit -m "research: certify compositional strip load"
```

### Task 3: Prove the cross-line phase period

**Files:**
- Modify: `CLRSLean/Research/ThreeDIC/StripDefectLoad.lean`

- [x] **Step 1: Define and prove positivity of the cross period**

Add:

```lean
def stripAcrossColorPeriod
    (M K : Nat) (along across : Nat × Nat) : Nat :=
  let g := Nat.gcd K (lineColorStep M along)
  g / Nat.gcd g (lineColorStep M across)

theorem stripAcrossColorPeriod_pos
    (M K : Nat) (along across : Nat × Nat) (hK : 0 < K) :
    0 < stripAcrossColorPeriod M K along across := by
  let g := Nat.gcd K (lineColorStep M along)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hK
  exact Nat.div_pos
    (Nat.le_of_dvd hg (Nat.gcd_dvd_left g (lineColorStep M across)))
    (Nat.gcd_pos_of_pos_left (lineColorStep M across) hg)
```

- [x] **Step 2: Normalize the affine color of a strip sample**

Prove privately:

```lean
private theorem affineChainColor_stripPoint
    (M K : Nat) (base along across : Nat × Nat) (r t : Nat) :
    affineChainColor M K (stripPoint base along across r t).1
      (stripPoint base along across r t).2 =
        (base.1 + M * base.2 + lineColorStep M across * r +
          lineColorStep M along * t) % K := by
  unfold stripPoint
  rw [affineChainColor_linePoint]
  simp only [linePoint, lineColorStep]
  congr 1
  ring
```

- [x] **Step 3: Prove cross-row residue congruence**

Keep the structural lemma private until a downstream consumer needs it:

```lean
private theorem stripColor_row_index_congruent
    (M K : Nat) (base along across : Nat × Nat) (hK : 0 < K)
    {r s t u : Nat}
    (hColor :
      affineChainColor M K (stripPoint base along across r t).1
          (stripPoint base along across r t).2 =
        affineChainColor M K (stripPoint base along across s u).1
          (stripPoint base along across s u).2) :
    r % stripAcrossColorPeriod M K along across =
      s % stripAcrossColorPeriod M K along across := by
  -- Rewrite both colors with affineChainColor_stripPoint.
  -- Let g = gcd K (lineColorStep M along).
  -- Regard equality of residues as Nat.ModEq modulo K, reduce it modulo g
  -- with ModEq.of_dvd and gcd_dvd_left, and erase both along terms using
  -- gcd_dvd_right. Cancel the common base with ModEq.add_left_cancel'.
  -- Apply ModEq.cancel_left_div_gcd to the across step and unfold R.
```

Do not replace this lemma with an assumption.  It is the mathematical bridge
that makes the phase theorem stronger than the sum-of-lines theorem.

- [x] **Step 4: Add a concrete period regression check**

Extend the interface test:

```lean
example : stripAcrossColorPeriod 2 8 (0, 1) (1, 0) = 2 := by decide
example : stripAcrossColorPeriod 3 8 (1, 0) (0, 1) = 1 := by decide
```

- [x] **Step 5: Build and commit**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.StripDefectLoad
```

Then:

```bash
git add CLRSLean/Research/ThreeDIC/StripDefectLoad.lean \
  Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean
git commit -m "research: expose strip color phase period"
```

### Task 4: Prove the phase-aware product bound and wrappers

**Files:**
- Modify: `CLRSLean/Research/ThreeDIC/StripDefectLoad.lean`
- Modify: `Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean`

- [x] **Step 1: Prove injectivity of the two-period quotient map**

For

```text
R = stripAcrossColorPeriod M K along across
T = lineColorPeriod M K along,
```

map a colored index pair `(r,t)` to `(r/R,t/T)`.  Equal images give equal
quotients.  `stripColor_row_index_congruent` gives equal row remainders, hence
`r=s`.  After substituting the row equality, `lineColor_index_congruent` gives
equal along-index remainders, hence `t=u`.

The image lies in:

```lean
(Finset.range ((W + R - 1) / R)).product
  (Finset.range ((L + T - 1) / T))
```

by `quotient_lt_add_pred_div` and positivity of both periods.

- [x] **Step 2: Expose the phase-aware theorem**

Implement the exact approved signature:

```lean
theorem stripColor_load_le_phase_periods
    (M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along) := by
  rw [stripColorPoints_eq_image_indexPairs]
  refine Finset.card_image_le.trans ?_
  -- Bound colored index pairs by the quotient-pair image and its product range.
```

- [x] **Step 3: Add the axis-aligned and finite-grid wrappers**

Implement:

```lean
theorem stripColor_horizontal_load_le
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card ≤
      W * ((L + K - 1) / K)

theorem stripColor_vertical_load_le_phase
    (M K W L c : Nat) (base : Nat × Nat) (hK : 0 < K) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card ≤
      ((W + Nat.gcd K M - 1) / Nat.gcd K M) *
        ((L + K / Nat.gcd K M - 1) / (K / Nat.gcd K M))

theorem stripColor_finiteGrid_load_le_phase_periods
    (N M K W L c : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (_hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (stripColorPoints M K W L c base along across).card ≤
      ((W + stripAcrossColorPeriod M K along across - 1) /
          stripAcrossColorPeriod M K along across) *
        ((L + lineColorPeriod M K along - 1) /
          lineColorPeriod M K along)
```

Use `simpa [stripAcrossColorPeriod, lineColorPeriod, lineColorStep]` for the
axis-aligned wrappers.  The finite-grid theorem calls the phase theorem and
retains `_hGrid` solely to expose the physical-domain contract.

- [x] **Step 4: Verify GREEN at the public interface**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.StripDefectLoad
lake env lean Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean
```

Expected: both exit zero, including all concrete `by decide` examples.

- [x] **Step 5: Commit the headline theorem**

```bash
git add CLRSLean/Research/ThreeDIC/StripDefectLoad.lean \
  Tests/Research_ThreeDIC_StripDefectLoad_Interface.lean
git commit -m "research: certify phase-aware strip load"
```

### Task 5: Trust audit, research claims, and final verification

**Files:**
- Modify: `Tests/Research_ThreeDIC_Trust.lean`
- Modify: `docs/research/3d-ic-route-a-literature-audit-2026-08-29.md`
- Modify: `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`
- Modify: `docs/superpowers/plans/2026-08-29-3dic-strip-phase-load.md`

- [x] **Step 1: Extend the trust audit**

Import `StripDefectLoad`, update the audited-theorem count, and add:

```lean
#assert_axioms CLRS.Research.ThreeDIC.stripColor_load_le_phase_periods
```

- [x] **Step 2: Synchronize research documentation**

Record both theorem levels and the exact assumptions.  State that the phase
bound can be strictly smaller when `R > 1`, but do not call it tight, optimal,
an open-problem solution, or end-to-end repairability.  Change the roadmap so
the next research gate is either a matching lower-bound/tightness result or
affine coefficient/direction co-design.

- [x] **Step 3: Run focused verification**

```bash
lake build CLRSLean.Research.ThreeDIC.StripDefectLoad
for f in Tests/Research_ThreeDIC_*Interface.lean \
  Tests/Research_ThreeDIC_Trust.lean; do
  lake env lean "$f"
done
```

Expected: every command exits zero.

- [x] **Step 4: Run trust, placeholder, and repository gates**

```bash
rg -n '\b(sorry|admit)\b|^[[:space:]]*axiom[[:space:]]' \
  CLRSLean/Research/ThreeDIC \
  Tests/Research_ThreeDIC_*Interface.lean \
  Tests/Research_ThreeDIC_Trust.lean
uv run python scripts/check_repository.py
git diff --check
```

Expected: the placeholder scan has no findings and the remaining commands exit
zero.

- [x] **Step 5: Request independent semantic review**

Ask the reviewer to check:

- physical points are deduplicated before the public load is counted;
- the cross-row period derivation is mathematically sound in degenerate and
  boundary cases;
- `K=1`, zero directions, `W=0`, and `L=0` remain correct;
- the vertical wrapper preserves the phase improvement;
- documentation does not claim tightness or repairability.

Resolve every Critical or Important issue and rerun the affected gates.

- [x] **Step 6: Close the reviewed plan and record the final state**

After the independent reviewer accepts the audit fixes and the post-review
gates pass, mark Steps 5 and 6 complete, then commit that final plan state:

```bash
git add docs/research/3d-ic-route-a-literature-audit-2026-08-29.md \
  docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md \
  docs/superpowers/plans/2026-08-29-3dic-strip-phase-load.md
git commit -m "docs(plan): close phase-aware strip certificate"
```

The branch is ready for integration only after a fresh post-commit focused
test run and `scripts/check_repository.py` both succeed.
