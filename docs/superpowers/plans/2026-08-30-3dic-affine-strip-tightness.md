# 3D-IC Affine Strip Tightness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that the existing phase-aware affine-strip load certificate is attained exactly on full-period, period-aligned, non-self-overlapping strips, and expose axis-aligned fixed-color corollaries.

**Architecture:** `AffineStripTightnessCore.lean` contains modular phase-cell and exact index-count results; `AffineStripTightness.lean` contains only the injective physical-point bridge and axis-aligned wrappers.  The implementation follows a strict RED/GREEN interface loop and does not add proof material to the existing large strip modules.

**Tech Stack:** Lean 4, Mathlib `Finset` cardinality and `Nat.ModEq` arithmetic, CLRS-Lean `AffineStripDefectLoad`, interface tests, trust audit, repository verification scripts.

---

## File map

- Create `CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean` for the
  full-period predicate, fundamental phase image, and exact index count.
- Create `CLRSLean/Research/ThreeDIC/AffineStripTightness.lean` for physical
  sampling injectivity, exact physical load, and axis-aligned wrappers.
- Create `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean` for
  exact public theorem applications and concrete boundary regressions.
- Modify `Tests/Research_ThreeDIC_Trust.lean` to import the headline module and
  audit its two main theorems.
- Modify the design, research contract, literature audit, and final question
  stack only after the proof surface is green.

## Task 1: Freeze the missing public interface and observe RED

**Files:**
- Create: `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean`

- [x] **Step 1: Add the intended interface before production modules exist**

Create the test with the following declarations and exact theorem applications:

```lean
import CLRSLean.Research.ThreeDIC.AffineStripTightness

open CLRS.Research.ThreeDIC

#check affineStripFullColorPeriod
#check affineStripColorIndexPairs
#check affineStripColorIndexCount
#check affineStripPeriod_product_eq
#check affineStripFundamentalColor_image_eq_range
#check affineStripColorIndexCount_eq_of_period_dvd
#check affineStripSamplingInjective
#check affineStripColorPoints_card_eq_indexCount
#check affineStripColor_load_eq_of_period_dvd
#check affineStripColor_load_eq_phase_periods
#check affineStripColor_axisAligned_load_eq_phase_periods
#check affineStripColor_axisAlignedSwapped_load_eq_phase_periods
#check stripColor_horizontal_load_eq
#check stripColor_vertical_load_eq_phase

example
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L)
    (hInjective : affineStripSamplingInjective W L base along across) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card =
      (W / affineStripAcrossPeriod alpha beta K along across) *
        (L / affineLinePeriod alpha beta K along) :=
  affineStripColor_load_eq_of_period_dvd
    alpha beta gamma K W L c base along across
      hK hc hFull hRW hTL hInjective

example
    (M K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K) (hKL : K ∣ L) :
    (stripColorPoints M K W L c base (1, 0) (0, 1)).card =
      W * (L / K) :=
  stripColor_horizontal_load_eq M K W L c base hK hc hKL

example
    (M K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hRW : Nat.gcd K M ∣ W)
    (hTL : K / Nat.gcd K M ∣ L) :
    (stripColorPoints M K W L c base (0, 1) (1, 0)).card =
      (W / Nat.gcd K M) * (L / (K / Nat.gcd K M)) :=
  stripColor_vertical_load_eq_phase
    M K W L c base hK hc hRW hTL
```

- [x] **Step 2: Run the narrow interface and verify the expected missing-module RED**

Run:

```bash
lake env lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
```

Expected: failure because
`CLRSLean.Research.ThreeDIC.AffineStripTightness` does not exist.  A parser,
unrelated import, or environment failure is not an acceptable RED.

- [x] **Step 3: Commit the RED interface**

```bash
git add Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
git commit -m "test(research): freeze affine strip tightness interface"
```

## Task 2: Define the full-period core and prove the period product

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean`
- Test: `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean`

- [x] **Step 1: Add the core definitions**

Create the module header, explicit claim boundary, and these definitions:

```lean
import CLRSLean.Research.ThreeDIC.AffineStripDefectLoad
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.CardIntervalMod

namespace CLRS.Research.ThreeDIC

def affineStripFullColorPeriod
    (alpha beta K : Nat) (along across : Nat × Nat) : Prop :=
  Nat.gcd
      (Nat.gcd K (affineDirectionStep alpha beta along))
      (affineDirectionStep alpha beta across) = 1

def affineStripColorIndexPairs
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Finset (Nat × Nat) :=
  ((Finset.range W).product (Finset.range L)).filter fun rt =>
    affineGridColor alpha beta gamma K
      (stripPoint base along across rt.1 rt.2).1
      (stripPoint base along across rt.1 rt.2).2 = c

def affineStripColorIndexCount
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Nat :=
  (affineStripColorIndexPairs alpha beta gamma K W L c
    base along across).card
```

Use a private abbreviation `g` only inside proofs; do not add another public
period definition alongside the established `affineLinePeriod` and
`affineStripAcrossPeriod`.

- [x] **Step 2: Prove the exact period-product theorem**

Add:

```lean
theorem affineStripPeriod_product_eq
    (alpha beta K : Nat) (along across : Nat × Nat)
    (hK : 0 < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across) :
    affineStripAcrossPeriod alpha beta K along across *
        affineLinePeriod alpha beta K along = K := by
  unfold affineStripFullColorPeriod at hFull
  unfold affineStripAcrossPeriod affineLinePeriod
  let g := Nat.gcd K (affineDirectionStep alpha beta along)
  have hg : 0 < g :=
    Nat.gcd_pos_of_pos_left (affineDirectionStep alpha beta along) hK
  have hgK : g ∣ K := Nat.gcd_dvd_left K _
  change
    (g / Nat.gcd g (affineDirectionStep alpha beta across)) *
        (K / g) = K
  rw [hFull]
  simp only [Nat.div_one]
  exact Nat.mul_div_cancel' hgK
```

The pinned Mathlib theorem `Nat.mul_div_cancel' hgK` has conclusion
`g * (K / g) = K`, so no alternative period statement is permitted.

- [x] **Step 3: Build the core module and keep the interface RED focused on later declarations**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.AffineStripTightnessCore
lake env lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
```

Expected: the core build passes; the interface still fails only because the
physical headline module or later public declarations are absent.

- [x] **Step 4: Commit the full-period foundation**

```bash
git add CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean
git commit -m "research: define affine strip full periods"
```

## Task 3: Prove fundamental-cell bijectivity

**Files:**
- Modify: `CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean`
- Test: `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean`

- [x] **Step 1: Add private modular-normalization and residue-injectivity lemmas**

Add a private color normal form:

```lean
private theorem affineGridColor_stripPoint_tightness
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (r t : Nat) :
    affineGridColor alpha beta gamma K
        (stripPoint base along across r t).1
        (stripPoint base along across r t).2 =
      (alpha * base.1 + beta * base.2 + gamma +
        affineDirectionStep alpha beta across * r +
        affineDirectionStep alpha beta along * t) % K := by
  unfold affineGridColor stripPoint linePoint affineDirectionStep
  congr 1
  ring
```

Add a private lemma mirroring the established upper-bound congruence proof:
if two index pairs have equal color, their row indices agree modulo `R`; after
the row indices are equal, their along indices agree modulo `T`.  Its proof
must use `Nat.ModEq.of_dvd`, `cancel_left_div_gcd`, and the public
`affineGridColor_line_index_congruent`; it must not use bounded enumeration.

- [x] **Step 2: Define the fundamental phase cell and prove color injectivity**

Add:

```lean
def affineStripFundamentalIndexPairs
    (alpha beta K : Nat) (along across : Nat × Nat) :
    Finset (Nat × Nat) :=
  (Finset.range (affineStripAcrossPeriod alpha beta K along across)).product
    (Finset.range (affineLinePeriod alpha beta K along))

private theorem affineStripFundamentalColor_injOn
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K) :
    Set.InjOn
      (fun rt : Nat × Nat =>
        affineGridColor alpha beta gamma K
          (stripPoint base along across rt.1 rt.2).1
          (stripPoint base along across rt.1 rt.2).2)
      (affineStripFundamentalIndexPairs alpha beta K
        along across) := by
  intro x hx y hy hColor
  obtain ⟨hxR, hxT⟩ := Finset.mem_product.mp hx
  obtain ⟨hyR, hyT⟩ := Finset.mem_product.mp hy
  have hRowMod := affineStripTightness_row_index_congruent
    alpha beta gamma K base along across hK hColor
  have hRow : x.1 = y.1 :=
    Nat.ModEq.eq_of_lt_of_lt hRowMod
      (Finset.mem_range.mp hxR) (Finset.mem_range.mp hyR)
  have hAlongMod := affineGridColor_line_index_congruent
    alpha beta gamma K (linePoint base across x.1) along hK
      (by simpa [stripPoint, hRow] using hColor)
  have hAlong : x.2 = y.2 :=
    Nat.ModEq.eq_of_lt_of_lt hAlongMod
      (Finset.mem_range.mp hxT) (Finset.mem_range.mp hyT)
  exact Prod.ext hRow hAlong
```

Use the pinned method form `hRowMod.eq_of_lt_of_lt` and
`hAlongMod.eq_of_lt_of_lt` with the two `Finset.mem_range` bounds.

- [x] **Step 3: Prove the fundamental-cell image is exactly `range K`**

Add the public theorem:

```lean
theorem affineStripFundamentalColor_image_eq_range
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across) :
    (affineStripFundamentalIndexPairs alpha beta K along across).image
        (fun rt => affineGridColor alpha beta gamma K
          (stripPoint base along across rt.1 rt.2).1
          (stripPoint base along across rt.1 rt.2).2) =
      Finset.range K := by
  apply Finset.eq_of_subset_of_card_le
  · intro color hcolor
    obtain ⟨rt, _hrt, rfl⟩ := Finset.mem_image.mp hcolor
    exact Finset.mem_range.mpr (Nat.mod_lt _ hK)
  · rw [Finset.card_range]
    rw [Finset.card_image_iff.mpr
      (affineStripFundamentalColor_injOn
        alpha beta gamma K base along across hK)]
    rw [Finset.product_eq_sprod, Finset.card_product]
    simp only [Finset.card_range]
    exact (affineStripPeriod_product_eq
      alpha beta K along across hK hFull).ge
```

Check the orientation of `Finset.eq_of_subset_of_card_le`; if it expects the
reverse card inequality, use `.le` instead of `.ge` while preserving equality.

- [x] **Step 4: Add an exact interface application for the fundamental image and run GREEN**

Append to the interface test:

```lean
example
    (alpha beta gamma K : Nat) (base along across : Nat × Nat)
    (hK : 0 < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across) :
    (affineStripFundamentalIndexPairs alpha beta K along across).image
        (fun rt => affineGridColor alpha beta gamma K
          (stripPoint base along across rt.1 rt.2).1
          (stripPoint base along across rt.1 rt.2).2) =
      Finset.range K :=
  affineStripFundamentalColor_image_eq_range
    alpha beta gamma K base along across hK hFull
```

`affineStripFundamentalIndexPairs` remains public because this exact interface
application is part of the audited theorem surface.

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.AffineStripTightnessCore
```

Expected: success.

- [x] **Step 5: Commit the fundamental-cell bijection**

```bash
git add CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
git commit -m "research: certify affine strip phase cells"
```

## Task 4: Count exactly one color sample per quotient block

**Files:**
- Modify: `CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean`
- Test: `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean`

- [x] **Step 1: Add quotient-block reconstruction helpers**

Add private lemmas with these exact logical jobs:

```lean
private theorem index_eq_mul_div_add_mod
    (x d : Nat) : x = d * (x / d) + x % d := by
  omega

private theorem mul_add_lt_of_lt_div
    {block rem n d : Nat} (hd : 0 < d) (hdn : d ∣ n)
    (hblock : block < n / d) (hrem : rem < d) :
    d * block + rem < n := by
  obtain ⟨q, rfl⟩ := hdn
  have hblock' : block < q := by
    simpa [Nat.mul_div_left _ hd] using hblock
  nlinarith
```

Do not introduce stronger positivity assumptions on `W` or `L`.

- [x] **Step 2: Prove the quotient-block map is injective on one color**

For

```lean
fun rt =>
  (rt.1 / affineStripAcrossPeriod alpha beta K along across,
   rt.2 / affineLinePeriod alpha beta K along)
```

prove `Set.InjOn` over `affineStripColorIndexPairs`.  Reuse the row and along
congruence lemmas from Task 3 and reconstruct each coordinate from equal
quotient and equal remainder using `Nat.mod_add_div`.

- [x] **Step 3: Prove every quotient block has one color witness**

Given

```lean
block ∈
  (Finset.range (W / affineStripAcrossPeriod alpha beta K along across)).product
    (Finset.range (L / affineLinePeriod alpha beta K along))
```

instantiate `affineStripFundamentalColor_image_eq_range` at the shifted base

```lean
stripPoint base along across
  (affineStripAcrossPeriod alpha beta K along across * block.1)
  (affineLinePeriod alpha beta K along * block.2)
```

and color `c`.  Extract an inner pair `(r0,t0)`, construct

```lean
(R * block.1 + r0, T * block.2 + t0),
```

prove that it lies in the original `W x L` index rectangle, prove its color is
`c` by expanding `stripPoint`, and prove its quotient-block image is `block`
using `Nat.add_mul_div_left`/`Nat.add_mul_mod_self_left` after normalizing
addition order.

- [x] **Step 4: Prove the exact index-count theorem**

Add:

```lean
theorem affineStripColorIndexCount_eq_of_period_dvd
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hFull : affineStripFullColorPeriod alpha beta K along across)
    (hRW : affineStripAcrossPeriod alpha beta K along across ∣ W)
    (hTL : affineLinePeriod alpha beta K along ∣ L) :
    affineStripColorIndexCount alpha beta gamma K W L c
        base along across =
      (W / affineStripAcrossPeriod alpha beta K along across) *
        (L / affineLinePeriod alpha beta K along) := by
  unfold affineStripColorIndexCount
  let blockMap : Nat × Nat → Nat × Nat := fun rt =>
    (rt.1 / affineStripAcrossPeriod alpha beta K along across,
     rt.2 / affineLinePeriod alpha beta K along)
  have hImage :
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image blockMap =
      (Finset.range
        (W / affineStripAcrossPeriod alpha beta K along across)).product
        (Finset.range (L / affineLinePeriod alpha beta K along)) := by
    apply Finset.Subset.antisymm
    · exact affineStripColorBlock_image_subset
      alpha beta gamma K W L c base along across hK
    · exact affineStripColorBlock_surjective
      alpha beta gamma K W L c base along across
        hK hc hFull hRW hTL
  rw [← Finset.card_image_iff.mpr
    (affineStripColorBlock_injOn
      alpha beta gamma K W L c base along across hK)]
  rw [hImage, Finset.product_eq_sprod, Finset.card_product]
  simp
```

The three named block lemmas in this proof are private declarations created by
Steps 2 and 3.  Keep the public surface limited to the exact count theorem.

- [x] **Step 5: Build the core and run its exact interface application**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.AffineStripTightnessCore
```

Expected: success without `sorry`, `admit`, or a new `axiom`.

- [x] **Step 6: Commit the exact index count**

```bash
git add CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
git commit -m "research: count aligned affine strip phases exactly"
```

## Task 5: Lift exact index count to distinct physical points

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/AffineStripTightness.lean`
- Modify: `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean`

- [x] **Step 1: Define the explicit sampling-injectivity predicate**

Create the module and add:

```lean
import CLRSLean.Research.ThreeDIC.AffineStripTightnessCore

namespace CLRS.Research.ThreeDIC

def affineStripSamplingInjective
    (W L : Nat) (base along across : Nat × Nat) : Prop :=
  Set.InjOn
    (fun rt : Nat × Nat => stripPoint base along across rt.1 rt.2)
    ((Finset.range W).product (Finset.range L))
```

- [x] **Step 2: Prove the image representation and cardinality bridge**

Add:

```lean
private theorem affineStripColorPoints_eq_tightness_image
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) :
    affineStripColorPoints alpha beta gamma K W L c base along across =
      (affineStripColorIndexPairs alpha beta gamma K W L c
        base along across).image
          (fun rt => stripPoint base along across rt.1 rt.2) := by
  unfold affineStripColorPoints stripPoints affineStripColorIndexPairs
  rw [Finset.filter_image]

theorem affineStripColorPoints_card_eq_indexCount
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat)
    (hInjective : affineStripSamplingInjective W L base along across) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card =
      affineStripColorIndexCount alpha beta gamma K W L c
        base along across := by
  rw [affineStripColorPoints_eq_tightness_image]
  unfold affineStripColorIndexCount
  apply Finset.card_image_iff.mpr
  intro x hx y hy hxy
  apply hInjective
  · exact (Finset.mem_filter.mp hx).1
  · exact (Finset.mem_filter.mp hy).1
  · exact hxy
```

- [x] **Step 3: Prove exact quotient and matching-ceiling headlines**

Add `affineStripColor_load_eq_of_period_dvd` with the signature frozen in the
interface and prove it by rewriting the physical/index bridge followed by
`affineStripColorIndexCount_eq_of_period_dvd`.

Add `affineStripColor_load_eq_phase_periods` with the same hypotheses and the
existing upper-bound expression as its right-hand side.  Derive it from the
quotient theorem plus `Nat.ceilDiv_eq_add_pred_div` and the standard fact that
`d ∣ n` and `0 < d` imply `n ⌈/⌉ d = n/d`; use the established positivity
theorems for `R` and `T`.

- [x] **Step 4: Run the focused module and interface GREEN**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.AffineStripTightness
lake env lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
```

Expected: both commands succeed.

- [x] **Step 5: Commit the physical equality**

```bash
git add CLRSLean/Research/ThreeDIC/AffineStripTightness.lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
git commit -m "research: certify exact physical affine strip load"
```

## Task 6: Add axis-aligned and fixed-color tightness wrappers

**Files:**
- Modify: `CLRSLean/Research/ThreeDIC/AffineStripTightness.lean`
- Modify: `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean`

- [x] **Step 1: Prove both axis-aligned sampling maps are injective**

Add public wrappers:

```lean
theorem affineStripSamplingInjective_axisAligned
    (W L : Nat) (base : Nat × Nat) :
    affineStripSamplingInjective W L base (1, 0) (0, 1) := by
  intro x _hx y _hy hxy
  apply Prod.ext
  · have h := congrArg Prod.snd hxy
    simpa [stripPoint, linePoint] using Nat.add_left_cancel h
  · have h := congrArg Prod.fst hxy
    simpa [stripPoint, linePoint] using Nat.add_left_cancel h

theorem affineStripSamplingInjective_axisAlignedSwapped
    (W L : Nat) (base : Nat × Nat) :
    affineStripSamplingInjective W L base (0, 1) (1, 0) := by
  intro x _hx y _hy hxy
  apply Prod.ext
  · have h := congrArg Prod.fst hxy
    simpa [stripPoint, linePoint] using Nat.add_left_cancel h
  · have h := congrArg Prod.snd hxy
    simpa [stripPoint, linePoint] using Nat.add_left_cancel h
```

The unswapped proof recovers row indices from physical second coordinates and
along indices from physical first coordinates.  The swapped proof recovers
them from physical first and second coordinates respectively.

- [x] **Step 2: Derive full-period conditions from a coprime coefficient**

Add a private lemma for

```lean
Nat.Coprime K alpha ∨ Nat.Coprime K beta
```

implying `affineStripFullColorPeriod alpha beta K (1,0) (0,1)`, and the swapped
orientation.  In the alpha case, simplify `gcd(K,alpha)=1`; in the beta case,
use `Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left K alpha) hBeta` to show that
`gcd(K,alpha)` is coprime to `beta`, then unfold `Nat.Coprime`.  Do not use a
prime-factor argument.

- [x] **Step 3: Add general affine axis-aligned wrappers**

Add:

```lean
theorem affineStripColor_axisAligned_load_eq_phase_periods
    (alpha beta gamma K W L c : Nat) (base : Nat × Nat)
    (hK : 0 < K) (hc : c < K)
    (hUnit : Nat.Coprime K alpha ∨ Nat.Coprime K beta)
    (hRW : affineStripAcrossPeriod alpha beta K (1, 0) (0, 1) ∣ W)
    (hTL : affineLinePeriod alpha beta K (1, 0) ∣ L) :
    (affineStripColorPoints alpha beta gamma K W L c
      base (1, 0) (0, 1)).card =
      (W / affineStripAcrossPeriod alpha beta K (1, 0) (0, 1)) *
        (L / affineLinePeriod alpha beta K (1, 0)) :=
  affineStripColor_load_eq_of_period_dvd
    alpha beta gamma K W L c base (1, 0) (0, 1)
      hK hc (affineStripFullColorPeriod_axisAligned hUnit)
      hRW hTL (affineStripSamplingInjective_axisAligned W L base)
```

Add the swapped wrapper analogously.

- [x] **Step 4: Add fixed-color horizontal and vertical exact-load wrappers**

Add the two statements frozen by Task 1.  Horizontal simplification uses

```text
alpha = 1, beta = M, along = (1,0), across = (0,1), R = 1, T = K.
```

Vertical simplification uses

```text
alpha = 1, beta = M, along = (0,1), across = (1,0),
R = gcd(K,M), T = K/gcd(K,M).
```

Use `affineStripColorPoints_fixed_eq_stripColorPoints` and `simpa` with
`affineDirectionStep`, `affineLinePeriod`, and `affineStripAcrossPeriod`; do
not restate a second counting proof.

- [x] **Step 5: Add concrete boundary and necessity regressions**

Append:

```lean
example :
    (stripColorPoints 3 1 4 5 0
      (0, 0) (1, 0) (0, 1)).card = 20 := by decide

example :
    (stripColorPoints 3 8 0 16 0
      (0, 0) (1, 0) (0, 1)).card = 0 := by decide

example :
    (stripColorPoints 2 8 4 0 0
      (0, 0) (0, 1) (1, 0)).card = 0 := by decide

example :
    (stripColorPoints 2 8 4 4 0
      (0, 0) (0, 1) (1, 0)).card = 2 := by decide

example :
    (affineStripColorIndexCount 1 0 0 2 2 2 1
      (0, 0) (1, 0) (1, 0)) = 2 := by decide

example :
    (affineStripColorPoints 1 0 0 2 2 2 1
      (0, 0) (1, 0) (1, 0)).card = 1 := by decide
```

The last pair is the frozen counterexample showing that index tightness does
not imply physical tightness when along and across coincide.

- [x] **Step 6: Run all new interface tests and commit wrappers**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.AffineStripTightness
lake env lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
```

Expected: success.

Commit:

```bash
git add CLRSLean/Research/ThreeDIC/AffineStripTightness.lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
git commit -m "research: specialize affine strip tightness"
```

## Task 7: Audit trust, claims, and repository integration

**Files:**
- Modify: `Tests/Research_ThreeDIC_Trust.lean`
- Modify: `docs/research/3d-ic-affine-strip-tightness-contract-2026-08-30.md`
- Modify: `docs/research/3d-ic-route-a-literature-audit-2026-08-29.md`
- Modify: `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`
- Modify: `docs/superpowers/specs/2026-08-30-3dic-affine-strip-tightness-design.md`
- Modify: `docs/superpowers/plans/2026-08-30-3dic-affine-strip-tightness.md`

- [x] **Step 1: Freeze the trust surface**

Import `CLRSLean.Research.ThreeDIC.AffineStripTightness` and append:

```lean
#assert_axioms CLRS.Research.ThreeDIC.affineStripFundamentalColor_image_eq_range
#assert_axioms CLRS.Research.ThreeDIC.affineStripColor_load_eq_phase_periods
```

- [x] **Step 2: Update the research contract from pending to supported**

Change only claims that the completed Lean surface proves.  Record exact
hypotheses `0 < K`, `c < K`, full color generation, both period divisibilities,
and physical sampling injectivity.  Retain `fail` for measured DART
repairability and retain routing/spare/mux exclusions.

- [x] **Step 3: Update the prior-art audit and final question stack**

Replace “no matching lower-bound/tightness result” with the bounded claim:

```text
The phase-aware certificate is attained exactly on full-color-period,
period-aligned, non-self-overlapping strips.  Tightness for partial periods,
self-overlapping geometries, and the end-to-end repair model remains open.
```

Do not claim a recognized open problem has been solved.  Keep DART evaluation,
physical routing, spare placement, mux reachability, delay, and congestion in
the uncertified list.

- [x] **Step 4: Mark the design implemented and close completed plan boxes**

Set the spec status to `implemented and verified` only after all Lean and trust
commands pass.  Check plan boxes as each command and commit actually completes;
do not pre-check the independent-review or final-clean-tree steps.

- [x] **Step 5: Run focused production, interface, and trust gates**

```bash
lake build CLRSLean.Research.ThreeDIC.AffineStripTightnessCore
lake build CLRSLean.Research.ThreeDIC.AffineStripTightness
lake env lean Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean
lake env lean Tests/Research_ThreeDIC_Trust.lean
```

Expected: all commands exit zero.

- [x] **Step 6: Run the complete verification gates**

```bash
lake build CLRSLean
uv run python scripts/check_repository.py
rg -n "\bsorry\b|\badmit\b|^\s*axiom\b" \
  CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean \
  CLRSLean/Research/ThreeDIC/AffineStripTightness.lean \
  Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean \
  Tests/Research_ThreeDIC_Trust.lean
git diff --check
```

Expected: builds and repository checker pass; placeholder scan has no matches;
diff check exits zero.

- [x] **Step 7: Commit the audit package**

```bash
git add Tests/Research_ThreeDIC_Trust.lean \
  docs/research/3d-ic-affine-strip-tightness-contract-2026-08-30.md \
  docs/research/3d-ic-route-a-literature-audit-2026-08-29.md \
  docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md \
  docs/superpowers/specs/2026-08-30-3dic-affine-strip-tightness-design.md \
  docs/superpowers/plans/2026-08-30-3dic-affine-strip-tightness.md
git commit -m "docs(research): audit affine strip tightness"
```

- [ ] **Step 8: Request independent mathematical and claim-boundary review**

Review must check:

- the full-period condition really implies `R*T=K`;
- the block-surjectivity proof covers every valid color and every quotient
  block;
- physical cardinality equality uses the no-overlap hypothesis rather than
  silently counting duplicate indices;
- zero dimensions and `K=1` are valid;
- wrappers have the documented directions and divisibility hypotheses;
- docs do not generalize aligned tightness to arbitrary strips or DART repair.

- [ ] **Step 9: Address review findings and rerun affected gates**

Every Critical or Important finding must be fixed and rechecked.  Minor
interface findings should be fixed when they can be addressed without
expanding the theorem claim.  Commit review-driven fixes separately with a
message naming the corrected boundary.

- [ ] **Step 10: Close the plan and verify a clean worktree**

After independent review is clear, check the final boxes, commit the plan-only
closure if needed, then run:

```bash
git diff --check HEAD^ HEAD
git status --short --branch
```

Expected: diff check exits zero and the feature worktree is clean.
