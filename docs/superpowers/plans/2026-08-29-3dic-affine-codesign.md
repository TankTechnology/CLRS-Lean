# Affine Coefficient/Direction Co-Design Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize the verified line and strip load certificates to arbitrary affine coefficients and expose an exact worst-case coefficient selector over finite defect and candidate families.

**Architecture:** Four small Lean modules separate modular coloring algebra, line counting, strip phase counting, and EDA-facing family co-design. Existing fixed-color modules remain unchanged and are connected by specialization theorems; public interfaces are frozen with RED/GREEN tests before production proofs.

**Tech Stack:** Lean 4, Mathlib `Nat.ModEq`, `Finset`, quotient/remainder arithmetic, existing ThreeDIC line/strip geometry and trust audit.

---

### Task 1: Freeze the generalized coloring interface

**Files:**
- Create: `Tests/Research_ThreeDIC_AffineColoring_Interface.lean`
- Create: `CLRSLean/Research/ThreeDIC/AffineColoring.lean`

- [x] **Step 1: Write the failing interface test**

Freeze these names and exact applications:

```lean
#check affineGridColor
#check affineDirectionStep
#check affineLinePeriod
#check affineLinePeriod_pos
#check affineGridColor_linePoint
#check affineGridColor_line_periodic
#check affineGridColor_line_index_congruent
#check affineGridColor_fixed_eq_affineChainColor
#check affineDirectionStep_fixed_eq_lineColorStep
#check affineLinePeriod_fixed_eq_lineColorPeriod
```

Include concrete evaluations for `(alpha,beta,gamma,K) = (1,3,0,8)` and a
nontrivial `(2,1,4,7)` case.

- [x] **Step 2: Run RED**

Run `lake env lean Tests/Research_ThreeDIC_AffineColoring_Interface.lean` and
confirm failure is the missing module/name, not syntax.

- [x] **Step 3: Implement the algebraic module**

Define:

```lean
def affineGridColor (alpha beta gamma K i j : Nat) : Nat :=
  (alpha * i + beta * j + gamma) % K

def affineDirectionStep
    (alpha beta : Nat) (step : Nat × Nat) : Nat :=
  alpha * step.1 + beta * step.2

def affineLinePeriod
    (alpha beta K : Nat) (step : Nat × Nat) : Nat :=
  K / Nat.gcd K (affineDirectionStep alpha beta step)
```

Prove positivity under `0 < K`, the line-point normal form, periodicity, equal
color index congruence modulo the exact period, and all three fixed-color
specializations.

- [x] **Step 4: Verify GREEN and commit**

Run the module build and interface test, then commit with
`research: generalize affine grid coloring`.

### Task 2: Lift the finite-line load theorem

**Files:**
- Create: `Tests/Research_ThreeDIC_AffineLineDefectLoad_Interface.lean`
- Create: `CLRSLean/Research/ThreeDIC/AffineLineDefectLoad.lean`

- [x] **Step 1: Write and run a failing interface**

Freeze:

```lean
def affineLineColorIndices
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat) : Finset Nat

theorem affineLineColor_load_le_ceilDiv_period
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + affineLinePeriod alpha beta K step - 1) /
        affineLinePeriod alpha beta K step

theorem affineLineColor_coprime_load_le
    (alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K)
    (hCoprime : Nat.Coprime K (affineDirectionStep alpha beta step)) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + K - 1) / K

theorem affineLineColor_finiteGrid_load_le
    (N alpha beta gamma K L c : Nat) (base step : Nat × Nat)
    (hK : 0 < K)
    (_hGrid : ∀ t < L, inGrid N (linePoint base step t)) :
    (affineLineColorIndices alpha beta gamma K L c base step).card ≤
      (L + affineLinePeriod alpha beta K step - 1) /
        affineLinePeriod alpha beta K step
```

Verify RED before creating production code.

- [x] **Step 2: Prove the quotient injection bound**

Reuse the existing proof shape: colored indices have one residue modulo the
positive line period, quotient by that period is injective, and the quotient
image lies below `ceil(L/T)`.

- [x] **Step 3: Add specialization and boundary regressions**

Test empty prefixes, invalid colors, zero direction, and equality with the old
fixed-color index set at `(1,M,0)`.

- [x] **Step 4: Verify and commit**

Run focused build/interface checks and commit with
`research: certify generalized affine line load`.

### Task 3: Lift the phase-aware physical-strip theorem

**Files:**
- Create: `Tests/Research_ThreeDIC_AffineStripDefectLoad_Interface.lean`
- Create: `CLRSLean/Research/ThreeDIC/AffineStripDefectLoad.lean`

- [ ] **Step 1: Write and run a failing interface**

Freeze:

```lean
def affineStripColorPoints
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) : Finset (Nat × Nat)

def affineStripAcrossPeriod
    (alpha beta K : Nat) (along across : Nat × Nat) : Nat

theorem affineStripAcrossPeriod_pos
    (alpha beta K : Nat) (along across : Nat × Nat) (hK : 0 < K) :
    0 < affineStripAcrossPeriod alpha beta K along across

theorem affineStripColor_load_le_phase_periods
    (alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) (hK : 0 < K) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card ≤
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along)

theorem affineStripColor_finiteGrid_load_le_phase_periods
    (N alpha beta gamma K W L c : Nat)
    (base along across : Nat × Nat) (hK : 0 < K)
    (_hGrid : ∀ r < W, ∀ t < L,
      inGrid N (stripPoint base along across r t)) :
    (affineStripColorPoints alpha beta gamma K W L c
      base along across).card ≤
      ((W + affineStripAcrossPeriod alpha beta K along across - 1) /
          affineStripAcrossPeriod alpha beta K along across) *
        ((L + affineLinePeriod alpha beta K along - 1) /
          affineLinePeriod alpha beta K along)
```

The headline bound is exactly `ceil(W/R) * ceil(L/T)` with generalized
periods. Verify RED.

- [ ] **Step 2: Prove cross-row congruence**

Normalize a strip sample to
`basePhase + acrossStep*r + alongStep*t mod K`, reduce equality modulo
`gcd(K,alongStep)`, erase the along terms, and cancel the across step.

- [ ] **Step 3: Prove the two-period quotient injection**

Map colored index pairs to `(r/R,t/T)`, reconstruct row and along indices from
equal quotients and residues, bound the image by the product of two ceiling
ranges, and transfer to the deduplicated physical-point image.

- [ ] **Step 4: Add fixed specialization and geometry regressions**

Check horizontal, vertical, zero width/length, repeated physical points, and
equality with existing `stripColorPoints` at `(1,M,0)`.

- [ ] **Step 5: Verify and commit**

Run focused checks and commit with
`research: certify generalized affine strip load`.

### Task 4: Add the finite-family co-design layer

**Files:**
- Create: `Tests/Research_ThreeDIC_AffineDirectionCodesign_Interface.lean`
- Create: `CLRSLean/Research/ThreeDIC/AffineDirectionCodesign.lean`

- [ ] **Step 1: Write and run a failing interface**

Freeze:

```lean
structure AffineCoefficients where
  alpha : Nat
  beta : Nat

structure StripDefectShape where
  width : Nat
  length : Nat
  along : Nat × Nat
  across : Nat × Nat

def affineStripLoadCertificate
    (K : Nat) (coeff : AffineCoefficients) (shape : StripDefectShape) : Nat

def affineDefectFamilyScore
    (K : Nat) (coeff : AffineCoefficients)
    (family : Finset StripDefectShape) : Nat

theorem affineStripColor_load_le_certificate
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (base : Nat × Nat) (hK : 0 < K) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineStripLoadCertificate K coeff shape

theorem affineStripColor_load_le_familyScore
    (K gamma c : Nat) (coeff : AffineCoefficients)
    (shape : StripDefectShape) (family : Finset StripDefectShape)
    (base : Nat × Nat) (hK : 0 < K) (hshape : shape ∈ family) :
    (affineStripColorPoints coeff.alpha coeff.beta gamma K
      shape.width shape.length c base shape.along shape.across).card ≤
        affineDefectFamilyScore K coeff family

theorem exists_affineCoefficients_minimizer
    (K : Nat) (family : Finset StripDefectShape)
    (candidates : Finset AffineCoefficients) (hne : candidates.Nonempty) :
    ∃ coeff ∈ candidates, ∀ other ∈ candidates,
      affineDefectFamilyScore K coeff family ≤
        affineDefectFamilyScore K other family
```

Verify the missing module/name RED failure.

- [ ] **Step 2: Implement certificate and family score**

Define the shape certificate with the generalized `R` and `T`, and define the
family score as `family.sup (affineStripLoadCertificate K coeff)`.

- [ ] **Step 3: Prove actual-load bridges**

Instantiate the generalized strip theorem for one shape, then compose with
`Finset.le_sup hshape` for a family member.

- [ ] **Step 4: Prove exact candidate-relative minimization**

Use `candidates.exists_min_image` on the family score to prove:

```lean
∃ coeff ∈ candidates, ∀ other ∈ candidates,
  affineDefectFamilyScore K coeff family ≤
    affineDefectFamilyScore K other family
```

- [ ] **Step 5: Add executable examples and commit**

Include an empty family score, a singleton shape, two coefficients with
different directional scores, and one concrete nonempty candidate-set
minimizer. Verify and commit with
`research: certify finite affine direction codesign`.

### Task 5: Audit documentation and trust surface

**Files:**
- Modify: `Tests/Research_ThreeDIC_Trust.lean`
- Modify: `docs/research/3d-ic-route-a-literature-audit-2026-08-29.md`
- Modify: `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`
- Modify: `docs/research/3d-ic-affine-codesign-contract-2026-08-29.md`

- [ ] **Step 1: Add trust assertions**

Audit `affineStripColor_load_le_phase_periods` and
`exists_affineCoefficients_minimizer` with `#assert_axioms`.

- [ ] **Step 2: Update claim ledgers**

Record the generalized coefficient-sensitive certificate and finite-family
minimizer as verified infrastructure. Retain explicit statements that window
balance preservation, matching lower bounds, routing, and repairability are
unproved.

- [ ] **Step 3: Run focused audit and commit**

Run all ThreeDIC interface/trust tests and a declaration-aware placeholder
scan. Commit with `docs(research): audit affine direction codesign`.

### Task 6: Final verification and integration review

**Files:**
- Modify: `docs/superpowers/plans/2026-08-29-3dic-affine-codesign.md`

- [ ] **Step 1: Run fresh full verification**

Run:

```bash
lake build CLRSLean
for f in Tests/Research_ThreeDIC_*Interface.lean \
         Tests/Research_ThreeDIC_Trust.lean; do
  lake env lean "$f"
done
uv run python scripts/check_repository.py
git diff --check
```

Scan changed production/test files for `sorry`, `admit`, and declaration-level
`axiom`.

- [ ] **Step 2: Review design and claims line by line**

Check every public name against the design, ensure actual-load theorems count
unique physical points, and ensure documentation never upgrades the finite
candidate minimizer into global/window-balanced optimality.

- [ ] **Step 3: Close the plan and commit**

Mark all genuinely completed steps, rerun `git diff --check`, and commit with
`docs(research): close affine codesign plan`.
