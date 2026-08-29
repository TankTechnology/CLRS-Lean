# Balanced Affine Co-Design Certificate Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove exact translated-window balance for a coprime-coordinate affine family when `K ∣ M`, then prove that the existing direction-sensitive strip score has an exact minimizer inside that certified family.

**Architecture:** `AffineWindowLoad.lean` isolates the modular-permutation count and two-dimensional window theorem. `BalancedAffineCodesign.lean` filters the existing canonical residue domain, proves admissibility and nonemptiness, and reuses finite minimization. Dedicated interface tests freeze full theorem applications before production proofs are written.

**Tech Stack:** Lean 4, Mathlib `Nat.count`, `Nat.ModEq`, `Fin`, `Finset.product`, existing `AffineColoring` and `AffineDirectionCodesign` modules, CLRS-Lean interface/trust gates.

---

### Task 1: Freeze and prove the affine window-load interface

**Files:**
- Create: `Tests/Research_ThreeDIC_AffineWindowLoad_Interface.lean`
- Create: `CLRSLean/Research/ThreeDIC/AffineWindowLoad.lean`

- [x] **Step 1: Write the failing public-interface test**

Create the test with the intended names and exact applications:

```lean
import CLRSLean.Research.ThreeDIC.AffineWindowLoad

open CLRS.Research.ThreeDIC

#check affineWindowColorCount
#check affineGridColor_window_count_eq_of_coprime_alpha
#check affineGridColor_window_count_eq_of_coprime_beta
#check affineGridColor_window_count_eq_of_coprime_coefficient

example
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcop : Nat.Coprime K alpha) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K :=
  affineGridColor_window_count_eq_of_coprime_alpha
    M K alpha beta gamma p q c hK hKM hc hcop

example
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcop : Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K :=
  affineGridColor_window_count_eq_of_coprime_beta
    M K alpha beta gamma p q c hK hKM hc hcop

example : affineWindowColorCount 4 2 1 0 3 5 7 0 = 8 := by decide
example : affineWindowColorCount 4 2 0 1 3 5 7 1 = 8 := by decide
```

- [x] **Step 2: Run RED and confirm the missing module is the reason**

Run:

```bash
lake env lean Tests/Research_ThreeDIC_AffineWindowLoad_Interface.lean
```

Expected: nonzero exit reporting that
`CLRSLean.Research.ThreeDIC.AffineWindowLoad` does not exist.

- [x] **Step 3: Define the physical-offset count**

Create the production module importing `AffineColoring`, `Mathlib.Data.Fintype.Card`,
`Mathlib.Data.Int.CardIntervalMod`, and the required Finset big-operator module.
Define:

```lean
def affineWindowColorCount
    (M K alpha beta gamma p q c : Nat) : Nat :=
  (((Finset.range M).product (Finset.range M)).filter fun offset =>
    affineGridColor alpha beta gamma K
      (p + offset.1) (q + offset.2) = c).card
```

Document that the product elements are distinct physical offsets in the full
translated window.

- [x] **Step 4: Prove the one-dimensional exact-count kernel**

Add private helpers with these complete semantic contracts:

```lean
private theorem exists_affine_residue_preimage
    (K alpha base c : Nat) (hK : 0 < K) (hc : c < K)
    (hcop : Nat.Coprime K alpha) :
    ∃ d < K, (base + alpha * d) % K = c

private theorem affine_residue_eq_iff_modEq
    (K alpha base c d : Nat) (hK : 0 < K) (hc : c < K)
    (hcop : Nat.Coprime K alpha)
    (hd : d < K) (hcolor : (base + alpha * d) % K = c) (t : Nat) :
    (base + alpha * t) % K = c ↔ t ≡ d [MOD K]

private theorem affine_residue_count_eq_div
    (n K alpha base c : Nat) (hK : 0 < K) (hKn : K ∣ n)
    (hc : c < K) (hcop : Nat.Coprime K alpha) :
    n.count (fun t => (base + alpha * t) % K = c) = n / K
```

For the preimage theorem, define the self-map of `Fin K` induced by
`d ↦ (base + alpha*d) % K`, prove injectivity by cancelling the base and the
coprime multiplier with `Nat.ModEq.cancel_left_of_coprime`, then use
`Finite.surjective_of_injective`.  For the count theorem, rewrite the predicate
using the `ModEq` characterization and simplify `Nat.count_modEq_card` with
`n % K = 0` from `hKn`.

- [x] **Step 5: Lift the kernel row-wise and column-wise**

Add a private cardinality decomposition for a filtered product:

```lean
private theorem card_filter_product_eq_sum_right
    {alpha beta : Type*} [DecidableEq alpha] [DecidableEq beta]
    (s : Finset alpha) (t : Finset beta) (pred : alpha × beta → Prop)
    [DecidablePred pred] :
    ((s.product t).filter pred).card =
      ∑ y ∈ t, (s.filter fun x => pred (x, y)).card
```

Prove the row theorem by rewriting each row's affine expression to
`baseRow + alpha*i`, applying `affine_residue_count_eq_div`, summing the
constant `M/K` over `M` rows, and closing the target with
`Nat.mul_div_assoc M hKM`.  Prove the column theorem with the symmetric
decomposition and `beta`.  Finally expose:

```lean
theorem affineGridColor_window_count_eq_of_coprime_coefficient
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hunit : Nat.Coprime K alpha ∨ Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K
```

by cases on `hunit` and applying the corresponding truth-source theorem.

- [x] **Step 6: Verify GREEN and commit the first theorem family**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.AffineWindowLoad
lake env lean Tests/Research_ThreeDIC_AffineWindowLoad_Interface.lean
git diff --check
```

Expected: all commands exit zero. Commit only the production module and its
interface test with:

```bash
git commit -m "research: certify balanced affine window load"
```

### Task 2: Freeze and prove the balanced coefficient domain

**Files:**
- Create: `Tests/Research_ThreeDIC_BalancedAffineCodesign_Interface.lean`
- Create: `CLRSLean/Research/ThreeDIC/BalancedAffineCodesign.lean`

- [x] **Step 1: Write the failing co-design interface**

Freeze:

```lean
import CLRSLean.Research.ThreeDIC.BalancedAffineCodesign

open CLRS.Research.ThreeDIC

#check balancedAffineCoefficientCandidates
#check mem_balancedAffineCoefficientCandidates_iff
#check balancedAffineCoefficientCandidates_nonempty
#check balancedAffineCoefficient_window_count_eq
#check exists_balancedAffineCoefficients_score_minimizer
#check exists_balancedAffineCoefficients_minimizer

example
    (M K : Nat) (family : Finset StripDefectShape)
    (hK : 0 < K) (hKM : K ∣ M) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      (∀ gamma p q c, c < K ->
        affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
          (M * M) / K) ∧
      (∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family) :=
  exists_balancedAffineCoefficients_minimizer M K family hK hKM
```

- [x] **Step 2: Run RED**

Run the new interface test and confirm failure is the missing module.

- [x] **Step 3: Define and characterize the certified feasible domain**

Import `AffineWindowLoad` and `AffineDirectionCodesign`, then define:

```lean
def balancedAffineCoefficientCandidates
    (K : Nat) : Finset AffineCoefficients :=
  (canonicalAffineCoefficientCandidates K).filter fun coeff =>
    Nat.Coprime K coeff.alpha ∨ Nat.Coprime K coeff.beta
```

Expose the exact membership theorem:

```lean
theorem mem_balancedAffineCoefficientCandidates_iff
    (K : Nat) (coeff : AffineCoefficients) :
    coeff ∈ balancedAffineCoefficientCandidates K ↔
      coeff.alpha < K ∧ coeff.beta < K ∧
        (Nat.Coprime K coeff.alpha ∨ Nat.Coprime K coeff.beta)
```

Derive the canonical-domain portion by unfolding
`canonicalAffineCoefficientCandidates`, eliminating `Finset.mem_image`, and
using `AffineCoefficients.ext` on the witness pair.

- [x] **Step 4: Prove nonemptiness and candidate admissibility**

Use `canonicalAffineCoefficients K { alpha := 1, beta := 0 }` as the witness.
Its first coefficient is `1 % K`; obtain coprimality from
`Nat.coprime_mod_iff_coprime` and symmetry.  Prove:

```lean
theorem balancedAffineCoefficientCandidates_nonempty
    (K : Nat) (hK : 0 < K) :
    (balancedAffineCoefficientCandidates K).Nonempty

theorem balancedAffineCoefficient_window_count_eq
    (M K gamma p q c : Nat) (coeff : AffineCoefficients)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hcoeff : coeff ∈ balancedAffineCoefficientCandidates K) :
    affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
      (M * M) / K
```

The second theorem extracts the coprime disjunction from membership and calls
the window truth source directly.

- [x] **Step 5: Prove finite balanced minimization and the headline wrapper**

Instantiate `exists_affineCoefficients_minimizer` with the certified candidate
set and its nonemptiness theorem:

```lean
theorem exists_balancedAffineCoefficients_score_minimizer
    (K : Nat) (family : Finset StripDefectShape) (hK : 0 < K) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      ∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family
```

Then bundle score minimality with universal translated-window balance:

```lean
theorem exists_balancedAffineCoefficients_minimizer
    (M K : Nat) (family : Finset StripDefectShape)
    (hK : 0 < K) (hKM : K ∣ M) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      (∀ gamma p q c, c < K ->
        affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
          (M * M) / K) ∧
      (∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family)
```

- [x] **Step 6: Add executable boundary regressions, verify, and commit**

Add `by decide` examples for `K = 1`, inclusion of a unit-coordinate pair,
exclusion of `{alpha := 2, beta := 4}` at `K = 6`, and the zero score of an
empty defect family. Run the production build, interface test, and
`git diff --check`; then commit with:

```bash
git commit -m "research: optimize over balanced affine coefficients"
```

### Task 3: Synchronize trust and claim surfaces

**Files:**
- Modify: `Tests/Research_ThreeDIC_Trust.lean`
- Modify: `docs/research/3d-ic-balanced-affine-codesign-contract-2026-08-30.md`
- Modify: `docs/research/3d-ic-affine-codesign-contract-2026-08-29.md`
- Modify: `docs/research/3d-ic-route-a-literature-audit-2026-08-29.md`
- Modify: `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`

- [x] **Step 1: Audit the two headline theorems**

Import `BalancedAffineCodesign` in the trust test and add:

```lean
#assert_axioms CLRS.Research.ThreeDIC.affineGridColor_window_count_eq_of_coprime_coefficient
#assert_axioms CLRS.Research.ThreeDIC.exists_balancedAffineCoefficients_minimizer
```

- [x] **Step 2: Update the research contracts and claim ledgers**

Change the new contract's two target claims to supported and cite their exact
Lean theorem names.  In the earlier affine contract, replace the unsupported
blanket statement with the bounded result: balance is now proved only for
`K ∣ M` and a coprime coordinate.  Update the literature audit and final
question stack to mark the constrained balanced-family minimization as proved
while retaining all forbidden claims from the design.

- [x] **Step 3: Run focused trust and documentation gates**

Run:

```bash
lake env lean Tests/Research_ThreeDIC_AffineWindowLoad_Interface.lean
lake env lean Tests/Research_ThreeDIC_BalancedAffineCodesign_Interface.lean
lake env lean Tests/Research_ThreeDIC_Trust.lean
uv run python scripts/check_repository.py
git diff --check
```

Expected: all commands exit zero. Commit with:

```bash
git commit -m "docs(research): audit balanced affine codesign"
```

### Task 4: Run full verification and review the theorem boundary

**Files:**
- Modify: `docs/superpowers/plans/2026-08-30-3dic-balanced-affine-codesign.md`

- [x] **Step 1: Run all ThreeDIC interfaces and trust tests**

```bash
for test_file in Tests/Research_ThreeDIC_*_Interface.lean Tests/Research_ThreeDIC_Trust.lean; do
  lake env lean "$test_file"
done
```

Expected: every file exits zero.

- [x] **Step 2: Run the full repository gates**

```bash
lake build CLRSLean
uv run python scripts/check_repository.py
rg -n "\bsorry\b|\badmit\b|\baxiom\b" \
  CLRSLean/Research/ThreeDIC/AffineWindowLoad.lean \
  CLRSLean/Research/ThreeDIC/BalancedAffineCodesign.lean \
  Tests/Research_ThreeDIC_AffineWindowLoad_Interface.lean \
  Tests/Research_ThreeDIC_BalancedAffineCodesign_Interface.lean \
  Tests/Research_ThreeDIC_Trust.lean
git diff --check
```

Expected: builds and checkers exit zero; the declaration-aware scan has no
production placeholders or new axioms.

- [x] **Step 3: Perform a mathematical and claim-boundary review**

Check that the public theorem retains `0 < K`, `K ∣ M`, `c < K`, and the
coprime-coordinate hypothesis; that the count is over unique offset pairs;
that minimization is only over `balancedAffineCoefficientCandidates`; and that
no document claims full classification, tightness, repairability, or a solved
traditional EDA open problem.

- [x] **Step 4: Close the plan and commit**

Mark only genuinely completed checkboxes, rerun `git diff --check`, and commit:

```bash
git commit -m "docs(research): close balanced affine codesign plan"
```
