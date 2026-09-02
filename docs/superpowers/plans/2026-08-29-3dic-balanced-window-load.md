# 3D-IC Balanced Window Load Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that every color has floor/ceiling-balanced load in each translated affine `M x M` window and expose the result as a box-defect capacity certificate.

**Architecture:** A focused `WindowLoad.lean` module uses quotient/remainder to enumerate the window by `t < M^2`, proves that enumeration is bijective, and reduces color counting to Mathlib's exact count for one modular residue. A dedicated interface test and the existing ThreeDIC trust audit make the public and axiom surfaces explicit.

**Tech Stack:** Lean 4, Mathlib `Nat.count`, `Nat.ModEq`, `Nat.count_modEq_card`, CLRS-Lean interface and trust tests.

---

### Task 1: Freeze the public theorem surface

**Files:**
- Create: `Tests/Research_ThreeDIC_WindowLoad_Interface.lean`

- [x] **Step 1: Write the failing interface test**

```lean
import CLRSLean.Research.ThreeDIC.WindowLoad

open CLRS.Research.ThreeDIC

#check windowIndexPoint
#check windowIndexPoint_inWindow
#check windowIndexPoint_injective
#check exists_windowIndexPoint_eq
#check windowColorCount
#check affineChainColor_window_count_eq_floor_or_ceil
#check affineChainColor_window_load_le_ceilDiv
```

- [x] **Step 2: Verify RED**

Run `lake env lean Tests/Research_ThreeDIC_WindowLoad_Interface.lean`.
Expected: nonzero exit because `CLRSLean.Research.ThreeDIC.WindowLoad` does not
exist.

### Task 2: Implement canonical window counting

**Files:**
- Create: `CLRSLean/Research/ThreeDIC/WindowLoad.lean`

- [x] **Step 1: Define the canonical enumeration and count**

```lean
def windowIndexPoint (M p q t : Nat) : Nat × Nat :=
  (p + t % M, q + t / M)

def windowColorCount (M K p q c : Nat) : Nat :=
  (M * M).count (fun t =>
    affineChainColor M K (windowIndexPoint M p q t).1
      (windowIndexPoint M p q t).2 = c)
```

- [x] **Step 2: Prove the enumeration contract**

Use `Nat.mod_lt`, `Nat.div_lt_of_lt_mul`, `Nat.mod_add_div`, and coordinate
arithmetic to prove that valid indices are in the window, distinct indices map
to distinct coordinates, and each pair of offsets below `M` is reached by
`t = di + M*dj`.

- [x] **Step 3: Prove the modular color identity**

Normalize

```lean
affineChainColor M K (windowIndexPoint M p q t).1
  (windowIndexPoint M p q t).2
```

to `(p + M*q + t) % K` using `Nat.mod_add_div` and semiring
normalization.

- [x] **Step 4: Prove floor/ceiling balance**

Choose the unique residue offset `d < K` that changes the base color into
`c`. Cancel the common base using `Nat.ModEq.add_left_cancel'`, rewrite
`windowColorCount` as `Nat.count (fun t => t ≡ d [MOD K]) (M*M)`, and apply
`Nat.count_modEq_card`. Splitting the indicator yields:

```lean
windowColorCount M K p q c = (M * M) / K ∨
  windowColorCount M K p q c = (M * M) ⌈/⌉ K
```

- [x] **Step 5: Prove the direct capacity wrapper**

Expose:

```lean
windowColorCount M K p q c ≤ (M * M) ⌈/⌉ K
```

without requiring downstream users to eliminate the floor/ceiling
disjunction.

- [x] **Step 6: Verify GREEN narrowly**

Run:

```bash
lake build CLRSLean.Research.ThreeDIC.WindowLoad
lake env lean Tests/Research_ThreeDIC_WindowLoad_Interface.lean
```

Expected: both commands exit zero.

### Task 3: Trust and research-document synchronization

**Files:**
- Modify: `Tests/Research_ThreeDIC_Trust.lean`
- Modify: `docs/research/3d-ic-route-a-literature-audit-2026-08-29.md`
- Modify: `docs/research/3d-ic-hbt-final-question-stack-2026-08-29.md`

- [x] **Step 1: Add the module and upper bound to the trust audit**

Import `WindowLoad` and add:

```lean
#assert_axioms CLRS.Research.ThreeDIC.affineChainColor_window_load_le_ceilDiv
```

- [x] **Step 2: Mark the balanced-window hypothesis as proved**

Update both research documents to cite the exact Lean theorem while preserving
the literature-audit warning that this elementary balancing lemma is not a
standalone novelty claim.

- [x] **Step 3: Run focused and repository verification**

```bash
lake build CLRSLean.Research.ThreeDIC.WindowLoad
for test_file in Tests/Research_ThreeDIC_*_Interface.lean Tests/Research_ThreeDIC_Trust.lean; do
  lake env lean "$test_file"
done
rg -n "\bsorry\b|\badmit\b|\baxiom\b" \
  CLRSLean/Research/ThreeDIC Tests/Research_ThreeDIC_*_Interface.lean Tests/Research_ThreeDIC_Trust.lean
uv run python scripts/check_repository.py
git diff --check
```

Expected: Lean commands and repository checker exit zero; the placeholder scan
has no findings in the changed proof surface.
