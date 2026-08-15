# Ch34 Affine Exactly-One Kernel Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a reusable contextual machine theorem that serializes an
exactly-one constraint at arbitrary runtime gate and source-wire bases.

**Architecture:** Keep pure gate arithmetic in `AffineTrace.lean` and concrete
builder execution in `AffineRun.lean`.  Reuse the already verified
`sequentialExactlyOneRevProgram`; expose only the counter-preserving support
lemmas needed by the affine proof.  The public run starts at the body entry
configuration, prepends the reverse affine trace to an arbitrary output suffix,
halts with all counters cleared, and carries a quadratic bound in the combined
unary state size.

**Tech Stack:** Lean 4, Mathlib `StateTransition.EvalsToInTime`, the Chapter 34
`PolyBuilder` compiler, `Polynomial Nat`, focused direct Lean tests.

---

### Task 1: Lock the affine interface

**Files:**

- Create: `Tests/Chapter_34_CookLevin_AffineExactlyOne.lean`

- [x] **Step 1: Add the RED interface test**

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun

open CLRS.Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.PolyBuilder

#check affineSequentialExactlyOneGateStream
#check affineSequentialExactlyOneGateStream_eq_trace
#check affineSequentialExactlyOneBodyCfg
#check affineSequentialExactlyOneRevSteps
#check affineSequentialExactlyOneRev_runFrom
#check affineSequentialExactlyOneRev_steps_le
```

- [x] **Step 2: Observe the intended failure**

Run:

```text
lake env lean Tests/Chapter_34_CookLevin_AffineExactlyOne.lean
```

Expected: the imported module or first declaration is missing.  Do not add a
placeholder.

### Task 2: Fix the affine semantic trace

**Files:**

- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne/AffineTrace.lean`
- Test: `Tests/Chapter_34_CookLevin_AffineExactlyOne.lean`

- [x] **Step 1: Define the intended wire family and stream**

```lean
def affineSequentialExactlyOneWires (rowBase count : Nat) : List Nat :=
  (List.range count).map (fun wire => rowBase + wire)

def affineSequentialExactlyOneGateStream
    (start rowBase count : Nat) : List CircuitSym :=
  (exactlyOneGateTrace start
    (affineSequentialExactlyOneWires rowBase count)).gates.flatMap
      encodeCircuitGate
```

- [x] **Step 2: Publish the exact semantic equation**

```lean
theorem affineSequentialExactlyOneGateStream_eq_trace
    (start rowBase count : Nat) :
    affineSequentialExactlyOneGateStream start rowBase count =
      (exactlyOneGateTrace start
        ((List.range count).map (fun wire => rowBase + wire))).gates.flatMap
          encodeCircuitGate := by
  rfl
```

- [x] **Step 3: Define explicit affine chunks and prove trace equality**

Define private arithmetic `seen`, `duplicate`, and three-gate chunk functions
with gate indices `start + 3 * phase + offset`.  Prove their concatenation is
exactly `exactlyOneGateTrace start` over the shifted range.  Check `count = 0`
and a nonzero concrete example with `native_decide`.

### Task 3: Prove the contextual concrete run

**Files:**

- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne/AffineRun.lean`
- Test: `Tests/Chapter_34_CookLevin_AffineExactlyOne.lean`

- [x] **Step 1: Expose only reusable counter kernels**

Give public, documented names to the existing program configuration helper,
counter-preserving encoders for `seen`, `next`, and `wire`, the scan-register
update, and register cleanup.  Preserve all existing zero-based theorem names
and behavior.

- [x] **Step 2: Define the affine body entry**

```lean
def affineSequentialExactlyOneBodyCfg
    (start rowBase count : Nat) (output : List CircuitSym) :
    BuilderCfg sequentialExactlyOneRevProgram :=
  sequentialExactlyOneCfg .nextFirst none none false []
    ([.constFalseMark, .constFalseMark] ++ output)
    (List.replicate count ()) []
    (List.replicate start ())
    (List.replicate (start + 2) ())
    (List.replicate (rowBase + count) ())
```

- [x] **Step 3: Prove first, later, update, and final affine phases**

Each local theorem must preserve the arbitrary output suffix and all untouched
registers.  Use the counter encoder kernels rather than native evaluation.
Isolate `Nat` normalization into `omega`/`nlinarith` arithmetic facts.

- [x] **Step 4: Compose the public exact run**

```lean
def affineSequentialExactlyOneRev_runFrom
    (start rowBase count : Nat) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSequentialExactlyOneBodyCfg start rowBase count output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((affineSequentialExactlyOneGateStream start rowBase count).reverse ++
          output)))
      (affineSequentialExactlyOneRevSteps start rowBase count)
```

- [x] **Step 5: Prove a quadratic contextual bound**

```lean
theorem affineSequentialExactlyOneRev_steps_le
    (start rowBase count : Nat) :
    affineSequentialExactlyOneRevSteps start rowBase count ≤
      200 * (start + rowBase + count + 1) ^ 2
```

### Task 4: Integrate and verify the kernel

**Files:**

- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`
- Modify: `docs/proof-audits/2026-08-14-ch34-generator-attack.md`
- Test: `Tests/Chapter_34_CookLevin_AffineExactlyOne.lean`

- [x] **Step 1: Audit axioms and concrete examples**

Add `#print axioms` for the semantic equality, contextual run, and quadratic
bound.  Expected dependencies are only Lean/Mathlib foundations such as
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or project axiom.

- [x] **Step 2: Run focused verification**

```text
lake env lean Tests/Chapter_34_CookLevin_AffineExactlyOne.lean
lake env lean Tests/Chapter_34_CookLevin_ExactlyOneSerializer.lean
lake env lean Tests/Chapter_34_CookLevin_ExactlyOneGateTrace.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidity.lean
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne.AffineRun
python3 scripts/check_repository.py
git diff --check
```

No full-repository build belongs to this checkpoint.

- [x] **Step 3: Commit the independently accepted slice**

```text
git add CLRSLean/Chapter_34.lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne.lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne/AffineTrace.lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne/AffineRun.lean Tests/Chapter_34_CookLevin_AffineExactlyOne.lean docs/index.md docs/proof-audits/2026-08-14-ch34-generator-attack.md literate.toml
git commit -m "feat(ch34): lift exactly-one serialization affinely"
```
