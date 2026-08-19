# Chapter 34 Exact Polynomial Unary Frame Family Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that one fixed compiled TM2 turns a raw input word into the concatenated delimiter-bearing unary encodings of a fixed finite list of polynomials evaluated at the input length.

**Architecture:** Enumerate sentinel-extended tuples at one shared depth that dominates every polynomial degree. Append fixed field tags to the tuple list using the verified sentinel and bounded-loop builders. Run one verified row-major nested loop over `tuples ++ tags`: tuple outer rows emit nothing, and each tag outer row emits that polynomial's ticks across all tuple inner rows followed by exactly one separator in the tag suffix. Compose all concrete machines with `comp_scratch` and prove that the output is `encodeUnaryFrame (polynomials.map (fun p => p.eval input.length))`.

**Tech Stack:** Lean 4, Mathlib polynomials and lists, Chapter 34 `PolyBuilder`, Lake focused builds.

---

### Task 1: Add a red public-interface test

- [x] Add `Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryFrameFamily.lean` importing the intended module and checking:

```lean
#check polynomialFamilyDegree
#check exactPolynomialUnaryFrames
#check exactPolynomialUnaryFrames_eq
#check exactPolynomialUnaryFrames_computableInPolyTime
```

- [x] Run the focused test and confirm the expected missing-module failure.

### Task 2: Prove shared-depth exact polynomial emission

- [x] Define `polynomialFamilyDegree` as the sum of member natural degrees and prove every indexed member degree is bounded by it.
- [x] Define `exactPolynomialAtDepthBody` and `exactPolynomialAtDepthClock` using `tuplePrefixMatches` at the shared depth.
- [x] Adapt the exact-clock counting proof to show, under `p.natDegree ≤ depth`:

```lean
@[simp] theorem exactPolynomialAtDepthClock_length ... :
    (exactPolynomialAtDepthClock depth p input).length = p.eval input.length
```

### Task 3: Build the concrete tuple-plus-tag input

- [x] Define a bounded-loop body over a sentinel-terminated tuple list whose ordinary symbols emit `Sum.inl tuple` and whose sentinel emits all fixed `Fin polynomials.length` tags as `Sum.inr`.
- [x] Prove the exact semantic output `tuples.map Sum.inl ++ (List.finRange polynomials.length).map Sum.inr`.
- [x] Package the bounded-loop witness and compose it with the concrete sentinel appender.

### Task 4: Prove the nested-loop frame-family semantics

- [x] Define the pair-local nested-loop body: `(tag, tuple)` emits the shared-depth polynomial ticks; `(tag, firstTag)` emits one separator; all other pairs emit nothing.
- [x] Prove one tag row is exactly `encodeUnaryFrameBlock ((polynomials.get tag).eval input.length)`.
- [x] Prove tuple outer rows vanish and tag outer rows concatenate in `List.finRange` order, then identify the result with:

```lean
def exactPolynomialUnaryFrames {Γ : Type}
    (polynomials : List (Polynomial Nat)) (input : List Γ) :
    List UnaryFrameSym :=
  encodeUnaryFrame (polynomials.map fun p => p.eval input.length)
```

### Task 5: Compose, expose, verify, and commit

- [x] Compose source sentinel insertion, shared tuple enumeration, tuple-list sentinel insertion, tuple/tag bounded relabeling, and the nested-loop serializer using only concrete `TM2ComputableInPolyTime` witnesses.
- [x] Expose the module through the PolyBuilder facade, Chapter 34 root, `literate.toml`, and `docs/index.md`; add focused semantic examples and axiom prints.
- [x] Run the focused test, production module, Chapter 34 root, status/progress checks, placeholder scan, and `git diff --check`; confirm only standard axioms.
- [x] Obtain an independent review and commit the stage as `feat(ch34): compile polynomial unary frame families`.
