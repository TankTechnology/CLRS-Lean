# Chapter 34 Exact Polynomial Unary Frame Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that one fixed compiled TM2 turns a raw input word into the delimiter-bearing unary block whose value is an arbitrary fixed polynomial evaluated at the input length.

**Architecture:** Reuse `exactPolynomialClock_computableInPolyTime` to generate exactly `p.eval input.length` unit tokens. Compose it with the verified sentinel appender and a new bounded-loop relabeler that maps each `some ()` to `.tick` and the final `none` to `.separator`. Identify the composed output with `encodeUnaryFrameBlock (p.eval input.length)` using the exact clock-length theorem.

**Tech Stack:** Lean 4, Mathlib TM2 computability, Chapter 34 `PolyBuilder`, Lake focused builds.

---

### Task 1: Pin the public theorem with a red interface test

- [x] Add `Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryFrame.lean` importing the intended production module and checking:

```lean
#check exactPolynomialUnaryFrame
#check exactPolynomialUnaryFrame_eq
#check exactPolynomialUnaryFrame_computableInPolyTime
```

- [x] Run `lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryFrame.lean` and confirm the expected unknown-module or unknown-identifier failure before production code exists.

### Task 2: Prove the fixed sentinel-to-frame relabeler

- [x] Add `PolyBuilder/ExactPolynomialUnaryFrame.lean`, importing `ExactPolynomialClock` and `UnaryFrame`.
- [x] Define the finite symbol-local body:

```lean
def unaryFrameSymbolBody : LoopBody (Option Unit) UnaryFrameSym where
  emit
    | some _ => [.tick]
    | none => [.separator]
  cost := fun _ => 1
  emit_length_le_cost := by intro symbol; cases symbol <;> simp
```

- [x] Define `unaryFrameSymbols` as the corresponding `flatMap`, prove that applying it to `sentinelInput tokens` is exactly `encodeUnaryFrameBlock tokens.length`, and package its concrete bounded-loop TM2 as:

```lean
noncomputable def unaryFrameSymbols_computableInPolyTime :
    Turing.TM2ComputableInPolyTime id id unaryFrameSymbols
```

- [x] Run the focused test and the production module; fix only errors local to this checkpoint.

### Task 3: Compose the exact source-to-unary-block compiler

- [x] Define the public source function:

```lean
def exactPolynomialUnaryFrame {Γ : Type} (p : Polynomial Nat)
    (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrameBlock (p.eval input.length)
```

- [x] Prove the semantic bridge from the three-stage pipeline:

```lean
theorem exactPolynomialUnaryFrame_eq {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) :
    unaryFrameSymbols (sentinelInput (exactPolynomialClock p input)) =
      exactPolynomialUnaryFrame p input
```

- [x] Compose `exactPolynomialClock_computableInPolyTime`, `sentinelInput_computableInPolyTime`, and `unaryFrameSymbols_computableInPolyTime` with `TM2Comp.TM2ComputableInPolyTime.comp_scratch`, obtaining:

```lean
noncomputable def exactPolynomialUnaryFrame_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryFrame Γ p)
```

- [x] Run `lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryFrame.lean` and `lake env lean CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactPolynomialUnaryFrame.lean`.

### Task 4: Expose, audit, and commit the checkpoint

- [x] Import the module from `PolyBuilder.lean` and `Chapter_34.lean`, then add `#print axioms exactPolynomialUnaryFrame_computableInPolyTime` to the focused test.
- [x] Run the focused test, `lake env lean CLRSLean/Chapter_34.lean`, and the repository's diff/axiom checks applicable to Chapter 34.
- [x] Confirm `git diff --check` is clean and inspect the staged diff for accidental unrelated changes.
- [x] Commit this independently verifiable stage with message `feat(ch34): compile exact polynomial unary frames`.
