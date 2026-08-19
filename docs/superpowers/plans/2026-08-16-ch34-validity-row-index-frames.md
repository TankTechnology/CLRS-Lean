# Validity Row Index Frames Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a fixed polynomial-time TM2 that maps the raw verifier word to the delimiter-bearing unary ordinals of every actual Cook--Levin validity row.

**Architecture:** Compose the existing exact polynomial clock with the verified unary-index streamer, then relabel `true/false` to `tick/separator` using a bounded loop. Specialize the generic compiler to `verifierHorizon W + 1` and prove that the decoded ordinals have exactly the same length and order as `verifierValidityRowFramesByLength W`.

**Tech Stack:** Lean 4, Mathlib polynomials, CLRS-Lean TM2 composition, PolyBuilder bounded loops, focused `#check`/axiom tests.

---

### Task 1: Exact polynomial unary-index frame compiler

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactPolynomialUnaryIndexFrames.lean`
- Test: `Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryIndexFrames.lean`

- [x] **Step 1: Write the failing public-interface test**

```lean
#check exactPolynomialUnaryIndexFrames
#check exactPolynomialUnaryIndexFrames_eq_map
#check exactPolynomialUnaryIndexFrames_computableInPolyTime
```

- [x] **Step 2: Verify RED**

Run: `lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryIndexFrames.lean`

Expected: failure because the new module or declarations do not exist.

- [x] **Step 3: Implement the semantic relabeling and TM2 composition**

```lean
def unaryIndexFrameSymbol : Bool → UnaryFrameSym
  | true => .tick
  | false => .separator

def exactPolynomialUnaryIndexFrames {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) : List UnaryFrameSym :=
  encodeUnaryFrame (List.range (p.eval input.length))

noncomputable def exactPolynomialUnaryIndexFrames_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryIndexFrames Γ p)
```

The proof must compose `exactPolynomialClock_computableInPolyTime`,
`unaryIndexStream_computableInPolyTime`, and
`boundedLoop_computableInPolyTime` with only `comp_scratch`.

- [x] **Step 4: Verify GREEN**

Run:

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryIndexFrames
lake env lean Tests/Chapter_34_PolyBuilder_ExactPolynomialUnaryIndexFrames.lean
```

Expected: both commands exit zero; printed axioms contain only the repository's standard `propext`, `Classical.choice`, and `Quot.sound` surface.

### Task 2: Specialize to every actual validity row

**Files:**
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityRowIndices.lean`
- Test: `Tests/Chapter_34_CookLevin_ValidityRowIndices.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization.lean`
- Modify: `CLRSLean/Chapter_34.lean`
- Modify: `literate.toml`
- Modify: `docs/index.md`

- [x] **Step 1: Write the failing Cook--Levin interface test**

```lean
#check verifierValidityRowCountPolynomial
#check verifierValidityRowIndexFrames
#check verifierValidityRowIndexFrames_eq_frameOrdinals
#check verifierValidityRowIndexFrames_computableInPolyTime
```

- [x] **Step 2: Verify RED**

Run: `lake env lean Tests/Chapter_34_CookLevin_ValidityRowIndices.lean`

Expected: failure because the specialized module or declarations do not exist.

- [x] **Step 3: Implement the specialization and exact bridge**

```lean
def verifierValidityRowCountPolynomial (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierHorizon W + 1

def verifierValidityRowIndexFrames (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  exactPolynomialUnaryIndexFrames
    (verifierValidityRowCountPolynomial W) input

theorem verifierValidityRowIndexFrames_eq_frameOrdinals
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowIndexFrames W input =
      encodeUnaryFrame
        (List.range (verifierValidityRowFramesByLength W input.length).length)
```

The theorem must unfold `arithmeticValidityRowFrames` and prove exact equality with the runtime family length, not merely an upper bound.

- [x] **Step 4: Verify GREEN and chapter integration**

Run:

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowIndices
lake env lean Tests/Chapter_34_CookLevin_ValidityRowIndices.lean
lake env lean CLRSLean/Chapter_34.lean
python3 scripts/check_status_claims.py
python3 scripts/check_progress_csv.py --check-dashboard
git diff --check
```

Expected: all commands exit zero. The site-consistency checker may retain its known pre-existing Chapter 34 omissions, but it must not mention either new module.

- [x] **Step 5: Review, commit, and push**

Request an independent proof review. Fix every Critical or Important finding, rerun the focused checks, then commit with:

```bash
git commit -m "feat(ch34): compile validity row index frames"
git push origin codex/ch34-textbook-closure
```
