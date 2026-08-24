# Chapter 34 Strict Section 34.5 Closure Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the remaining strict CLRS §34.5 boundary by proving honest serialized, fixed polynomial-time TM2, NP-membership, NP-hardness, and NP-completeness layers for HAM-CYCLE, decision-TSP, and SUBSET-SUM.

**Architecture:** Finish HAM-CYCLE first on the existing unary graph grammar, reusing the proven VERTEX-COVER parser guard, stream combinators, and verifier components.  Then introduce one shared self-delimiting binary-natural codec and its fixed-machine interface; decision-TSP and SUBSET-SUM receive separate tagged raw grammars, certificate semantics, reduction machines, and public NP-completeness wrappers.  Each public interface is frozen with a failing `#check` test before production declarations are added, and every stage is a separate reviewable commit.

**Tech Stack:** Lean 4.32.0-rc1, Mathlib, the repository's `Turing.TM2`, `TM2ComputableInPolyTime`, `PolyTimeReducible`, `PolyTimeVerifiable`, `ClassNP`, `NPHard`, and `NPComplete` interfaces.

---

## File structure

- `HamiltonianCycle/RawReduction.lean`: total raw VERTEX-COVER-to-HAM-CYCLE map and all-input membership equivalence.
- `HamiltonianCycle/Reduction/EncodingBounds.lean`: edge-count, endpoint, and encoded-output polynomial bounds for the typed gadget.
- `HamiltonianCycle/RawReductionLength.lean`: all-input raw map length theorem.
- `HamiltonianCycle/VerifierMachine/`: fixed checker pipeline, exact semantics, and polynomial runtime.
- `HamiltonianCycle/ReductionMachine/`: fixed generator pipeline and exact raw-map computation theorem.
- `HamiltonianCycle/NP.lean`, `HamiltonianCycle/NPCompleteness.lean`: public complexity wrappers.
- `BinaryNat/`: shared canonical binary-natural encoder/parser, round trip, length bounds, and fixed-machine utilities.
- `TravelingSalesperson/Encoding/`: tagged honest TSP instance/certificate grammar over binary naturals.
- `TravelingSalesperson/Language.lean`, `Certificate/`, `VerifierMachine/`, `ReductionMachine/`, `NP.lean`, `NPCompleteness.lean`: strict decision-TSP closure.
- `SubsetSum/Encoding/`: tagged honest SUBSET-SUM instance/certificate grammar over binary naturals.
- `SubsetSum/Language.lean`, `Certificate/`, `VerifierMachine/`, `ReductionMachine/`, `NP.lean`, `NPCompleteness.lean`: strict SUBSET-SUM closure.
- `Tests/Chapter_34_{HamiltonianCycle,TSP,SubsetSum}_NPComplete.lean`: public surface and axiom audits.
- `CLRSLean/Chapter_34.lean`, `CLRSLean/FourthEdition/Chapter_34.lean`, `CLRSLean/Status.lean`, `docs/proof-map.md`, `docs/proof-status-board.md`, `docs/clrs-proof-progress.csv`, `literate.toml`: final wiring and status truth.

### Task 1: Freeze and close the raw HAM-CYCLE semantic map

**Files:**
- Create: `Tests/Chapter_34_HamiltonianCycle_RawReduction.lean`
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/HamiltonianCycle/RawReduction.lean`
- Modify: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/HamiltonianCycle.lean`

- [ ] **Step 1: Write the failing public interface test**

```lean
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle

#check CLRS.Chapter34.vertexCoverToHamiltonianMap
#check CLRS.Chapter34.vertexCoverToHamiltonianMap_mem_HAMCYCLE_iff
#print axioms CLRS.Chapter34.vertexCoverToHamiltonianMap_mem_HAMCYCLE_iff
```

- [ ] **Step 2: Verify RED**

Run: `lake env lean Tests/Chapter_34_HamiltonianCycle_RawReduction.lean`

Expected: failure naming the missing `vertexCoverToHamiltonianMap` declaration.

- [ ] **Step 3: Implement the total map and exact semantics**

Define the raw map by complete decoding; map parser failures and decoded ill-formed source instances to `canonicalHamiltonianNoInstance`, and map well-formed sources to `vertexCoverToHamiltonianInstance`.  Prove the fallback is outside `HAMCYCLE`, prove the constructed target has `targetSize = vertexCount`, and combine `vertexCoverToHamiltonianInstance_wellFormed` with `vertexCoverToHamiltonianInstance_correct` to establish:

```lean
theorem vertexCoverToHamiltonianMap_mem_HAMCYCLE_iff
    (input : List VertexCoverSym) :
    vertexCoverToHamiltonianMap input ∈ HAMCYCLE ↔ input ∈ VERTEXCOVER
```

- [ ] **Step 4: Verify GREEN and commit**

Run `lake env lean Tests/Chapter_34_HamiltonianCycle_RawReduction.lean`, `lake build +CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.RawReduction`, and `git diff --check`.

Commit message: `feat(ch34): add total HAM-CYCLE raw reduction semantics`.

### Task 2: Prove HAM-CYCLE output-size bounds

**Files:**
- Create: `Tests/Chapter_34_HamiltonianCycle_RawLength.lean`
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/HamiltonianCycle/Reduction/EncodingBounds.lean`
- Create: `CLRSLean/Chapter_34/Section_34_5_NP_Complete_Problems/HamiltonianCycle/RawReductionLength.lean`

- [ ] **Step 1: Add the failing theorem check**

```lean
#check CLRS.Chapter34.HamiltonianCycleReduction.clrsReductionEdges_length_le
#check CLRS.Chapter34.vertexCoverToHamiltonianMap_length_le
```

Run the test and confirm the missing declarations.

- [ ] **Step 2: Bound every generated edge family**

Prove incidence-chain edges are bounded by twice the source edge count, selector endpoint edges by `2 * vertexCount * targetSize`, selector-clique edges by `targetSize ^ 2`, and all output endpoints by `12 * edges.length + targetSize`.  Use `encodeCliqueInstance_length` to convert these facts to a cubic encoded-output bound.

- [ ] **Step 3: Prove the all-input raw theorem**

Expose a theorem of the form:

```lean
theorem vertexCoverToHamiltonianMap_length_le (input : List VertexCoverSym) :
    (vertexCoverToHamiltonianMap input).length ≤
      1000 * (input.length + 1) ^ 3
```

Handle parser failures and ill-formed instances by the fixed fallback encoding.

- [ ] **Step 4: Verify and commit**

Run the two focused test/source commands and commit as `feat(ch34): bound HAM-CYCLE raw reduction output`.

### Task 3: Build the fixed HAM-CYCLE verifier and NP membership

**Files:**
- Create: `Tests/Chapter_34_HamiltonianCycle_VerifierMachine.lean`
- Create: focused modules under `HamiltonianCycle/VerifierMachine/`
- Create: `HamiltonianCycle/VerifierMachine.lean`
- Create: `HamiltonianCycle/NP.lean`

- [ ] **Step 1: Freeze the public machine interface in RED**

```lean
#check CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.computableInPolyTime
#check CLRS.Chapter34.generalHAMCYCLE_polyTimeVerifiable
#check CLRS.Chapter34.HAMCYCLE_mem_ClassNP
```

- [ ] **Step 2: Reuse graph and certificate preprocessing**

Compose the existing raw graph normalizer/well-formedness guard, unary certificate parser/canonicalizer, range check, nodup check, cardinality check, and batch adjacency lookup.  Add only the cycle-specific checks `targetSize = vertexCount`, certificate length `= vertexCount`, consecutive adjacency, and closing last-to-first adjacency.

- [ ] **Step 3: Prove exact all-input semantics and runtime**

Prove the fixed machine outputs `TM2Comp.boolEncoding (hamiltonianCycleVerifier certificate input)` on every paired input and satisfies a polynomial bound in the pair encoding length.

- [ ] **Step 4: Package NP membership and verify**

Use `mem_generalHAMCYCLE_iff_exists_bounded_certificate` and the checker machine to prove `generalHAMCYCLE_polyTimeVerifiable` and `HAMCYCLE_mem_ClassNP`.  Run the focused interface test and source build, audit headline axioms, and commit as `feat(ch34): prove HAM-CYCLE is in NP`.

### Task 4: Build the fixed HAM-CYCLE reduction machine and NP-completeness

Progress checkpoint (2026-08-25): the fixed nondegenerate header, the complete
fourteen-edge internal widget family, their combined encoding prefix, and the
complete selector clique are implemented.  The selector-clique machine
extracts `12 * edgeCount` and `targetSize`, generates shifted triangular rows,
loads the runtime base once, and reuses the verified pair-row formatter.  Each
public boundary has exact canonical semantics and a polynomial-time TM2
witness.  The two source-incidence-dependent families remain the active core.
Their common canonical vertex-query/graph pair stream is now produced by a
fixed polynomial-time machine, so the remaining operational proof begins at
one shared repeated incidence scanner rather than two independent parsers.
That scanner is now complete: it scans the raw graph once per descending
vertex query, preserves occurrence indices across rows, reverses the result
into canonical vertex order, and has an exact semantic theorem plus a uniform
cubic runtime bound.  The incidence-chain formatter is also complete: one
fixed controller parses each `(occurrence, side)` pair, retains consecutive
references across a row, emits the exact normalized gadget links, and has a
linear runtime bound in the scanner-stream length.  The active boundary is
further narrowed by a fixed endpoint extractor: it retains the first and last
occurrence of every nonempty incidence row, emits their two canonical gadget
ports, and has a linear runtime bound in the scanner-stream length.  The
selector-endpoint pipeline is now complete as well: a zero-step affine copier
repeats the extracted ports once per selector, and the offset-aware pair-row
controller was generalized to arbitrary marked rows with a quadratic input
bound.  Its output is proved permutation-equivalent to the textbook edge
family, preserving duplicates.  The active boundary is therefore reduced to
final guarded composition and the raw hardness packaging.

**Files:**
- Create: `Tests/Chapter_34_HamiltonianCycle_NPComplete.lean`
- Create: focused modules under `HamiltonianCycle/ReductionMachine/`
- Create: `HamiltonianCycle/ReductionMachine.lean`
- Create: `HamiltonianCycle/NPCompleteness.lean`

- [ ] **Step 1: Freeze final HAM-CYCLE checks in RED**

```lean
#check CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.computableInPolyTime
#check CLRS.Chapter34.VERTEXCOVER_reducible_to_HAMCYCLE
#check CLRS.Chapter34.HAMCYCLE_npHard
#check CLRS.Chapter34.HAMCYCLE_npComplete
```

- [ ] **Step 2: Generate the typed gadget stream with fixed controllers**

Reuse the normalized source instance and well-formedness flag.  Implement separately bounded controllers for the transformed header, the fourteen-edge widget template per source edge occurrence, incidence-chain links, selector endpoint links, selector-clique pairs, and the guarded fallback selector.

- [ ] **Step 3: Prove exact computation and polynomial runtime**

Compose the controllers into one `TM2ComputableInPolyTime id id vertexCoverToHamiltonianMap` witness.  The semantic equality must hold on malformed, ill-formed, degenerate, and ordinary inputs.

- [ ] **Step 4: Package hardness/completeness and commit**

Use `VERTEXCOVER_npHard`, the new reduction, and Task 3 membership.  Verify focused tests and the HAM facade, then commit as `feat(ch34): prove HAM-CYCLE NP-complete`.

### Task 5: Add the shared binary-natural codec

**Files:**
- Create: `Tests/Chapter_34_BinaryNat.lean`
- Create: `CLRSLean/Chapter_34/BinaryNat/Basic.lean`
- Create: `CLRSLean/Chapter_34/BinaryNat/Parser.lean`
- Create: `CLRSLean/Chapter_34/BinaryNat/RoundTrip.lean`
- Create: `CLRSLean/Chapter_34/BinaryNat/Length.lean`
- Create: `CLRSLean/Chapter_34/BinaryNat/Machine.lean`
- Create: `CLRSLean/Chapter_34/BinaryNat.lean`

- [ ] **Step 1: Freeze codec laws in RED**

```lean
#check CLRS.Chapter34.decodeBinaryNat_encode
#check CLRS.Chapter34.encodeBinaryNat_length_le
#check CLRS.Chapter34.Turing.BinaryNat.encoderComputableInPolyTime
#check CLRS.Chapter34.Turing.BinaryNat.decoderComputableInPolyTime
```

- [ ] **Step 2: Implement a canonical self-delimiting representation**

Represent zero by one zero bit and positive naturals by a leading one followed by the remaining big-endian bits, terminated by a field marker supplied by the enclosing grammar.  Reject leading-zero nonzero encodings so round trips and parser uniqueness are exact.

- [ ] **Step 3: Prove logarithmic length and fixed-machine behavior**

Relate physical length to `Nat.log2`, prove decode-after-encode, and provide fixed polynomial-time encoder/decoder witnesses reusable through alphabet injections.

- [ ] **Step 4: Verify and commit**

Run only the codec interface/source builds and commit as `feat(ch34): add reusable binary natural codec`.

### Task 6: Close honest decision-TSP

**Files:**
- Create: `Tests/Chapter_34_TSP_NPComplete.lean`
- Create: focused modules under `TravelingSalesperson/Encoding/`, `Certificate/`, `VerifierMachine/`, and `ReductionMachine/`
- Create: `TravelingSalesperson/Language.lean`
- Create: `TravelingSalesperson/NP.lean`
- Create: `TravelingSalesperson/NPCompleteness.lean`
- Modify: `TravelingSalesperson.lean`

- [ ] **Step 1: Freeze the complete public surface in RED**

```lean
#check CLRS.Chapter34.GeneralTSP
#check CLRS.Chapter34.tspVerifier_eq_true_iff
#check CLRS.Chapter34.generalTSP_polyTimeVerifiable
#check CLRS.Chapter34.HAMCYCLE_reducible_to_TSP
#check CLRS.Chapter34.TSP_npComplete
```

- [ ] **Step 2: Implement the honest finite raw grammar**

Encode `vertexCount`, `budget`, and exactly `vertexCount ^ 2` binary weights in row-major order, with separate instance/certificate markers.  Decode the matrix to the existing typed `TSPInstance`; reject incomplete, overlong, or noncanonical fields.

- [ ] **Step 3: Prove certificate semantics and NP membership**

Use a binary list of vertex indices as the tour certificate.  Check exact length, nodup, range, and cyclic total weight against the budget.  Prove a polynomial certificate bound and a fixed polynomial-time checker.

- [ ] **Step 4: Prove the raw HAM-CYCLE reduction**

Translate a decoded well-formed graph to the existing `hamiltonianToTSPInstance`; malformed graph strings go to a fixed TSP no-instance.  Stream binary weights `1` for edges and `2` for nonedges, prove the raw membership equivalence from `hamiltonianToTSP_correct`, and prove fixed-machine polynomial runtime.

- [ ] **Step 5: Package and commit**

Prove `TSP_mem_ClassNP`, `TSP_npHard`, and `TSP_npComplete`; run the focused interface/facade builds and axiom audit, then commit as `feat(ch34): prove decision-TSP NP-complete`.

### Task 7: Close honest SUBSET-SUM

**Files:**
- Create: `Tests/Chapter_34_SubsetSum_NPComplete.lean`
- Create: focused modules under `SubsetSum/Encoding/`, `Certificate/`, `VerifierMachine/`, and `ReductionMachine/`
- Create: `SubsetSum/Language.lean`
- Create: `SubsetSum/NP.lean`
- Create: `SubsetSum/NPCompleteness.lean`
- Modify: `SubsetSum.lean`

- [ ] **Step 1: Freeze the complete public surface in RED**

```lean
#check CLRS.Chapter34.GeneralSUBSETSUM
#check CLRS.Chapter34.subsetSumVerifier_eq_true_iff
#check CLRS.Chapter34.generalSUBSETSUM_polyTimeVerifiable
#check CLRS.Chapter34.ThreeCNFSAT_reducible_to_SUBSETSUM
#check CLRS.Chapter34.SUBSETSUM_npComplete
```

- [ ] **Step 2: Implement the honest finite raw grammar**

Encode a binary target and a binary list of item values.  Certificates are duplicate-free binary item indices; decoding builds the existing finite indexed instance rather than relying on proof-only item labels.

- [ ] **Step 3: Prove certificate semantics and NP membership**

Check index range, nodup, and exact selected sum with a fixed addition/comparison pipeline.  Bound certificate length by the instance word length and prove a fixed polynomial-time verifier.

- [ ] **Step 4: Bridge and stream the 3-CNF construction**

Define the indexed list order for positive-choice, negative-choice, first-slack, and second-slack items.  Prove that selecting indices is equivalent to selecting the existing labeled `Finset` items.  Generate packed values directly from their bounded base-`B` columns, emit them in binary without materializing unary magnitudes, and prove the raw membership equivalence using `cnfToSubsetSum_correct`.

- [ ] **Step 5: Prove bit/runtime bounds, package, and commit**

Bound each packed value's binary length by polynomially many columns times the logarithm of the polynomial base; prove the fixed reduction machine polynomial; derive `SUBSETSUM_mem_ClassNP`, hardness, and `SUBSETSUM_npComplete`.  Run focused tests/builds and commit as `feat(ch34): prove SUBSET-SUM NP-complete`.

### Task 8: Reconcile Chapter 34 and integrate

**Files:**
- Modify: all facade, chapter-guide, progress, proof-map, proof-status, and `literate.toml` files named in the file structure.

- [ ] **Step 1: Wire every new focused module**

Import strict facades from `CLRSLean/Chapter_34.lean`, register every new rendered source module in `literate.toml`, and keep individual implementation files small enough for focused compilation.

- [ ] **Step 2: Update the single source of status truth**

Change Chapter 34 from `partial` only after all three `NPComplete` theorems compile.  Remove the HAM-CYCLE/TSP/SUBSET-SUM strict gaps from `CLRSLean/Status.lean`, `docs/proof-map.md`, and `docs/proof-status-board.md`; update `docs/clrs-proof-progress.csv` and regenerate `CLRSLean/Progress.lean` with the repository script.

- [ ] **Step 3: Run final verification**

Run all three strict interface tests, `rg -n '\b(sorry|admit|axiom)\b'` over the new theorem-bearing paths, `git diff --check`, `uv run python scripts/check_repository.py`, and one final `lake build CLRSLean`.  Do not build or deploy the website because this is proof work, not a publishing request.

- [ ] **Step 4: Commit and prepare remote integration**

Commit documentation/status reconciliation separately as `docs(ch34): close strict section 34.5 boundary`.  Review the complete diff and commit history before pushing the feature branch and opening or updating the integration PR.
