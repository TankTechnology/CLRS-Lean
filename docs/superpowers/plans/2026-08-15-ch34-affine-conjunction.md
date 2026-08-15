# Ch34 Affine Conjunction Controller Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build one fixed finite TM2 controller that emits the exact tail-first conjunction of a runtime frame, then instantiate it at the final conjunction of one arithmetic Cook--Levin validity row.

**Architecture:** Extend the existing counter-preserving serializer with one small contextual AND kernel.  A new delimiter-bearing controller loads the start wire once, reads `wires.reverse` at runtime, redirects the AND kernel back to its wire loader, clears the accumulator at `frameEnd`, and exposes both redirectable-finish and standalone-halt theorems.  The arithmetic layer packages the already-proved final source-wire list into this generic frame.

**Tech Stack:** Lean 4, Mathlib `Turing.TM2`, `StateTransition.EvalsToInTime`, the Ch34 `PolyBuilder` DSL, unary runtime frames, focused `lake build` and `lake env lean` checks.

---

## File map

- Modify `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne.lean`: add only the finite labels and instructions needed by the reusable AND kernel.
- Create `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean`: own the AND core theorem, runtime frame, fixed controller, exact run, and quadratic bound.
- Modify `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityStack.lean`: instantiate the generic frame at the real final-conjunction indices.
- Create `Tests/Chapter_34_PolyBuilder_Conjunction.lean`: freeze the reusable controller surface and axiom dependencies.
- Modify `Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean`: freeze arithmetic stream equality, run, and bound.
- Modify `docs/proof-audits/2026-08-14-ch34-generator-attack.md`: record the new concrete boundary and rejected routes.
- Update this plan's checkboxes after every verified commit.

### Task 1: Lock the RED public interfaces

**Files:**
- Create: `Tests/Chapter_34_PolyBuilder_Conjunction.lean`
- Modify: `Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean`

- [x] **Step 1: Create the reusable RED sentinel**

Create the test with the exact intended public surface:

```lean
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction

open StateTransition
open CLRS.Chapter34.Turing.PolyBuilder

#check AffineConjunctionFrame
#check encodeAffineConjunctionFrame
#check encodeAffineConjunctionFrame_length
#check affineConjunctionGateStream
#check affineConjunctionGateStream_eq_trace
#check affineAndRevCoreSteps
#check affineAndRev_runToDoneLabel
#check affineConjunctionRevProgram
#check affineConjunctionLoopCfg
#check affineConjunctionFinishCfg
#check affineConjunctionRevSteps
#check affineConjunction_runToFinish
#check affineConjunction_run
#check affineConjunctionRev_steps_le

#print axioms affineAndRev_runToDoneLabel
#print axioms affineConjunctionGateStream_eq_trace
#print axioms affineConjunction_runToFinish
#print axioms affineConjunction_run
#print axioms affineConjunctionRev_steps_le
```

- [x] **Step 2: Add arithmetic RED checks**

Append these checks to the existing generator-validity stack sentinel:

```lean
#check arithmeticValidityFinalConjunctionFrame
#check arithmeticValidityFinalConjunctionGateStream_eq_framed
#check arithmeticValidityFinalConjunctionRev_runFrom
#check arithmeticValidityFinalConjunctionRev_steps_le

#print axioms arithmeticValidityFinalConjunctionGateStream_eq_framed
#print axioms arithmeticValidityFinalConjunctionRev_runFrom
#print axioms arithmeticValidityFinalConjunctionRev_steps_le
```

- [x] **Step 3: Run RED checks**

Run:

```bash
lake env lean Tests/Chapter_34_PolyBuilder_Conjunction.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean
```

Expected: the first command reports that `PolyBuilder.Conjunction` is absent;
the second reports the four missing arithmetic interfaces.

- [x] **Step 4: Commit the RED contract**

```bash
git add Tests/Chapter_34_PolyBuilder_Conjunction.lean \
  Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean
git commit -m "test(ch34): lock affine conjunction interfaces"
```

### Task 2: Add the contextual AND kernel

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne.lean`
- Create: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean`

- [x] **Step 1: Extend the shared finite control**

Append `conjunctionSource` and `conjunctionCarry` to the existing
`SequentialExactlyOneCont` declaration, then add the grouped phase type:

```lean
inductive SequentialConjunctionLabel
  | push | clearWire | incCarry | done
deriving DecidableEq, Fintype
```

Append `conjunction (phase : SequentialConjunctionLabel)` to the existing
`SequentialExactlyOneLabel` declaration.

Add these program equations, keeping all runtime naturals in counters:

```lean
| .resume .conjunctionSource =>
    .jump (.encode .seen .conjunctionCarry)
| .resume .conjunctionCarry =>
    .jump (.conjunction .clearWire)
| .conjunction .push =>
    .pushOutput .andMark (.encode .wire .conjunctionSource)
| .conjunction .clearWire =>
    .dec₃ (.conjunction .incCarry) (.conjunction .clearWire)
| .conjunction .incCarry =>
    .inc₁ (.conjunction .done)
| .conjunction .done => .halt
```

- [x] **Step 2: Define the exact kernel configurations**

Start `Conjunction.lean` by importing `UnaryFrame` and the affine exactly-one
run layer.  Define:

```lean
def affineAndGateStream (carry source : Nat) : List CircuitSym :=
  encodeCircuitGate (.and source carry)

def affineAndBodyCfg (carry source : Nat) (output : List CircuitSym) :=
  sequentialExactlyOneCfg (.conjunction .push) none none false [] output [] []
    (List.replicate carry ()) [] (List.replicate source ())

def affineAndCoreExitCfg (carry : Nat) (output : List CircuitSym) :=
  sequentialExactlyOneCfg (.conjunction .done) none none false [] output [] []
    (List.replicate (carry + 1) ()) [] []

def affineAndRevCoreSteps (carry source : Nat) : Nat :=
  6 * source + 5 * carry + 11
```

- [x] **Step 3: Prove the one-register cleanup loop**

Prove by induction on `source` that `.conjunction .clearWire` reaches
`.conjunction .incCarry` in `source + 1` steps.  Preserve `counter₁`, output,
and all empty scratch components exactly.  The successor case must rewrite
`List.replicate_succ` and use `Function.iterate_succ_apply` once.

- [x] **Step 4: Compose the exact AND core run**

Build `affineAndRev_runToDoneLabel` from these exact segments:

```text
push tag                         1
encode source        5*source + 3
resume to carry                  1
encode carry          5*carry + 3
resume to cleanup                1
clear source            source + 1
increment carry                  1
```

The target output must simplify to
`(affineAndGateStream carry source).reverse ++ output`, and the total must
simplify to `affineAndRevCoreSteps carry source` with `omega`.

- [x] **Step 5: Turn the kernel portion GREEN**

Run:

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
lake env lean Tests/Chapter_34_PolyBuilder_Conjunction.lean
```

Expected: the module builds; only the not-yet-defined outer-controller checks
remain red.

- [x] **Step 6: Commit the kernel**

```bash
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/ExactlyOne.lean \
  CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean
git commit -m "feat(ch34): add contextual conjunction gate kernel"
```

### Task 3: Define the runtime frame and semantic stream

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean`
- Test: `Tests/Chapter_34_PolyBuilder_Conjunction.lean`

- [x] **Step 1: Add frame encoding**

Define exactly:

```lean
structure AffineConjunctionFrame where
  start : Nat
  wires : List Nat
deriving DecidableEq, Repr

def encodeAffineConjunctionSources (sources : List Nat) :
    List UnaryFrameSym :=
  sources.flatMap encodeUnaryFrameBlock

def encodeAffineConjunctionFrame (frame : AffineConjunctionFrame) :
    List UnaryFrameSym :=
  encodeUnaryFrameBlock frame.start ++
    encodeAffineConjunctionSources frame.wires.reverse ++ [.frameEnd]
```

Prove the exact length as `frame.start + 2 +
(frame.wires.map fun wire => wire + 1).sum`.

- [x] **Step 2: Add the processing-order trace**

Define a tail-first fold over already-reversed sources:

```lean
def AffineConjunction.chunksFrom : Nat → List Nat → List CircuitGate
  | _, [] => []
  | carry, source :: rest =>
      .and source carry :: AffineConjunction.chunksFrom (carry + 1) rest

def affineConjunctionGateStream (frame : AffineConjunctionFrame) :
    List CircuitSym :=
  ([CircuitGate.const true] ++
    AffineConjunction.chunksFrom frame.start frame.wires.reverse).flatMap
      encodeCircuitGate
```

- [x] **Step 3: Align the tail-first semantic trace**

Prove a carry lemma for `chunksFrom` over append and a wire-index lemma
`(conjunctionGateTrace start wires).wire = start + wires.length`.  Induct on
`wires` to obtain:

```lean
theorem affineConjunctionGateStream_eq_trace
    (frame : AffineConjunctionFrame) :
    affineConjunctionGateStream frame =
      (CircuitBuilder.conjunctionGateTrace frame.start frame.wires).gates.flatMap
        encodeCircuitGate
```

The cons case must rewrite `List.reverse_cons`, use the append carry lemma, and
identify the last gate as `.and wire (start + rest.length)`.

- [x] **Step 4: Run the semantic checks and commit**

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
lake env lean Tests/Chapter_34_PolyBuilder_Conjunction.lean
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean \
  Tests/Chapter_34_PolyBuilder_Conjunction.lean
git commit -m "feat(ch34): frame tail-first conjunction streams"
```

### Task 4: Execute the variable-length conjunction frame

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean`
- Test: `Tests/Chapter_34_PolyBuilder_Conjunction.lean`

- [x] **Step 1: Define grouped outer labels and the fixed program**

Use grouped labels to avoid the prior derived-`Fintype` depth failure:

```lean
inductive AffineConjunctionLoadLabel
  | loadStart | incStart | seed | loadWire | incWire | clearCarry
deriving DecidableEq, Fintype

inductive AffineConjunctionLabel
  | load (phase : AffineConjunctionLoadLabel)
  | core (label : SequentialExactlyOneLabel)
  | finish | invalid
deriving DecidableEq, Fintype
```

The program behavior is fixed as follows:

```text
loadStart: tick -> incStart; separator -> seed; frameEnd -> invalid
incStart: increment counter₁ and return to loadStart
seed: push constTrueMark and enter loadWire
loadWire: tick -> incWire; separator -> core conjunction.push;
          frameEnd -> clearCarry; empty -> invalid
incWire: increment counter₃ and return to loadWire
core conjunction.done: jump to loadWire
other core labels: lift the shared instruction
clearCarry: decrement counter₁ until zero, then finish
finish/invalid: halt
```

- [x] **Step 2: Add public configuration surfaces**

Define fieldwise `affineConjunctionCfg`, clean `affineConjunctionLoopCfg`,
wire-loop configuration parameterized by the live carry, and
`affineConjunctionFinishCfg tail output` with `buffer₁ = some .frameEnd` and
all stacks/counters empty.

- [x] **Step 3: Transport the AND kernel**

Lift unit scratch symbols to `UnaryFrameSym.tick`, preserving the framed input
tail.  Prove instruction simulation for every kernel instruction except
`.conjunction .done`.  Transport the exact iterations only up to the source
done label, using the same no-return argument already established in
`Stack.lean` for `.finish`; do not use the whole-program lift theorem across
the redirected exit.

- [x] **Step 4: Prove exact loaders and one-wire execution**

Prove:

- raw start scan in `2 * start + 1` steps, followed by separator-buffer
  clearing and the true seed, for `2 * start + 3` total steps;
- raw wire scan in `2 * source + 1` steps, followed by separator-buffer
  clearing, for `2 * source + 2` loader steps while preserving the carry;
- one encoded source returns to `loadWire` with carry incremented, exact gate
  output prepended, and cost
  `2 * source + 2 + affineAndRevCoreSteps carry source + 1`, equivalently
  `8 * source + 5 * carry + 14`.

- [x] **Step 5: Prove the contextual and standalone runs**

Define the fold steps recursively over `frame.wires.reverse`.  Induct over that
processing list, compose `runOne`, then consume `frameEnd` and clear the final
carry.  Expose:

```lean
affineConjunction_runToFinish frame tail output
affineConjunction_run frame output
```

The contextual result must preserve `tail`; the standalone result must be
`haltCfg` with exact output
`(affineConjunctionGateStream frame).reverse ++ output`.

- [x] **Step 6: Run exact-run checks and commit**

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
lake env lean Tests/Chapter_34_PolyBuilder_Conjunction.lean
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean \
  Tests/Chapter_34_PolyBuilder_Conjunction.lean
git commit -m "feat(ch34): execute runtime conjunction frames"
```

### Task 5: Prove the explicit quadratic envelope

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean`
- Test: `Tests/Chapter_34_PolyBuilder_Conjunction.lean`

- [x] **Step 1: Bound the recursive fold**

Use the exact per-wire identity
`8 * source + 5 * carry + 14`.  The originally proposed measure
`carry + encodedLength + 1` is a known failed route: for a zero-valued source,
consuming its one-symbol block and incrementing the carry leaves that measure
unchanged, so it cannot pay the positive per-wire cost.  The accepted proof
uses the weighted measure
`carry + 2 * encodedLength + 1` and proves by induction:

```lean
affineConjunctionFoldSteps carry sources ≤
  20 * (carry + 2 *
    (encodeAffineConjunctionSources sources).length + 1) ^ 2 + 1
```

In the cons case, the measure drops by exactly `2 * source + 1`.  Expand the
square difference and separately bound its carry and source contributions;
this avoids asking nonlinear automation to discover the mixed-product
nonnegativity facts implicitly.

- [x] **Step 2: Lift to the public frame bound**

Combine the start loader, true seed, recursive fold, final carry cleanup, and
standalone halt.  Rewrite `encodeAffineConjunctionFrame_length` and prove:

```lean
theorem affineConjunctionRev_steps_le (frame : AffineConjunctionFrame) :
  affineConjunctionRevSteps frame ≤
    1000 * (encodeAffineConjunctionFrame frame).length ^ 2 + 2
```

- [x] **Step 3: Verify axiom output and commit**

```bash
lake env lean Tests/Chapter_34_PolyBuilder_Conjunction.lean
git diff --check
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/PolyBuilder/Conjunction.lean \
  Tests/Chapter_34_PolyBuilder_Conjunction.lean
git commit -m "feat(ch34): bound runtime conjunction frames"
```

Expected axiom output: only `propext`, `Classical.choice`, and `Quot.sound`.

### Task 6: Instantiate the arithmetic final conjunction

**Files:**
- Modify: `CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityStack.lean`
- Modify: `Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean`
- Modify: `docs/proof-audits/2026-08-14-ch34-generator-attack.md`

- [x] **Step 1: Import the generic conjunction controller**

Add the `PolyBuilder.Conjunction` import to `GeneratorValidityStack.lean`.

- [x] **Step 2: Define the real arithmetic frame**

```lean
noncomputable def arithmeticValidityFinalConjunctionFrame
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    AffineConjunctionFrame :=
  { start := arithmeticValidityFinalStart tm H start
    wires := arithmeticValidityConstraintWires tm H start rowBase }
```

- [x] **Step 3: Prove exact stream agreement**

Unfold the frame and generic stream, then rewrite with
`affineConjunctionGateStream_eq_trace` and
`arithmeticValidityFinalConjunctionGateStream_eq_semantic`:

```lean
theorem arithmeticValidityFinalConjunctionGateStream_eq_framed
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
  affineConjunctionGateStream
      (arithmeticValidityFinalConjunctionFrame tm H start rowBase) =
    arithmeticValidityFinalConjunctionGateStream tm H start rowBase
```

- [x] **Step 4: Add the exact run and inherited bound**

Specialize `affineConjunction_run` and `affineConjunctionRev_steps_le`, using
the stream equality to expose the established arithmetic byte stream.  Name
the results exactly:

```lean
arithmeticValidityFinalConjunctionRev_runFrom
arithmeticValidityFinalConjunctionRev_steps_le
```

- [x] **Step 5: Update tests and audit**

Turn the arithmetic RED checks green.  Record that the final conjunction now
has a concrete fixed-controller execution, while the remaining gap is the
linker from the already-complete stack family into this redirectable
conjunction controller.  Retain all six rejected routes from the design.

- [x] **Step 6: Run the focused acceptance gate**

Run only:

```bash
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactlyOne
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Conjunction
lake build CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityStack
lake env lean Tests/Chapter_34_PolyBuilder_Conjunction.lean
lake env lean Tests/Chapter_34_PolyBuilder_Stack.lean
lake env lean Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean
```

Then run the changed-file placeholder scan and `git diff --check`.  Do not run
a full-repository build.

- [x] **Step 7: Commit the arithmetic milestone**

```bash
git add CLRSLean/Chapter_34/Section_34_4_NP_Completeness_Proofs/CookLevin/Circuitization/GeneratorValidityStack.lean \
  Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean \
  docs/proof-audits/2026-08-14-ch34-generator-attack.md \
  docs/superpowers/plans/2026-08-15-ch34-affine-conjunction.md
git commit -m "feat(ch34): execute final validity conjunction"
```

## Final acceptance

- [x] The controller label type is finite and contains no runtime naturals.
- [x] The runtime encoding is unambiguous for zero-valued wires.
- [x] Tail-first output is byte-for-byte the semantic conjunction trace.
- [x] Both redirectable-finish and standalone-halt exact runs are public.
- [x] The standalone run has the explicit `1000 * |encoding|^2 + 2` bound.
- [x] The real arithmetic final-conjunction stream has an exact run and bound.
- [x] Focused builds/tests pass with only standard logical axioms.
- [x] No full-repository build is used.
