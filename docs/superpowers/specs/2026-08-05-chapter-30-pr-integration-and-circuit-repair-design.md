# Chapter 30 PR Integration And Circuit Repair Design

## Goal

Replace the stale, conflicting history behind Chapter 30 PR #154 with a clean
integration on the current `origin/main`, and close the semantic gap between
the parallel FFT network's evaluated circuit and its size/depth accounting.

The result preserves the already proved Chapter 30.1--30.3 mathematical core,
while making the parallel-network theorem genuinely about the gates that are
evaluated.

## Scope Boundary

Included:

- clean migration of Chapter 30 source, tests, designs, plans, and audits;
- integration with the current Chapters 27--29 and 31 metadata on `main`;
- explicit logical butterfly gates and their evaluation;
- recursive stage-circuit syntax matching the verified `fftStage` semantics;
- exact gate count and depth derived from that syntax;
- all nine Chapter 30 interface and closure tests;
- repository, progress, navigation, placeholder, axiom, and full Lean build
  checks.

Excluded:

- chapter-end exercises;
- Problems 30-1 through 30-6;
- floating-point error analysis;
- mutable-array, in-place, RAM, cache, SIMD, GPU, and scheduler refinements;
- NTT specialization and external code generation; and
- website generation, rendering inspection, preparation, or deployment.

The excluded exercises and Problems remain outside the reviewed theorem-group
denominator and do not prevent Chapter 30's main-text status from being
`proved`.

## Clean Integration Strategy

The old branch predates the completed Chapters 28, 29, and 31 and contains
unrelated historical changes.  It will not be merged or rebased commit by
commit.  A fresh branch starts at the latest `origin/main` and imports only:

- `CLRSLean/Chapter_30.lean` and `CLRSLean/Chapter_30/**`;
- `Tests/Chapter_30_*.lean`;
- Chapter 30 plans, designs, and proof audits; and
- the already approved proof-work-versus-publishing policy wording.

Shared owners (`CLRSLean.lean`, status/progress files, README, proof map,
navigation index, status board, and `literate.toml`) are edited against their
current `main` versions.  Generated progress files are regenerated from the
CSV instead of copied from the stale branch.

## Circuit Semantic Core

### Individual butterfly gate

`FFTButterflyGate K` stores the fixed twiddle constant of one logical
butterfly.  Its evaluator consumes two ring values and returns the pair

```text
let product = twiddle * v
(u + product, u - product).
```

This explicit sharing is the primitive semantic object counted as one
butterfly and expanded to one multiplication plus two addition/subtraction
gates.

### Butterfly-layer circuit

`ButterflyLayerCircuit K k` contains an actual gate family indexed by
`Fin (2 ^ k)`.  Its evaluator maps those gates over the lower and upper input
halves and joins the two output halves.  The canonical layer uses gate `j`
with twiddle `omega ^ j`.

The theorem `canonicalButterflyLayerCircuit_eval` proves that evaluating this
gate family is exactly the already verified `butterflyLayer omega`.  Thus the
gate enumeration and the algebraic butterfly implementation are connected by
a kernel-checked theorem.

### Recursive global-stage circuit

The existing `fftStage` definition recursively applies a final butterfly layer
or splits a nonfinal stage across two contiguous halves.  The circuit syntax
mirrors that structure:

```text
FFTStageCircuit.butterfly layer
FFTStageCircuit.parallel lowerCircuit upperCircuit
```

`fftStageCircuit omega s` builds the canonical circuit for stage `s`.  Its
evaluator recursively evaluates the stored syntax; it never delegates directly
to `fftStage`.  The bridge theorem

```text
fftStageCircuit_eval omega a s :
  (fftStageCircuit omega s).eval a = fftStage omega a s
```

is proved by induction on the exponent and the final/nonfinal stage split.

Circuit butterfly count is structural: a butterfly layer contributes the
cardinality of its actual gate family and a parallel node sums its children.
Stage depth is structural: a butterfly layer has depth one and a parallel node
takes the maximum child depth.  Canonical-stage theorems prove count
`2 ^ (k - 1)` and depth one.

### Layered FFT network

`FFTLayer` retains its root/stage metadata but also owns its
`FFTStageCircuit`.  `FFTLayer.eval`, `FFTLayer.butterflyCount`, and
`FFTLayer.butterflyDepth` are all projections or computations on that same
circuit.

`FFTNetwork.evalPrefix` evaluates each stored layer circuit.  Network size is
the sum of stored circuit counts, and network depth is the sum of stored
circuit depths.  Therefore the canonical equalities

- evaluation equals `iterativeRadix2FFT`;
- butterfly count equals `k * 2 ^ (k - 1)`;
- butterfly depth equals `k`;
- primitive gate count equals `3 * k * 2 ^ (k - 1)`; and
- primitive depth equals `2 * k`

are all properties of the evaluated syntax rather than unrelated formulas.
Bit reversal remains wiring and contributes no arithmetic gate.

## Testing Strategy

The existing parallel FFT interface test is first extended with checks for the
gate, layer-circuit, stage-circuit, evaluation bridge, and structural
count/depth theorems.  It must fail because those declarations do not exist.
Only after that RED result are production declarations added.

After GREEN, the test also keeps the existing concrete `k = 3` size/depth
examples.  The Milestone 2 closure test prints axioms for the repaired headline
theorems.  No `sorry`, `admit`, project axiom, or placeholder implementation is
permitted.

## Completion Criteria

Completion requires fresh evidence that:

1. all nine Chapter 30 tests compile;
2. Chapter 30 placeholder scans are empty;
3. closure axiom output contains only accepted foundational axioms;
4. progress CSV, generated dashboard, README, status, proof map, and navigation
   metadata agree;
5. repository and site-configuration checks pass;
6. `lake build CLRSLean` passes; and
7. the clean branch contains no unrelated changes from the stale PR history.

`lake build :literateHtml` is deliberately absent because this is proof and PR
repair work, not a publishing task.
