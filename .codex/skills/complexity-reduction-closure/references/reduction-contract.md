# Reduction Contract

Use this reference to shape the public reduction theorem and its closure
ledger.

## Contract

For `f : List Γ₁ → List Γ₂`, source language `A`, and target language `B`,
track these obligations independently:

| Layer | Typical Lean evidence |
| --- | --- |
| Typed semantics | `TypedYes source ↔ TypedYes (typedMap source)` |
| Total raw map | `f` returns a target string for every input string |
| Raw semantics | `x ∈ A ↔ f x ∈ B` |
| Output size | `(f x).length ≤ p.eval x.length` |
| Exact computation | a fixed machine returns exactly `f x` |
| Runtime | machine steps are at most `q.eval x.length` |
| Public packaging | `PolyTimeReducible A B` |

An output-length theorem is not evidence for exact computation or runtime.

## Truth Source

Prefer a strong exact theorem:

```lean
theorem typedMap_correct (I : SourceInstance) :
    SourceYes I ↔ TargetYes (typedMap I) := by
  ...
```

Split its proof into named soundness and completeness lemmas when the two
directions use different constructions.  Derive one-way wrappers only when
downstream code repeatedly needs them.

The raw theorem should quantify over all strings:

```lean
theorem rawMap_mem_iff (input : List SourceSym) :
    rawMap input ∈ TargetLanguage ↔ input ∈ SourceLanguage := by
  ...
```

Orient the final theorem to match the repository's reduction constructor.

## Hardness and Completeness

After proving `PolyTimeReducible A B`, reuse hardness transport:

```lean
theorem target_npHard : NPHard B :=
  NPHard.of_reducible source_npHard source_reducible_to_target
```

Keep NP membership independent:

```lean
theorem target_npComplete : NPComplete B :=
  ⟨target_polyTimeVerifiable, target_npHard⟩
```

Do not infer target NP membership from hardness or from the reduction.

## Ledger Discipline

For every row, record a theorem name or say `open`.  The first missing bridge
is the earliest open row in dependency order, not necessarily the most
interesting final theorem.
