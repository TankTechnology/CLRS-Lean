# Semantic-to-Machine Closure

Use this reference after typed semantics, raw semantics, and the output grammar
are stable.

## Exact-Map Rule

The concrete machine must compute the exact raw map appearing in the membership
theorem.  Do not substitute a propositionally equivalent encoding without an
explicit equality or target-language equivalence bridge.

## Phase Contract

Split a long machine into phases.  Each phase should prove:

1. its entry-state and input-layout precondition;
2. an exact final configuration or exact output stream;
3. preservation of untouched tapes, suffixes, delimiters, and bounded stacks;
4. an exact step count or reusable upper bound;
5. a bound on newly emitted data.

Accumulator-based emitters often use reverse output.  Prove the canonical
reverse-run theorem locally, then normalize only at the public boundary.

## Composition Order

Compose phases only after their exact interfaces align:

```text
parse/normalize
  -> typed transformation
  -> serialize records
  -> finalize canonical output
  -> halt
```

Prefer a short assembly theorem using phase contracts over unfolding every
controller in the final proof.

## Script Caveat

A theorem of the form

```text
steps ≤ C * encodedScript.length^d + C
```

is intermediate.  Also prove:

- a fixed machine generates the script from the original input;
- script length is polynomial in original input length;
- generation plus interpretation remains polynomial.

Do not hide runtime-sized values in finite control.  Store them in explicit
counters, stacks, or tapes whose manipulation is included in the runtime
proof.

## File Boundaries

Use focused files for configuration, steps, exact runs, semantics, local
bounds, polynomial lifting, and public packaging.  Large arithmetic or routing
lemmas deserve separate files when they would otherwise force recompilation of
an unrelated proof layer.
