# Chapter 4 Executable Maximum-Subarray Runtime Design

## Goal

Close PR #87's semantic gap by proving a `Θ(n log n)` bound for a cost model
that is attached to the executable divide-and-conquer maximum-subarray
algorithm, rather than for a standalone recurrence.

## Algorithm boundary

The implementation will use:

- a one-pass maximum nonempty-prefix selector;
- maximum suffix selection through the corresponding reverse traversal;
- a linear crossing-subarray selector built from those two scans;
- midpoint recursion whose terminal inputs have length at most one; and
- a costed execution returning the algorithm result together with an abstract
  control-step count.

The existing exhaustive subarray enumerators remain useful as specifications
and reference implementations, but the runtime theorem will not charge their
execution as if it were linear.

## Required bridges

The public proof surface must establish all of the following:

1. the linear crossing selector returns an optimal crossing subarray;
2. erasing the cost component recovers the executable divide-and-conquer
   result;
3. the executable result satisfies `IsMaxSubarrayResult`;
4. the measured cost depends only on input length and satisfies the actual
   midpoint recurrence with subproblem sizes `n / 2` and `n - n / 2`; and
5. that all-input cost is `Θ(n log n)`.

For odd inputs the two recursive sizes differ.  The asymptotic proof must
therefore use a proved comparison/sandwich argument (or an equivalent direct
proof), not silently replace the recurrence by two floor-sized calls.

## Cost-model claim

The theorem concerns abstract control steps for recursive frames, scan
transitions, and constant-size candidate choices.  It does not claim a full
RAM refinement for Lean list allocation, copying, indexing, or garbage
collection.  Documentation and theorem names must state this boundary.

## Acceptance criteria

- A Chapter 4 interface test fixes the executable/cost/correctness API.
- No `sorry`, `admit`, or new axioms are introduced.
- Chapter 4 source, repository checks, the full `CLRSLean` build, and the
  literate HTML build pass.
- The chapter guide, proof map, progress CSV/dashboard, and status summary no
  longer describe this executable runtime layer as missing.
- The repaired branch is pushed to PR #87 and its CI is observed to completion.
