# Chapter 34 Validity Tail Linker Plan

## Goal

Close the exact Cook--Levin row-validity suffix after halted/none-label
agreement by executing the already verified stack-family stream and final
conjunction in one fixed finite controller.

## Design

1. Extend the stack-family controller with an explicit outer `frameEnd`
   terminator.  This terminator is distinct from the `frameEnd` already owned
   by each complete stack frame, so adjacent zero-valued unary fields remain
   unambiguous.
2. Add a generic `AffineValidityTailFrame` containing a runtime stack-frame
   family and one runtime conjunction frame.
3. Define one combined program with disjoint stack and conjunction control
   labels.  The stack-family terminator enters a one-step cleanup bridge and
   then the unchanged conjunction entry.  Malformed stack and conjunction
   states remain rejecting halts.
4. Prove the exact independent-semantics run, exact emitted byte stream, and a
   quadratic bound in the combined explicit frame length.
5. Instantiate the generic controller at
   `arithmeticStackFrames` and
   `arithmeticValidityFinalConjunctionFrame`, then identify its output with
   `arithmeticValidityPostHaltedMatchGateStream`.

## Acceptance

- `Tests/Chapter_34_PolyBuilder_ValidityTail.lean` resolves the generic frame,
  program, exact run, and quadratic bound and prints their axioms.
- `Tests/Chapter_34_CookLevin_GeneratorValidityStack.lean` resolves the
  arithmetic instantiation and exact post-halted output theorem.
- Focused Lake builds for `PolyBuilder.ValidityTail` and
  `GeneratorValidityStack` pass.
- No `sorry`, `admit`, or project axiom is introduced; `git diff --check`
  passes.

## Rejected Alternatives

- Do not copy both mature controllers into a monolithic ad hoc row program.
- Do not treat the existing per-stack `frameEnd` as an outer-family boundary;
  zero-valued fields make separator-only families ambiguous.
- Do not halt between the stack family and conjunction and claim composition
  from two standalone output theorems.

