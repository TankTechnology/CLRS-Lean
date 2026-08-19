# Chapter 34 validity-row halted operands implementation plan

## Goal

Compile the actual `haltedStart`, `haltedLeft`, and `haltedRight` operands of
every Cook--Levin validity row from the raw verifier input with one fixed
polynomial-time TM2, and prove byte-for-byte agreement with the runtime row
frames.

## Tasks

1. Add a fixed controller for three simultaneous affine unary progressions.
   Prove its exact structured run, cleared-scratch postcondition, and a
   polynomial runtime bound.
2. Compose the controller after the exact-polynomial unary-frame-family
   compiler, producing all three row-major values directly from the raw word.
3. Instantiate the seven exact polynomials for validity-row halted operands
   and prove row-by-row equality with `verifierValidityRowFramesByLength`.
4. Export the concrete computability theorem, add interface and axiom tests,
   register the modules, and run the Chapter 34 acceptance suite.

## Acceptance

- The generic and exact-polynomial triple-controller tests compile.
- The Cook--Levin specialization exposes exact field and byte-stream equality.
- A concrete `TM2ComputableInPolyTime id id` theorem is exported.
- Chapter 34, status, progress, and literate checks pass without introducing
  `sorry`, `admit`, custom axioms, or unsafe declarations.
