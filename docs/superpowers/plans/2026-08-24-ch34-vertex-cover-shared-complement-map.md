# Chapter 34 Shared Complement-Map Plan

**Goal:** Give the two total CLIQUE/VERTEX-COVER reductions one shared pure
function target before implementing their fixed polynomial-time machine.

**Why this layer matters:** Both reductions parse the same graph grammar,
perform the same well-formedness guard, and emit the same deterministic graph
complement.  They differ only in the fixed no-instance used on rejected raw
inputs.  Factoring that parameter now lets the machine proof reuse one
controller and specialize only its constant fallback branch.

**Boundary:** This milestone factors and characterizes the existing semantic
maps.  It does not yet claim TM2 computability or polynomial-time reducibility.

## Task 1: Shared semantic target

- [ ] Define `guardedGraphComplementMap fallback input` independently of either
  target language.
- [ ] Publish equations for successful well-formed decoding, ill-formed
  decoding, and parser failure.

## Task 2: Directional factorization

- [ ] Define both public raw maps as specializations of the shared function.
- [ ] Preserve the existing all-input membership theorems unchanged.

## Task 3: Stable machine-facing contract

- [ ] Add a focused interface test for the shared definition and both
  specialization equations.
- [ ] Build the focused test and Chapter 34 root, then audit axioms and
  placeholders.

## Task 4: Checkpoint

- [ ] Commit the proof layer and its public wiring as independently buildable
  checkpoints.
