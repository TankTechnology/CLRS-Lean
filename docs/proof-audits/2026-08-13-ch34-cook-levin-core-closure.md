# Chapter 34 Cook--Levin Core Closure

Date: 2026-08-13

## Accepted Boundary

The whole-tableau circuit core is complete for a normalized
`VerifierWitness L` (named `W`) and public instance `x`:

- `verifierCircuit_wellFormed W x` proves the generated general circuit is
  structurally well formed.
- `verifierCircuit_satisfiable_iff W x` proves its satisfiability is equivalent
  to `x ∈ L`.
- `verifierCircuit_gate_count_le W x` supplies an explicit polynomial
  `verifierCircuitGateBound W` depending only on the fixed verifier and
  `x.length`.
- `verifierCircuit_input_count_le W x` and
  `verifierCircuit_encoding_length_le W x` bound the declared input arity and
  the complete unary circuit encoding by explicit fixed-verifier polynomials.
- `cookLevinMap W x` is the explicit function-level serialization;
  `cookLevinMap_mem_generalCircuitSAT_iff` proves exact language semantics and
  `cookLevinMap_length_le` proves its polynomial output-length bound.
- `generalCircuitVerifier` gives `GeneralCircuitSAT` an executable finite
  Boolean-certificate checker, and
  `mem_generalCircuitSAT_iff_exists_certificate` proves the exact certificate
  bound by the input-string length.

The construction allocates every tableau row, checks canonical row validity,
checks every adjacent stuttering transition, constrains the symbolic initial
input to a bounded certificate paired with the fixed public instance, fixes the
exact accepting `true` row, and conjoins all outputs.

## Known Failed or Rejected Routes

1. **Enumerating certificate contents.**  This makes the construction
   exponential and cannot establish the advertised polynomial gate bound.
   The accepted circuit enumerates only possible certificate lengths and
   recovers content from tableau input bits with `filterMap`.
2. **Leaving the initial input stack unconstrained.**  This admits tableaux for
   an unrelated input.  The accepted shape theorem fixes the public suffix and
   separator and proves exact equivalence with a bounded `(certificate, x)`
   encoding.
3. **Using a noncomputable membership-selected constant circuit.**  Although
   it could state a propositional equivalence, it is not a Cook--Levin
   construction and gives neither tableau semantics nor a polynomial-time
   reduction path.
4. **Adding separate certificate SAT inputs without a full linking proof.**
   This duplicates data and leaves an aliasing/equality gap.  The accepted
   construction uses the initial tableau stack itself as the certificate
   carrier.
5. **Claiming `PolyTimeReducible` from the size theorem alone.**  The project
   definition requires a concrete TM2 circuit generator.  The function-level
   map and output-size theorem do not by themselves supply that machine.  The
   concrete generator and final `GeneralCircuitSAT` NP-completeness wrappers
   remain a separate downstream boundary.
6. **Treating an executable Boolean function as a polynomial-time verifier.**
   The exact certificate checker closes the finite semantic layer, but the
   project definition of `PolyTimeVerifiable` still requires a concrete TM2
   plus its runtime proof.  No NP-membership wrapper is claimed from semantics
   alone.

## Focused Acceptance Checks

- Narrow builds for `Assembly.{Structure,Evaluation,Completeness,Soundness,
  Semantics,Bounds,EncodingBounds}`, `ReductionMap`, and
  `GeneralCircuit.Verification`, plus their dedicated tests.
- Public facade compilation through `CookLevin.Circuitization` and
  `CookLevin`.
- Axiom inspection of the new headline theorems; no `sorryAx` or
  project-defined axiom is permitted.
- Placeholder scan and `git diff --check`.

No full-repository build is part of this checkpoint.  Chapter 34 remains
partial because the explicit circuit-generator TM2, the final
polynomial-time certificate-checker TM2, the final `GeneralCircuitSAT`
NP-completeness wrappers, and Section 34.5 remain outside this accepted core.
