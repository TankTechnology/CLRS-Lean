# Balanced Affine Co-Design Certificate Design

**Date:** 2026-08-30

**Status:** implemented, verified, and independently reviewed

## Goal

Close the main admissibility gap in the current affine direction co-design
theory.  For the coloring

```text
(alpha * i + beta * j + gamma) mod K,
```

prove a nontrivial sufficient condition under which every translated `M x M`
window has exactly the same load for every color, then minimize the existing
direction-sensitive strip certificate over that certified balanced family.

## Mathematical scope

Assume `0 < K` and `K ∣ M`.  If either `alpha` or `beta` is coprime to `K`,
then every color `c < K` occurs exactly

```text
(M * M) / K
```

times in every translated `M x M` window.  The proof is row-wise when
`alpha` is coprime and column-wise when `beta` is coprime: a block of `M`
consecutive affine steps contains each residue exactly `M / K` times because
`K ∣ M` and multiplication by a unit permutes residues modulo `K`.

This is a sufficient family, not a classification of all balanced affine
colorings.  The divisibility assumption is part of the public theorem and is
not hidden in a definition.

## Architecture

Keep the increment in two focused production modules.

### `AffineWindowLoad.lean`

This module owns the quantitative window model and the balance proof.

- `affineWindowColorCount` counts offset pairs in `Finset.range M ×
  Finset.range M` whose translated physical bump has color `c`.
- A private one-dimensional lemma proves exact residue counts over a block of
  length divisible by `K` for a coprime affine step.
- `affineGridColor_window_count_eq_of_coprime_alpha` exposes the row-wise
  theorem.
- `affineGridColor_window_count_eq_of_coprime_beta` exposes the symmetric
  column-wise theorem.
- `affineGridColor_window_count_eq_of_coprime_coefficient` is the main direct
  wrapper for the disjunctive admissibility condition.

The public count is defined over grid offsets rather than over a list with
possible duplicates, so its cardinality is an actual bump count.  Translation
by `(p,q)` is injective on natural-coordinate pairs.

### `BalancedAffineCodesign.lean`

This module connects admissibility to the existing direction-sensitive score.

- `balancedAffineCoefficientCandidates K` filters the canonical `K × K`
  residue domain to pairs for which `alpha` or `beta` is coprime to `K`.
- A membership theorem makes both the residue bounds and the coprimality
  condition available to downstream proofs.
- The candidate set is nonempty for every positive `K`, including `K = 1`.
- Every candidate satisfies the exact translated-window balance theorem when
  `K ∣ M`.
- An exact minimizer of `affineDefectFamilyScore` exists in the nonempty
  balanced candidate set.
- A headline theorem bundles the selected coefficient's window-balance
  certificate with its score minimality among all certified balanced
  candidates.

The minimization reuses `exists_affineCoefficients_minimizer`; no new search
algorithm or asymptotic optimization claim is introduced.

## Public theorem shape

The core theorem family will have the following semantic shape; exact binder
ordering may follow nearby repository style:

```lean
theorem affineGridColor_window_count_eq_of_coprime_coefficient
    (M K alpha beta gamma p q c : Nat)
    (hK : 0 < K) (hKM : K ∣ M) (hc : c < K)
    (hunit : Nat.Coprime K alpha ∨ Nat.Coprime K beta) :
    affineWindowColorCount M K alpha beta gamma p q c =
      (M * M) / K
```

The co-design headline will expose:

```lean
theorem exists_balancedAffineCoefficients_minimizer
    (M K : Nat) (family : Finset StripDefectShape)
    (hK : 0 < K) (hKM : K ∣ M) :
    ∃ coeff ∈ balancedAffineCoefficientCandidates K,
      (∀ gamma p q c, c < K ->
        affineWindowColorCount M K coeff.alpha coeff.beta gamma p q c =
          (M * M) / K) ∧
      (∀ other ∈ balancedAffineCoefficientCandidates K,
        affineDefectFamilyScore K coeff family ≤
          affineDefectFamilyScore K other family)
```

Separate membership, balance, and minimization theorems remain the reusable
truth sources; the bundled theorem is an EDA-facing wrapper.

## Proof strategy

1. Freeze the public applications in dedicated interface tests and verify the
   expected missing-module failure.
2. Prove a one-period modular permutation count for a coprime multiplier.
3. Extend the result from one period to `M` steps using `K ∣ M`.
4. Sum the row counts over `M` rows; obtain the column theorem by the symmetric
   argument rather than by an unproved coordinate-equivalence assertion.
5. Filter the already finite canonical residue domain and prove nonemptiness.
6. Reuse finite-image minimization and combine it with the balance theorem.

Arithmetic involving division, modulo, and coprimality will be isolated in
small private lemmas.  Public statements will not expose proof-specific
quotient encodings.

## Testing and verification

Create separate interface tests for both new modules.  Tests freeze full
theorem applications, not only bare names, and include:

- a concrete `M = 4`, `K = 2` exact-count evaluation;
- a coprime-`alpha` case and a coprime-`beta` case;
- translated windows and nonzero `gamma`;
- the `K = 1` candidate-set boundary;
- a coefficient excluded because neither coefficient is coprime to `K`;
- a concrete balanced-candidate minimizer application;
- an empty defect family, whose score remains zero.

The ThreeDIC trust test will assert the core exact-count theorem and the
balanced minimizer theorem.  Final acceptance requires focused module and
interface builds, all ThreeDIC interface/trust tests, full `lake build
CLRSLean`, the repository checker, a declaration-aware placeholder scan, and
`git diff --check`.

## Claim boundary

Allowed after completion:

- a broad, coefficient-sensitive affine family is formally certified to have
  exact translated-window balance in the regime `K ∣ M`;
- the existing directional strip score has an exact minimizer inside that
  certified balanced family;
- the theorem is machine checked and the finite feasible domain is explicit.

Not allowed:

- this condition characterizes every balanced affine coloring;
- the selected coefficient minimizes actual failure load rather than the
  proved upper certificate;
- the certificate is tight;
- the result proves spare reachability, mux feasibility, routing quality, or
  DART repair success;
- the result by itself resolves a traditional EDA open problem.
