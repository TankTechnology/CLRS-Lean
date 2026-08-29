# 3D-IC Balanced Window Load Design

Date: 2026-08-29

Status: approved follow-up to the route-A literature audit

## Goal

Strengthen affine window surjectivity into a quantitative box-defect
certificate: in every translated `M x M` window, the number of bumps assigned
to a fixed color is either `floor(M^2 / K)` or `ceil(M^2 / K)`.

## Scope

This increment covers only the current construction
`affineChainColor M K i j = (i + M*j) % K`. It does not generalize the affine
coefficients, introduce strip defects, or model DART spares and muxes.

## Architecture

Create `WindowLoad.lean` rather than extending `WindowDiversity.lean`.
The new module will:

1. enumerate an `M x M` translated window by the canonical index
   `t < M^2`, with coordinates `(p + t % M, q + t / M)`;
2. prove the enumeration stays inside the window, is injective, and reaches
   every offset;
3. define `windowColorCount` using `Nat.count` over the canonical indices;
4. reduce each enumerated color to the modular progression
   `(p + M*q + t) % K`;
5. use the exact Mathlib residue-count theorem to prove the floor/ceiling
   alternative and a direct ceiling upper bound.

This representation avoids a large `Finset.product` proof while retaining a
proved bijection between indices and actual window offsets.

## Public interface

- `windowIndexPoint`: canonical index-to-bump map.
- `windowIndexPoint_inWindow`: every valid index lies in the translated
  window.
- `windowIndexPoint_injective`: valid indices name distinct bumps.
- `exists_windowIndexPoint_eq`: every translated-window offset has an index.
- `windowColorCount`: number of actual window bumps assigned color `c` through
  the proved canonical enumeration.
- `affineChainColor_window_count_eq_floor_or_ceil`: exact two-valued count.
- `affineChainColor_window_load_le_ceilDiv`: direct box-defect load bound.

The count theorem assumes `0 < K`, `K <= M^2`, and `c < K`. These hypotheses
also force `0 < M`, which is required for quotient/remainder enumeration.

## Verification

Development uses only the new module and its interface test. Final acceptance
requires:

- the new interface test;
- the ThreeDIC trust audit with the new upper-bound theorem;
- all existing ThreeDIC interface tests;
- placeholder and axiom scans over the research modules;
- `scripts/check_repository.py` and `git diff --check`.

