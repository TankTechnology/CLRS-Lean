# Balanced Affine Co-Design Research Contract

## Phenomenon

- **One-sentence phenomenon:** A divisibility-and-unit condition gives a
  finite family of affine bump colorings that is exactly balanced in every
  translated target window while retaining coefficient freedom for
  direction-sensitive defect certificates.
- **Why it matters:** The existing optimizer is global for its certificate but
  does not guarantee window balance; this result restricts optimization to a
  formally admissible EDA-facing family.
- **Falsifier:** A translated `M x M` window, valid color, and coefficient pair
  satisfying `0 < K`, `K ∣ M`, and the coprimality condition whose exact count
  differs from `(M*M)/K`.

## Unit and universe

- **Primary unit:** one translated window, one requested color, and one affine
  coefficient pair.
- **Universe:** natural `M`, positive `K`, translations and offsets in `Nat`,
  and coefficients in the canonical residue domain modulo `K`.
- **Inclusion:** `K ∣ M`, `c < K`, and at least one coefficient coprime to `K`.
- **Exclusion:** arbitrary window sizes, non-affine colorings, and coefficients
  outside the certified sufficient condition.
- **Denominator:** exactly `M*M` physical bump offsets per full window.
- **Known missingness:** no classification of all balanced coefficients and no
  empirical DART data in this theorem phase.

## Terms

| Term | Definition | Do not confuse with |
|---|---|---|
| exact window balance | every color occurs `(M*M)/K` times in every translated full window | mere color coverage |
| balanced candidate | a canonical residue pair with `Coprime K alpha` or `Coprime K beta` | every possible balanced affine pair |
| score minimizer | least `affineDefectFamilyScore` inside the certified candidate set | least measured routing or repair cost |
| certificate | proved upper bound derived from line and cross-row periods | tight physical failure load |

## Research-question map

| RQ | Question | Unit | Evidence | Allowed claim |
|---|---|---|---|---|
| RQ1 | Which easy-to-check affine coefficients guarantee exact full-window balance when `K ∣ M`? | coefficient/window/color | `AffineWindowLoad.lean` | the coprime-coordinate condition is sufficient |
| RQ2 | Can the directional certificate be optimized without leaving that family? | candidate set/defect family | `BalancedAffineCodesign.lean` | a finite exact certificate minimizer exists in the certified family |

## Canonical artifacts

| Artifact | Purpose | Hand-edited? |
|---|---|---|
| `CLRSLean/Research/ThreeDIC/AffineWindowLoad.lean` | exact window-count theorem | yes, kernel checked |
| `CLRSLean/Research/ThreeDIC/BalancedAffineCodesign.lean` | admissible finite minimization | yes, kernel checked |
| `Tests/Research_ThreeDIC_*Interface.lean` | freeze public theorem applications | yes |
| `Tests/Research_ThreeDIC_Trust.lean` | audit theorem assumptions | yes |

## Claim ledger

| Claim | Status | Evidence | Caveat | Forbidden wording |
|---|---|---|---|---|
| coprime-coordinate pairs are exactly window balanced when `K ∣ M` | supported | `affineGridColor_window_count_eq_of_coprime_coefficient` | sufficient condition only | complete classification |
| a balanced-family score minimizer exists | supported | `exists_balancedAffineCoefficients_minimizer` | optimizes the upper certificate inside the certified family | globally optimal repair architecture |
| the result improves practical DART yield | unsupported | none | requires a model and experiments | demonstrated yield improvement |

## Open risks

- The verified modular-permutation proof establishes the sufficient family but
  does not characterize all coefficient pairs with exact or near-exact load.
- The candidate family may be conservative for composite `K`.
- Tightness, arbitrary `M`, physical routing, spare/mux semantics, and repair
  success remain separate research gates.
