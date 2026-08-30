# Affine Strip Tightness Research Contract

Date: 2026-08-30

Status: implemented and kernel-checked; independent final workflow review is
still pending at this commit

## Phenomenon

- **One-sentence phenomenon:** A full modular phase cell contains exactly one
  sample of every affine color, so complete nonoverlapping cells attain the
  existing phase-aware strip upper certificate.
- **Why it matters:** It distinguishes a genuinely sharp deterministic defect
  certificate from an upper bound that may contain avoidable slack.
- **Falsifier:** Parameters satisfying the four frozen hypotheses for which a
  valid color's distinct physical load differs from `(W/R)*(L/T)`.

## Unit and universe

- **Primary unit:** one valid color in one finite physical affine strip.
- **Universe:** natural affine coefficients, positive modulus `K`, natural
  lattice directions and base point, and finite widths and lengths.
- **Inclusion:** full color generation, complete row and along periods, and
  injective physical sampling.
- **Exclusion:** partial period boundaries, proper color cosets, and
  self-overlapping sampling.
- **Denominator:** `W*L` index samples; under the injectivity hypothesis this
  is also the number of distinct physical strip points.
- **Known missingness:** arbitrary phases at incomplete boundaries and
  multiplicity formulas for self-overlapping lattice strips.

## Terms

| Term | Definition | Do not confuse with |
|---|---|---|
| full color period | the along/across modular steps jointly generate all `K` residues | either step alone being coprime |
| period aligned | `R ∣ W` and `T ∣ L` | an arbitrary finite strip |
| sampling injective | distinct valid index pairs name distinct physical points | color-map injectivity |
| tight | equality with the existing phase-aware upper expression under the frozen hypotheses | universal optimality |

## RQ map

| RQ | Question | Unit | Denominator | Evidence | Allowed claim |
|---|---|---|---|---|---|
| RQ1 | Is the `R x T` affine phase map a permutation of all colors? | fundamental phase cell | `R*T = K` | `AffineStripTightnessCore.lean` | yes under the full-period condition |
| RQ2 | When does the physical upper certificate become equality? | color/strip | `W*L` unique points | `AffineStripTightness.lean` | equality for full, aligned, injective strips |

## Canonical artifacts

| Artifact | Purpose | Hand-edited? |
|---|---|---|
| `CLRSLean/Research/ThreeDIC/AffineStripTightnessCore.lean` | phase bijection and exact index count | yes, kernel checked after implementation |
| `CLRSLean/Research/ThreeDIC/AffineStripTightness.lean` | unique-physical-point equality and wrappers | yes, kernel checked after implementation |
| `Tests/Research_ThreeDIC_AffineStripTightness_Interface.lean` | freeze theorem use and boundaries | yes |
| `Tests/Research_ThreeDIC_Trust.lean` | audit assumptions of headline theorems | yes |

## Claim ledger

| Claim | Status | Evidence | Caveat | Forbidden wording |
|---|---|---|---|---|
| fundamental phase cells contain every color exactly once | support | `affineStripFundamentalColor_image_eq_range` under `hK : 0 < K` and `hFull : affineStripFullColorPeriod ...` | requires positive modulus and full color generation | arbitrary coefficients always cover all colors |
| aligned nonoverlapping strips attain the phase upper bound | support | `affineStripColor_load_eq_of_period_dvd` and `affineStripColor_load_eq_phase_periods` under `hK : 0 < K`, `hc : c < K`, `hFull : affineStripFullColorPeriod ...`, `hRW : R ∣ W`, `hTL : T ∣ L`, and `hInjective : affineStripSamplingInjective ...` | requires a valid color, full color generation, both period divisibilities, and physical sampling injectivity | the upper bound is universally tight |
| the result improves measured DART repairability | fail | none | requires hardware semantics and experiments | demonstrated yield improvement |

## Open risks

- The finite-cell image, aligned index count, and injective physical bridge are
  kernel-checked; an independent mathematical and claim-boundary review is
  still pending at this commit.
- The general physical theorem retains explicit sampling injectivity, while
  the axis-aligned wrappers discharge that hypothesis automatically.
- The no-overlap hypothesis must remain visible in the general headline and
  must not be hidden by documentation wording.
- Tight aligned load is not an end-to-end repairability or routing theorem.
