# Adversarial Review of the 3D-IC Repair-Chain Questions

Date: 2026-08-29

Status: independent review required by the research-question audit

## Top three by realistic venue fit

1. **Q8: certified line/cluster-defect robustness.** This has the clearest 3D-IC
   identity and a plausible path to VTS/DFT/DATE if the certificate includes
   chain capacity, spares, and routing rather than only modular arithmetic.
2. **A strengthened Q4: exact dispersion plus physically faithful routing.**
   The current `O(M)` connectivity story is too elementary; a sharp bottleneck,
   total-length, turn, mux, or capacity result could make it substantial.
3. **Q7: same-model DART evaluation.** This is not a headline theorem, but a
   faithful repairability/runtime comparison is indispensable to an EDA paper.

## Weakest three

1. **Q2:** likely overlaps tiling, polychromatic coloring, and symbolic
   dynamics, while offering little EDA value without a routing consequence.
2. **Q9:** too broad for the first project and likely to rediscover robust
   assignment or facility-location results.
3. **Q10:** potentially valuable long term, but the current artifact lacks the
   RTL, refinement map, and routing implementation needed for an end-to-end
   formal-methods contribution.

## Per-question verdicts

- **Q1:** constructive baseline; high tractability, very high prior-art risk;
  keep only as a mechanism result.
- **Q2:** structural but currently unsupported and prior-art-heavy; defer/drop.
- **Q3:** tractable bridge lemma, but the connectivity bound is elementary;
  mechanism result only.
- **Q4:** structural and relevant, but currently collapses into Q1, elementary
  window connectivity, and classical graph-power results; support Q8 unless a
  sharper physical guarantee is found.
- **Q5:** potentially strong but currently ungrounded; freeze the objective
  before attempting hardness, and retain as future framing.
- **Q6:** useful organizer for results but too broad as a headline; support.
- **Q7:** empirically tractable only after a faithful DART reproduction; support.
- **Q8:** strongest headline candidate; audit multidimensional burst-error and
  interleaving prior art before claiming novelty.
- **Q9:** low current tractability and large adjacent literature; framing/drop.
- **Q10:** long-term formal-methods direction, not the first paper.

## Technical corrections from review

The affine square-window result is a direct special case of the established
connection between translational tilings and full-size polychromatic colorings.
It must not be presented as a solved open problem.

The earlier `2R` Hamiltonian-order argument was invalid: shortcutting a doubled
tree walk may jump over arbitrarily many tree edges. The classical safe result
is that the cube of a connected graph is Hamiltonian-connected, giving a
generic `3R` rather than `2R` baseline. See
[Chebikin](https://arxiv.org/abs/math/0307359) and
[Chartrand--Kapoor](https://nvlpubs.nist.gov/nistpubs/jres/73B/jresv73Bn1p47_A1b.pdf).

Q8 also needs a careful collision audit with multidimensional burst-error
coloring constructions, including
[Etzion--Yaakobi](https://arxiv.org/abs/0712.4096).

## Recommended final stack

- **Headline:** Can deterministic hybrid-bond repair-chain synthesis provide
  worst-case per-chain load certificates for parameterized line and cluster
  defects together with physical routing guarantees, under the same spare and
  mux constraints used by DART?
- **Supporting question 1:** What sharp routing guarantee can coexist with
  perfect local dispersion?
- **Supporting question 2:** Do the certificates predict repairability and
  overhead under a faithful DART/YAP+ fault model?
