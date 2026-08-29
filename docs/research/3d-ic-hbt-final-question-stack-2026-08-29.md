# Final Question Stack: Certified 3D-IC Repair Chains

Date: 2026-08-29

Status: route A combinatorial core formally verified; not a claim that a
recognized open problem has been solved

## Headline question

For explicitly parameterized W2W line-shaped and clustered defects, can a
deterministic hybrid-bond repair-chain assignment simultaneously provide a
worst-case certificate on the number of failures charged to each chain and a
physical routing guarantee, while respecting the spare and mux constraints of
the DART architecture?

## Why this is the right main question

The question starts from DART's real motivation--line and cluster faults--but
replaces heuristic quality alone with a falsifiable certificate. Route A now
formally verifies perfect window dispersion, exact floor/ceiling-balanced
per-chain box load, finite-grid same-color bounded-hop connectivity, and the
exact modular ceiling bound for lattice-line load. These are certified
baselines. A paper contribution must still add nontrivial hardware-specific
strip load or routing guarantees and show that they predict actual
repairability, not merely rediscover modular coloring and interleaving facts.

## Supporting sub-questions

1. What is the sharpest maximum-hop, total-length, turn, or capacity guarantee
   compatible with perfect local color diversity on a finite bump grid?
2. Under identical defect distributions, spare ratios, and mux constraints,
   do those analytic certificates predict DART-model repairability and reduce
   synthesis runtime or variance?

## Falsifiable hypotheses

- **H1 -- certified load:** Translated `M x M` boxes now have the proved bound
  `ceil(M^2/K)`, and the lattice-line subcase has the proved bound
  `ceil(L / (K / gcd(K, a + M*b)))`. The remaining hypothesis is that a tight
  strip or multi-direction extension is asymptotically or numerically better
  than regular localized chains at the same spare ratio.
- **H2 -- routability:** The same construction admits a chain ordering with a
  nontrivial, physically meaningful bound on maximum hop and total route length.
  The elementary window-connectivity radius and the classical generic `3R`
  Hamiltonian lift are baselines, not the target contribution.
- **H3 -- predictive validity:** Under a faithful reproduction of DART's fault
  and repair semantics, the load certificate predicts success/failure and the
  deterministic construction is competitive in repairability while materially
  reducing optimization time and run-to-run variance.
- **H4 -- novelty gate:** The load and routing theorem is not a direct instance
  of existing polychromatic-coloring, burst-error-code, interleaving, or robust
  assignment results after translating the hardware constraints faithfully.

Any failure of H1--H3 is informative and should narrow or stop the paper claim.
H4 is a mandatory literature gate rather than an empirical hypothesis.

## Paper skeleton

- **Introduction:** hybrid-bond line/cluster defects; why heuristic chain
  formation lacks worst-case guarantees; precise claim boundary.
- **Model:** DART-compatible bump grid, chains, spares, mux/reroute semantics,
  defect families, and physical routing metrics.
- **Result 1 -- exact baseline:** formally verified perfect window dispersion
  and floor/ceiling-balanced window load; explicit acknowledgement that the
  construction belongs to known polychromatic/tiling territory.
- **Result 2 -- certificate:** worst-case per-chain load bounds for the frozen
  line/cluster family, including lower bounds or adversarial tight examples.
- **Result 3 -- routing:** sharp bottleneck/length/capacity guarantee and a
  deterministic synthesis algorithm.
- **Result 4 -- evaluation:** identical-model comparison against DART simulated
  annealing and regular repair chains across fault shape, spare ratio, and grid
  scale.
- **Formal artifact:** Lean statements for the baseline and theorem-backed load
  and routing results, separated from empirical simulator assumptions.
- **Discussion:** what is certified, what is model-dependent, collision with
  coding/tiling prior art, and limits of the fault physics.

## Publication gate

The expanded route A proof package is still not enough by itself for a paper:
its box and line-load theorems are elementary modular counting until a
hardware-specific strengthening shows otherwise, and its routing result is
connectivity rather than a simple physical chain. A credible short EDA paper
needs a stronger strip/multi-direction or routing result plus a faithful
evaluation.
A stronger DATE/ISPD/ICCAD/TCAD submission needs those results together with
repairability evidence. A formal-methods venue additionally needs a larger
verified refinement or executable routing artifact.
