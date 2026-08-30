# Final Question Stack: Certified 3D-IC Repair Chains

Date: 2026-08-29

Status: route A combinatorial core, general affine strip certificates, exact
attainment on full-color-period, period-aligned, non-self-overlapping strips,
the canonical coefficient-domain optimizer, and constrained optimization over
a proved balanced affine family formally verified; this bounded exact result
alone is neither paper completion nor a claim that a recognized open problem
has been solved

Prior-art and claim basis: [route-A literature audit](./3d-ic-route-a-literature-audit-2026-08-29.md).

## Headline question

For explicitly parameterized W2W line-shaped and clustered defects, can a
deterministic hybrid-bond repair-chain assignment simultaneously provide a
worst-case certificate on the number of failures charged to each chain and a
physical routing guarantee, while respecting the spare and mux constraints of
the DART architecture?

## Why this is the right main question

For a lattice direction `v`, the formulas below use
`lineColorStep M v = v.1 + M*v.2`.

The question starts from DART's real motivation--line and cluster faults--but
replaces heuristic quality alone with a falsifiable certificate. Route A now
formally verifies perfect window dispersion, exact floor/ceiling-balanced
per-chain box load, finite-grid same-color bounded-hop connectivity, and the
exact modular ceiling bound for lattice-line load. It also certifies finite
physical-strip load first by the unique-point baseline `W * ceil(L/T)` and then
by the direction-sensitive upper bound `ceil(W/R) * ceil(L/T)`. The latter now
holds for arbitrary affine coefficients. When `0 < K` and `c < K`, it is
attained exactly when the two steps generate the full color period, `R ∣ W`,
`T ∣ L`, and physical strip sampling is injective; axis-aligned wrappers prove
that injectivity automatically. For a finite strip family, the
verified worst-case score is invariant under reducing coefficients modulo `K`,
and the canonical `K x K` domain contains a global minimizer for that frozen
score. When `0 < K` and `K ∣ M`, the canonical pairs with a coprime coordinate
form a nonempty family in which every translated window has exact load
`M^2/K`; this family also contains an exact score minimizer. These are
certified baselines.
A paper contribution must still add a stronger arbitrary-boundary/structural
strip result, a stronger admissibility or constrained-performance theorem, or
a physical routing guarantee and show that it predicts actual repairability,
not merely rediscover modular coloring and interleaving facts. The bounded
aligned tightness result alone does not complete the paper or an open problem.

## Supporting sub-questions

1. What is the sharpest maximum-hop, total-length, turn, or capacity guarantee
   compatible with perfect local color diversity on a finite bump grid?
2. Under identical defect distributions, spare ratios, and mux constraints,
   do those analytic certificates predict DART-model repairability and reduce
   synthesis runtime or variance?

## Falsifiable hypotheses

- **H1 -- certified load:** For `0 < K <= M^2` and every valid color `c < K`,
  full translated `M x M` windows have the proved bound `ceil(M^2/K)`. For the
  lattice-line and finite-strip theorems the exact assumption is only `0 < K`:
  the line bound is `ceil(L/T)`, the physical unique-point strip baseline is
  `W * ceil(L/T)`, and the phase-aware strip upper certificate is
  `ceil(W/R) * ceil(L/T)`, where
  `T = K / gcd(K, lineColorStep M along)` and
  `R = gcd(K, lineColorStep M along) /
  gcd(gcd(K, lineColorStep M along), lineColorStep M across)`. These strip
  theorems do not require `c < K`; invalid colors select no points. The phase
  certificate can be strictly better than the baseline when `R > 1`. For the
  exact theorem, `0 < K`, `c < K`, the full-color-period gcd condition,
  `R ∣ W`, `T ∣ L`, and injective physical sampling imply load
  `(W/R)*(L/T) = ceil(W/R)*ceil(L/T)`. The generalized theorem replaces the
  baseline step by
  `alpha*v.1 + beta*v.2`. The finite-family score has a proved global minimizer
  over all natural coefficient pairs after canonical residue reduction. Under
  `0 < K` and `K ∣ M`, the coprime-coordinate candidate family has exact load
  `M^2/K` for every valid color and contains its own exact score minimizer. The
  remaining load questions concern partial periods, self-overlapping
  multiplicity geometry, and arbitrary or nonrectangular strip unions. A
  complete balanced-coefficient characterization and a useful bound against
  the unconstrained optimum also remain open.
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
- **Result 2 -- certificate:** the proved general affine physical-strip and
  finite-family upper certificates, canonical-domain optimization, and exact
  constrained optimization over the proved balanced sufficient family,
  together with exact aligned nonoverlapping-strip attainment and a stronger
  partial-boundary, overlap-multiplicity, or arbitrary-union characterization.
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

The expanded route A proof package is still not enough by itself for a paper.
The foundational strip theorem, general affine upper certificate, and global
optimizer for the frozen family-score objective are complete. Constrained
co-design is also complete for the `0 < K`, `K ∣ M` coprime-coordinate
sufficient family. Exact load equality is complete only for valid colors on
full-color-period, period-aligned, non-self-overlapping strips. This is neither
a complete balanced-coefficient classification nor arbitrary-strip or
hardware optimality, and the routing result is connectivity rather than a
simple physical chain. The next research gate is a stronger
arbitrary-boundary/structural theorem beyond the aligned case or the sufficient
family. A credible short EDA paper additionally needs a faithful evaluation;
the current package does not certify spare placement, mux reachability, routing
delay/congestion, DART evaluation, arbitrary connected clusters, arbitrary or
nonrectangular unions of finite strips or line prefixes, or general repair
success.
A stronger DATE/ISPD/ICCAD/TCAD submission needs those results together with
repairability evidence. A formal-methods venue additionally needs a larger
verified refinement or executable routing artifact.
