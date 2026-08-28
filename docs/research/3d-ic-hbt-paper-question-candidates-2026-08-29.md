# Candidate Research Questions: Provable 3D-IC Repair Chains

Date: 2026-08-29

Status: adversarial question audit; none of these questions is yet claimed as
an open problem or a publication contribution

Tracking issue: [#342](https://github.com/TankTechnology/CLRS-Lean/issues/342)

## Evidence boundary

The current artifact proves one exact statement: for `0 < K <= M^2`, the
affine assignment

```text
color(i, j) = (i + M * j) mod K
```

puts all `K` repair-chain colors in every translated `M x M` window. This
exactly minimizes DART's diversity term, but it says nothing by itself about
the routing term or post-fault repairability.

This diversity theorem is not a safe novelty claim. In the language of
polychromatic colorings, an `M x M` square tiles `Z^2`, and known theory relates
full-size polychromatic colorings to translational tilings. The affine formula
is therefore best treated as a simple exact construction specialized to the
DART objective, not as a newly solved open problem. Relevant prior art includes
[Polychromatic Colorings on the Integers](https://arxiv.org/abs/1704.00042)
and the broader perfect-map literature.

The research opportunity begins only when local diversity is coupled to
finite-grid routing, balance, spare placement, or repairability under a stated
fault model.

## Q1. Can DART's diversity term be optimized exactly without search?

### Question

For `K <= M^2`, can one construct an `N x N` repair-chain assignment attaining
the information-theoretic minimum of the sliding-window diversity loss?

### Conceptual height

Phenomenon/constructive baseline. It removes an unnecessary heuristic from one
component of a larger optimizer but does not explain the full design problem.

### Core hypotheses

- H1: The affine coloring contains every color in every `M x M` window.
- H2: Its diversity loss equals `(N-M+1)^2 (M^2-K)` when `N >= M`.

### Current evidence

H1 is formally proved in Lean. H2 is a short finite-sum corollary, not yet
formalized.

### Venue fit and risk

Useful lemma or baseline, not a standalone paper. High prior-art risk and low
conceptual height.

### Provisional role

Mechanism-only result.

## Q2. Which assignments achieve perfect sliding-window diversity?

### Question

Can all periodic or finite-boundary colorings in which every `M x M` window
contains every color be characterized, including their balance and periods?

### Conceptual height

Structural combinatorics: asks for the solution space rather than one formula.

### Core hypotheses

- H1: Under `K=M^2` and suitable periodicity, perfect assignments have a rigid
  tiling/coset structure.
- H2: For `K<M^2`, non-affine solution families can improve routing while
  retaining perfect diversity.

### Current evidence

Only one affine family is proved. No classification data or theorem exists.

### Venue fit and risk

Potential combinatorics result, but may already live in polychromatic-coloring,
tiling, covering-array, or symbolic-dynamics literature. Weak EDA story unless
the characterization enables better chains.

### Provisional role

Supporting sub-question.

## Q3. Does perfect local diversity force bounded-hop global connectivity?

### Question

If every `M x M` window of a finite bump grid contains a given chain color,
must that color class be connected when points within a universal radius are
linked?

### Conceptual height

Mechanism question connecting local fault dispersion to global routability.

### Core hypotheses

- H1: Radius `R = sqrt(M^2 + (M-1)^2)` suffices for connectivity.
- H2: The classical cube-of-a-connected-graph theorem gives a safe generic
  Hamiltonian-order baseline of `3R`; any `R` or `2R` result requires extra
  structure and a separate proof.
- H3: Some constant smaller than `R` is impossible in the worst case.

### Current evidence

H1 has a short proof plan through the connected graph of sliding windows: pick
a colored representative per window and compare representatives of adjacent
windows. A 7,350-instance sweep found no counterexample. The tempting claim
that a doubled spanning-tree traversal can be shortcut to `2R` is false in
general: a shortcut may skip arbitrarily many tree edges. The safe generic
Hamiltonian baseline is instead the classical result that the cube of every
connected graph is Hamiltonian-connected.

### Venue fit and risk

Strong bridge lemma, but not a standalone paper. The connectivity upper bound
is elementary, while the generic `3R` Hamiltonian lift is classical; sharp
lower bounds or grid-specific `R`/`2R` routing would be the novel part.

### Provisional role

Supporting sub-question / theorem.

## Q4. Can one jointly guarantee optimal diversity and bounded repair routing?

### Question

For a finite `N x N` hybrid-bond array with `K <= M^2` repair chains, is there a
deterministic construction that is globally optimal for DART's local-diversity
term and simultaneously gives each color class a provably short physical
chain?

### Conceptual height

Structural EDA question: identifies when a heuristic multi-objective tradeoff
is genuine and when one objective can be closed exactly without sacrificing a
bounded routing guarantee.

### Core hypotheses

- H1: Exact diversity and `O(M)` maximum-hop routing are simultaneously
  achievable for all feasible `N,M,K`.
- H2: A polynomial-time construction provides an approximation guarantee for
  total chain length or fragmentation.
- H3: The guarantee remains competitive with DART's simulated annealing under
  identical physical constraints.

### Current evidence

Exact diversity is proved. The generic connectivity argument suggests an
`O(M)` bottleneck guarantee for any perfectly diverse coloring, but total
length, Hamiltonian ordering, finite boundaries, and DART's exact greedy
fragmentation objective are not closed.

### Venue fit and risk

Best current EDA headline. It can support an ISPD/DATE/VTS-style paper if the
routing objective is physically faithful and experiments are reproduced. It
is not yet an established community open problem; it is a newly extracted,
well-posed research question from DART's heuristic formulation.

### Provisional role

Headline candidate.

## Q5. What is the approximation complexity of diversity-plus-fragmentation?

### Question

For the weighted objective `alpha * L_div + beta * L_frag`, what approximation
ratios are possible, and which restricted parameter regimes admit exact
polynomial-time algorithms?

### Conceptual height

Structural algorithmic question about the boundary between easy local
dispersion and hard global routing.

### Core hypotheses

- H1: The unrestricted joint problem is NP-hard.
- H2: Fixed `M` or fixed `K` admits dynamic programming or a PTAS on the grid.
- H3: Seeding with an exact-diversity construction improves the practical
  Pareto frontier without weakening worst-case guarantees.

### Current evidence

No reduction or algorithmic guarantee exists. DART reports an ILP with
quadratic pair variables and uses simulated annealing, which is motivation but
not a hardness proof.

### Venue fit and risk

Potentially strong algorithms/EDA paper. High proof risk because the exact
definition of `L_frag` is algorithm-dependent and may be awkward as an
optimization objective.

### Provisional role

Headline candidate if a clean hardness/approximation boundary is found.

## Q6. What is the diversity-routing-balance Pareto frontier?

### Question

How do perfect local color diversity, equal repair-chain capacity, maximum hop,
and total wire length constrain one another on finite grids?

### Conceptual height

Structural tradeoff question, closer to physical design than diversity alone.

### Core hypotheses

- H1: Exact balance and exact diversity coexist for broad divisibility classes.
- H2: Boundary imbalance is bounded by a constant for the affine family.
- H3: Any exact-diversity assignment obeys a nontrivial routing lower bound.

### Current evidence

At the DART-scale audit point `N=25,M=3,K=8`, affine color-class sizes differ by
at most one. No general balance theorem or routing lower bound has been proved.

### Venue fit and risk

Good results-section organizer. It becomes too broad unless one Pareto theorem
is sharp.

### Provisional role

Supporting sub-question.

## Q7. Do deterministic chains improve repairability under clustered faults?

### Question

Under the same cluster, line, and random-fault distributions and spare budgets
used by DART, does a provable deterministic chain construction match or improve
repairability, runtime, and rerouting overhead?

### Conceptual height

Empirical mechanism question: tests whether theorem-backed dispersion predicts
actual repair outcomes.

### Core hypotheses

- H1: Perfect window diversity improves worst-case local load distribution.
- H2: Bounded-hop ordering prevents the routing penalty of naive modular
  interleaving.
- H3: The deterministic method is substantially faster and less variable than
  simulated annealing while preserving repairability.

### Current evidence

No faithful DART reproduction has been run. Current sweeps validate only
combinatorial window coverage and geometric connectivity conjectures.

### Venue fit and risk

Required for an EDA publication, but not a sufficient headline by itself. It
may falsify the deterministic design if unmodeled constraints dominate.

### Provisional role

Empirical supporting question.

## Q8. Can line-defect robustness be certified rather than sampled?

### Question

For a stated family of horizontal, vertical, diagonal, or bounded-width line
faults, can one certify the maximum number of failed bumps assigned to any
repair chain and derive a sufficient spare budget?

### Conceptual height

Mechanism/robust-optimization question tailored to wafer-to-wafer particle
defects rather than generic stochastic trials.

### Core hypotheses

- H1: Affine chain assignments admit closed-form per-line load bounds.
- H2: Choosing the affine slope coprime to `K` minimizes worst-case line
  concentration over a specified direction set.
- H3: The certificate predicts simulator repairability for the modeled faults.

### Current evidence

YAP+ motivates approximately straight particle-void tails, but no formal line
family, load theorem, or comparison exists yet.

### Venue fit and risk

Potentially fun and tractable EDA contribution. It needs careful defect physics
and can collapse into elementary modular arithmetic if the fault family is too
simple.

### Provisional role

Alternate headline / supporting theorem.

## Q9. How should spare placement be co-designed with repair-chain coloring?

### Question

Can repair-chain colors and spare-bump locations be selected jointly to provide
certified repairability against localized defect sets at bounded routing cost?

### Conceptual height

Structural architecture question: moves from coloring a fixed spare layout to
co-designing redundancy.

### Core hypotheses

- H1: Alternating/coset spare placements give exact guarantees for bounded
  windows.
- H2: Joint placement strictly dominates color-only optimization at equal spare
  ratio.
- H3: A tractable special case has a matching- or flow-based exact algorithm.

### Current evidence

No model or result exists. The earlier robust-matching audit shows that generic
formulations overlap substantial prior art.

### Venue fit and risk

High EDA relevance but too expansive for the first paper and at high risk of
rediscovering robust assignment/facility-location results.

### Provisional role

Framing/future work.

## Q10. Can the repair architecture be verified end to end?

### Question

Can a theorem-proved chain generator be refined into a concrete mux/control
architecture with machine-checked functional repair and resource bounds?

### Conceptual height

Structural formal-methods question linking mathematical construction to
hardware implementation.

### Core hypotheses

- H1: The generated hardware implements the abstract rerouting semantics.
- H2: Area, depth, and control-state bounds follow from the construction.
- H3: Fault certificates can be checked by an executable verified procedure.

### Current evidence

Only the affine coloring theorem is in Lean. There is no RTL, refinement map,
or verified fault-routing algorithm.

### Venue fit and risk

Could become a CPP/ITP/FM artifact or complement an EDA paper, but it is a much
larger project and should not obscure the first algorithmic contribution.

### Provisional role

Long-term framing.

## Provisional top three before independent review

1. Q4: deterministic exact diversity plus bounded routing;
2. Q8: certified robustness against line-shaped faults;
3. Q5: complexity/approximation boundary for the joint objective.

The immediate theorem path is Q3 -> Q4. The immediate empirical falsification
path is Q7. Q1 remains a formally verified baseline, not the claimed research
novelty.
