# Affine Window Coloring for 3D-IC Repair Chains

Date: 2026-08-29

Tracking issue: [#342](https://github.com/TankTechnology/CLRS-Lean/issues/342)

Status: verified route A proof package; not a novelty claim and not part of
the CLRS textbook-completion claim

## Research boundary

DART assigns every hybrid-bond bump to a repair chain (a color). Its diversity
term slides an `M × M` window over an `N × N` bump grid and penalizes missing
colors; its compactness term measures a greedy geometric traversal of each
color class. DART uses simulated annealing to trade off these objectives.

The diversity term alone has a deterministic exact baseline. For `K ≤ M²`,
define

```text
color(i, j) = (i + M * j) mod K.
```

Every translated `M × M` window contains every one of the `K` colors. No
coloring can expose more than all available colors, so the construction reaches
the global lower bound of the DART diversity loss.

In the established language of polychromatic coloring, this is the special
case where the square window tiles the integer grid. It should therefore be
described as an exact DART-specific baseline, not as a solved open problem.

This observation does not solve DART's full optimization problem. The current
artifact now proves finite-boundary same-color connectivity with a local hop
bound and an exact load ceiling for parameterized lattice-line defects. Simple
chain ordering, total route length, strip/cluster defects, spare placement,
signal-integrity constraints, and repairability under concrete fault models
remain open.

## Lean artifact

The diversity theorem is formalized in
`CLRSLean/Research/ThreeDIC/WindowDiversity.lean`:

- `affineChainColor` is the executable construction;
- `affineChainColor_lt` proves that it produces a valid color residue;
- `affineChainColor_window_surjective` proves that every target-size window
  contains each repair-chain color.

The constructive witness first chooses an offset `t < K` with the target
modular residue and then uses Euclidean division:

```text
t = (t mod M) + M * (t / M).
```

The assumption `t < K ≤ M²` places both coordinates inside the window.

Seven small follow-on modules close route A's combinatorial proof package:

- `WindowRouting.lean` proves that arbitrary representatives of horizontally
  or vertically adjacent `M × M` windows have squared grid distance at most
  `M² + (M - 1)²`, and lifts an adjacent-window path to a bounded-hop
  representative path;
- `AffineWindowRouting.lean` combines that geometry with affine window
  surjectivity, selecting the requested chain color in each window along any
  adjacent-window path;
- `FiniteGrid.lean` and `WindowOriginPath.lean` prove finite-boundary window
  coverage and construct valid Manhattan paths between canonical window
  origins;
- `AffineFiniteConnectivity.lean` proves
  `affineChainColor_finiteGrid_connected`: any two same-color bumps in an
  `N × N` grid admit an endpoint-exact same-color path that stays in the grid,
  with every squared hop at most `M² + (M - 1)²`;
- `LineDefect.lean` proves the modular line progression, positive period
  `T = K / gcd(K, a + M*b)`, periodicity, and the converse same-color index
  congruence;
- `LineDefectLoad.lean` proves that each color occurs at most `ceil(L/T)` times
  in a length-`L` line prefix, with horizontal, vertical, coprime-step, and
  finite-grid corollaries.

The connectivity path may repeat vertices. The result therefore does not give
a simple or Hamiltonian ordering of every bump in a color class, a
total-wire-length bound, or an end-to-end repairability theorem.

## Executable audit

An in-memory exhaustive audit checked the affine construction on representative
DART-scale and parameter-sweep instances.

For `N = 25`, `M = 3`, and `K = 8`:

- every `3 × 3` window contains all eight colors;
- the measured diversity loss is `529`, equal to the information-theoretic
  lower bound `(25 - 3 + 1)² × (3² - 8)`;
- color-class sizes are `79, 78, 78, 78, 78, 78, 78, 78`;
- the Euclidean minimum-spanning-tree bottleneck observed across the color
  classes is `√10` bump pitches.

The last item motivated the now-formal local representative bound. A sweep over
7,350 tuples with `2 ≤ M ≤ 15`, `2 ≤ K ≤ M²`, and several grid sizes found no
counterexample to finite color-class connectivity at radius
`√(M² + (M - 1)²)`. The later Lean theorem now proves that finite-boundary
connectivity statement for arbitrary same-color endpoints, independently of
the executable sweep.

## Prior-art audit

The earlier expected-matching-rank proposal is not a novelty candidate:
matching rank is a transversal-matroid rank, hence submodular, and expectation
preserves submodularity. Generic scenario-robust matching is also covered by
the robust-assignment literature.

The affine construction targets the specific graph-coloring objective used for
hybrid-bond repair chains, but the focused audit found that its diversity-only
content lies in established polychromatic-coloring/tiling territory. Axenovich
et al. state the general equivalence between a finite shape tiling an abelian
group and attaining full polychromatic number. The square-window result is an
elementary instance.

The generic route-ordering baseline must also be stated carefully. A doubled
tree traversal cannot simply be shortcut to obtain a `2R` maximum hop. The
classical theorem that the cube of every connected graph is
Hamiltonian-connected gives a safe generic `3R` baseline; a sharper `R` or
`2R` result would need extra grid structure.

Starting references:

- [DART: Dynamic Repair for Interconnect Fault Tolerance in Hybrid Bonding](https://doi.org/10.1109/VTS69484.2026.11563352)
- [YAP+: Pad-Layout-Aware Yield Modeling and Simulation for Hybrid Bonding](https://arxiv.org/html/2511.05506v1)
- [Robust Assignments with Vulnerable Nodes](https://arxiv.org/abs/1703.06074)
- [How to Secure Matchings Against Edge Failures](https://doi.org/10.4230/LIPIcs.STACS.2019.38)
- [Polychromatic Colorings on the Integers](https://arxiv.org/abs/1704.00042)
- [Graph powers and k-ordered Hamiltonicity](https://arxiv.org/abs/math/0307359)
- [Error-Correction of Multidimensional Bursts](https://arxiv.org/abs/0712.4096)

## Next decision gates

1. Extend the now-certified lattice-line family to a parameterized strip or
   cluster-fault family and freeze the exact DART spare/mux repair semantics.
2. Audit the proved modular line-load certificate against multidimensional
   burst-error/interleaving prior art; seek a stronger hardware-specific bound
   before making a novelty claim.
3. Strengthen the proved finite-boundary connectivity result to a sharp simple
   ordering, Hamiltonian, or total-length guarantee beyond the classical
   generic `3R` baseline.
4. Replace the random-start nearest-neighbor compactness proxy with a canonical
   chain-ordering objective and prove an approximation or exact special case.
5. Reproduce DART's repairability evaluation and compare the deterministic
   affine construction against its heuristic chains under identical fault and
   spare models.
6. Keep formalizing theorem-backed load and routing results in small modules;
   do not formalize simulator assumptions until their semantics are frozen.
