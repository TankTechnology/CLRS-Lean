# Affine Window Coloring for 3D-IC Repair Chains

Date: 2026-08-29

Tracking issue: [#342](https://github.com/TankTechnology/CLRS-Lean/issues/342)

Status: research baseline; not part of the CLRS textbook-completion claim

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

This observation does not solve DART's full optimization problem. Routing
length, finite-boundary chain ordering, spare placement, signal-integrity
constraints, and repairability under concrete clustered faults remain open.

## Lean artifact

The theorem is formalized in
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

The last item is empirical evidence, not yet a theorem. A sweep over 7,350
tuples with `2 ≤ M ≤ 15`, `2 ≤ K ≤ M²`, and several grid sizes found no
counterexample to the stronger conjecture that each finite color class is
connected using edges of length at most
`√(M² + (M - 1)²)`.

## Prior-art audit

The earlier expected-matching-rank proposal is not a novelty candidate:
matching rank is a transversal-matroid rank, hence submodular, and expectation
preserves submodularity. Generic scenario-robust matching is also covered by
the robust-assignment literature.

The affine construction instead targets the specific graph-coloring objective
used for hybrid-bond repair chains. Its relationship to grid distance coloring,
polychromatic coloring, periodic array design, and geometric discrepancy still
requires a focused novelty audit.

Starting references:

- [DART: Dynamic Repair for Interconnect Fault Tolerance in Hybrid Bonding](https://doi.org/10.1109/VTS69484.2026.11563352)
- [YAP+: Pad-Layout-Aware Yield Modeling and Simulation for Hybrid Bonding](https://arxiv.org/html/2511.05506v1)
- [Robust Assignments with Vulnerable Nodes](https://arxiv.org/abs/1703.06074)
- [How to Secure Matchings Against Edge Failures](https://doi.org/10.4230/LIPIcs.STACS.2019.38)

## Next decision gates

1. Complete the grid-coloring and periodic-array novelty audit.
2. Prove or refute the finite-grid bottleneck-connectivity conjecture.
3. Replace the random-start nearest-neighbor compactness proxy with a canonical
   chain-ordering objective and prove an approximation or exact special case.
4. Reproduce DART's repairability evaluation and compare the deterministic
   affine construction against its heuristic chains under identical fault and
   spare models.
5. Formalize only the theorem-backed routing result after the objective and
   boundary semantics are frozen.
