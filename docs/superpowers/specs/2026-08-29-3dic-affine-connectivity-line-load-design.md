# Verified Affine Repair-Chain Connectivity and Line-Load Design

Date: 2026-08-29

Status: approved design for research route A

Tracking issue: [#342](https://github.com/TankTechnology/CLRS-Lean/issues/342)

Draft pull request: [#343](https://github.com/TankTechnology/CLRS-Lean/pull/343)

## Goal

Close the theorem-backed core of the affine 3D-IC repair-chain construction in
two precise senses:

1. on a finite `N x N` bump grid, every two bumps of the same affine chain
   color are connected by a finite same-color path whose every hop has squared
   Euclidean grid distance at most `M^2 + (M - 1)^2`;
2. along a parameterized lattice-line defect, bound the number of failed bumps
   charged to any one chain by the modular period of that line direction.

The result is a complete mathematical closure of route A's combinatorial
model. It is not an end-to-end claim about DART mux circuitry, spare capacity,
timing, signal integrity, or manufacturing physics.

## Existing foundation

Three research modules already establish the local ingredients:

- `WindowDiversity.lean` defines
  `affineChainColor M K i j = (i + M * j) % K` and proves that every translated
  `M x M` window contains every color when `0 < K <= M^2`;
- `WindowRouting.lean` proves the squared-distance bound for representatives of
  adjacent windows and lifts adjacent-window paths to bounded-hop point paths;
- `AffineWindowRouting.lean` combines the two results for any supplied path of
  window origins.

The missing facts are finite-grid boundary coverage, explicit connectivity of
the finite window-origin grid, attachment of arbitrary same-color endpoints,
and modular counting along line defects.

## Mathematical model

### Grid points and windows

A bump coordinate is a pair `(i, j) : Nat x Nat`.

```text
inGrid N (i,j)  := i < N and j < N
inWindow M p q x := p <= x.i < p+M and q <= x.j < q+M
```

Assume:

```text
0 < K
K <= M^2
M <= N
```

These imply `0 < M` and ensure that at least one full target window exists.
Valid window origins satisfy `p <= N-M` and `q <= N-M`.

### Bounded same-color paths

For

```text
R2(M) = M^2 + (M-1)^2,
```

a point list is a bounded same-color grid path when:

- its first point is the requested source;
- its last point is the requested destination;
- every listed point lies in the finite `N x N` grid;
- every listed point has the requested affine chain color;
- consecutive points have `gridDistSq <= R2(M)`.

The path need not be simple. This is a graph-connectivity theorem, not a
Hamiltonian ordering or a total-wire-length theorem. Repetition is allowed so
that the theorem states exactly what the local window argument establishes.

### Lattice-line defects

A parameterized line defect is

```text
linePoint (i0,j0) (a,b) t = (i0 + a*t, j0 + b*t),  0 <= t < L.
```

Along the line,

```text
affineChainColor M K (linePoint base step t)
  = (baseColor + delta*t) mod K,

delta = a + M*b.
```

Let

```text
T = K / gcd(K, delta).
```

Because `0 < K`, the period `T` is positive. All indices producing a fixed
color lie in at most one residue class modulo `T`. Therefore any color occurs
at most

```text
ceil(L / T)
```

times among `t = 0, ..., L-1`.

Important specializations are:

- horizontal unit line `(a,b)=(1,0)`: `T=K`, load at most `ceil(L/K)`;
- vertical unit line `(a,b)=(0,1)`: `T=K/gcd(K,M)`;
- a direction coprime to `K`: `gcd(K,a+M*b)=1`, so every chain receives at
  most `ceil(L/K)` faults.

The theorem counts the infinite-lattice parameterization. A finite-grid
corollary applies when every indexed line point lies in `inGrid N`.

## Construction for finite-grid connectivity

### Canonical covering window

For a coordinate `i < N`, choose the window origin

```text
coverOrigin N M i = min i (N-M).
```

When `M <= N`, this origin is valid and the coordinate lies in its length-`M`
interval. Applying it independently to both coordinates places every finite
grid point in a canonical full `M x M` window.

### Window-origin path

Any two valid window origins are connected inside the origin rectangle
`[0, N-M] x [0, N-M]` by a Manhattan path:

1. move the first coordinate monotonically from the source origin to the
   destination origin;
2. move the second coordinate monotonically to the destination.

Every consecutive pair satisfies `windowAdjacent`, and every origin remains
valid. The construction must handle increasing, decreasing, and equal
coordinates without relying on natural-number subtraction outside proved
bounds.

### Same-color representatives and endpoint attachment

Use `affineChainColor_windowPath_bounded` to choose a point of the requested
color in every window along the origin path. Since all origins are valid, every
representative lies in the finite grid.

Attach the arbitrary source before the first representative and the arbitrary
destination after the last representative. Each endpoint and its adjacent
representative lie in the same `M x M` window, so both coordinate distances are
at most `M-1`. Hence their squared distance is at most

```text
2*(M-1)^2 <= M^2 + (M-1)^2.
```

The resulting list proves the advertised endpoint-exact, finite-grid,
same-color bounded-hop connectivity theorem.

## Lean module boundaries

Keep compilation units small and single-purpose.

### `FiniteGrid.lean`

Defines `inGrid`, valid window origins, and `coverOrigin`. Proves:

- a point in a valid full window lies in the finite grid;
- `coverOrigin` is a valid origin;
- every finite-grid point lies in its canonical covering window;
- two points in one window satisfy the squared-distance threshold.

### `WindowOriginPath.lean`

Defines an executable monotone path between natural coordinates and then a
Manhattan path between window origins. Proves:

- exact first and last origins;
- `List.IsChain windowAdjacent`;
- every origin on the path remains inside the valid origin rectangle.

### `AffineFiniteConnectivity.lean`

Defines the public bounded-path predicate and proves the main theorem:

```text
affineChainColor_finiteGrid_connected
```

For any finite-grid points `x` and `y` with the same requested affine color,
the theorem returns a point list satisfying exact endpoints, grid membership,
color preservation, and the hop bound.

### `LineDefect.lean`

Defines `linePoint`, `lineColorStep`, and `lineColorPeriod`. Proves the modular
progression identity, periodicity, and the exact index-period characterization.

### `LineDefectLoad.lean`

Proves the general cardinality bound and the horizontal, vertical, coprime-step,
and finite-grid corollaries. Counting is over `Finset.range L`; no probability
or simulator assumption enters the theorem.

Each module receives its own interface test under `Tests/Research_ThreeDIC_*`.

## Public theorem surface

The intended reader-facing names are:

```text
inGrid
validWindowOrigin
coverOrigin
inWindow_coverOrigin
gridDistSq_same_window_le

natIntervalPath
windowOriginPath
windowOriginPath_head?
windowOriginPath_getLast?
windowOriginPath_isChain
windowOriginPath_mem_valid

BoundedColorPath
affineChainColor_finiteGrid_connected

linePoint
lineColorStep
affineChainColor_linePoint
lineColor_period
lineColor_index_congruent
lineColor_load_le_ceilDiv_period
lineColor_horizontal_load_le
lineColor_vertical_load_le
lineColor_coprime_load_le
lineColor_finiteGrid_load_le
```

Private arithmetic helpers may be added when they isolate division, modulo,
gcd, or natural-subtraction facts. They must not weaken the public statements.

## Correctness invariants

The development must preserve all of the following:

1. **Endpoint exactness:** connectivity paths start at `x` and end at `y`.
2. **Color exactness:** every path point has color `c`, not merely a valid color.
3. **Finite boundary:** every path point lies in `inGrid N`.
4. **Local hop bound:** `List.IsChain` uses the same squared-distance threshold
   on every consecutive pair.
5. **Nonempty modulus:** period positivity, same-color congruence, and every
   counting theorem explicitly carry `0 < K`; periodicity itself is proved in
   the stronger zero-modulus-compatible form.
6. **Period positivity:** counting never divides by a zero period.
7. **Counting universe:** the denominator is the exact index range
   `Finset.range L`, not all lattice points or all finite-grid points.
8. **Claim separation:** connectivity and fault-load theorems do not claim a
   simple Hamiltonian chain, spare feasibility, or measured yield.

## Testing strategy

Every public theorem family follows the Lean interface red-green loop:

1. add its intended `#check` to a focused interface test;
2. run the test and confirm failure due to the missing module or identifier;
3. implement the smallest supporting theorem set;
4. run the module build and interface test to green;
5. add small executable examples for boundary cases such as `M=1`, `N=M`,
   zero-length line defects, zero line step, horizontal lines, and non-coprime
   vertical steps.

The final gate is:

```text
lake build <all ThreeDIC research modules>
lake env lean <all ThreeDIC interface tests>
trust-pattern scan for sorry/admit/axiom/native_decide
git diff --check
```

A broader root build is run only if the research modules are deliberately
imported into the project root; this design keeps them separate from the CLRS
textbook-completion surface.

## Documentation and research claims

Update the research note, issue, and draft PR with three distinct labels:

- **proved:** finite-grid same-color bounded-hop connectivity and line-load
  period/counting bounds;
- **known baseline:** full square-window diversity and generic graph-cube
  Hamiltonian facts;
- **unproved/model-dependent:** simple chain ordering, total wire length,
  DART spare/mux repairability, and empirical yield.

The line-load theorem must be audited against burst-error/interleaving and
array-code literature before it is described as novel. Formal correctness does
not establish publication novelty.

## Completion criteria

Route A's proof package is complete when:

1. all public theorem names above compile without `sorry`, `admit`, new axioms,
   or `native_decide`;
2. the finite-grid connectivity theorem exposes exact endpoints, same-color
   membership, finite-grid membership, and the stated hop bound in one usable
   interface;
3. the general lattice-line theorem bounds per-color load by
   `ceil(L / (K/gcd(K,a+M*b)))` and the listed special cases follow;
4. focused interface tests and trust checks pass;
5. the research documentation states the claim boundary without calling the
   result a solved community open problem before the novelty audit;
6. changes are committed in reviewable stages and pushed to draft PR #343.
