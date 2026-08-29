# Literature Audit and Generalization Contract for the 3D-IC Route-A Proofs

Date: 2026-08-29

Status: primary-source audit completed for the closest mathematical, coding,
formalization, and hybrid-bond repair-chain work found in this pass. This is a
novelty-screening document, not a claim of exhaustive prior-art clearance.

## Executive verdict

The current Lean package proves real, reusable theorems, but it does not solve
a recognized open conjecture. Its three mathematical ingredients--translated
window coverage, lattice/interleaver coloring, and modular load counting along
a line--all have substantial prior-art neighbors. A separate Lean project also
formalizes polychromatic colorings of the integers, so we must not claim the
first Lean formalization of polychromatic coloring.

The defensible contribution today is narrower: a kernel-checked,
DART-motivated deterministic construction that simultaneously exposes local
window diversity, exact floor/ceiling-balanced box load, finite-grid same-color
connectivity, and exact line-defect period/load certificates. This is a useful
verified baseline and a strong starting point, but not yet a standalone
research result of the strength needed for an EDA or formal-methods paper.

The most valuable next step is not a broader dimension-only generalization. It
is an end-to-end *repairability certificate*: prove balanced per-chain load for
box/strip defects, connect that load to spare/protection-window capacity and a
simple physical chain, and validate the resulting sufficient condition under
the same model as DART.

## Frozen research contract

### Phenomenon and scope

- **Phenomenon:** deterministic assignment of an `N x N` hybrid-bond bump grid
  to `K` repair chains under spatially correlated faults.
- **Current construction:** `color(i,j) = (i + M*j) mod K`.
- **Units of analysis:** one translated window, one finite color class, one
  finite lattice-line prefix, and eventually one DART protection window.
- **Current defect families:** translated `M x M` boxes and finite nonnegative
  lattice-line prefixes. Arbitrary connected clusters, thick strips, and unions
  of lines are not currently covered.
- **Certified outputs:** existential color coverage, exact per-color
  floor/ceiling window load, bounded-hop connectivity, exact line-color period,
  and per-color box/line ceiling load bounds.
- **Not certified:** simple/Hamiltonian repair-chain ordering, total wirelength,
  turns or congestion, spare placement, mux behavior, or end-to-end repair
  success.

### Evidence labels

- **Kernel-checked:** a theorem built by Lean from the pinned repository state.
- **Literature-established:** a claim made by a cited primary source, not
  re-proved in this repository.
- **Derived hypothesis:** a proposed strengthening that still needs proof.
- **Model-dependent:** a claim requiring a faithful DART/hardware or empirical
  model in addition to combinatorics.

### Canonical local evidence

- `CLRSLean/Research/ThreeDIC/WindowDiversity.lean`
- `CLRSLean/Research/ThreeDIC/AffineFiniteConnectivity.lean`
- `CLRSLean/Research/ThreeDIC/LineDefect.lean`
- `CLRSLean/Research/ThreeDIC/LineDefectLoad.lean`

## Exact theorem surface and classification

| Lean result | Exact content | Audit classification |
|---|---|---|
| `affineChainColor_window_surjective` | If `0 < K <= M^2`, every color occurs in every translated `M x M` window. | Explicit construction in known polychromatic/interleaving territory; useful baseline, not safe as mathematical novelty. |
| `affineChainColor_window_count_eq_floor_or_ceil` and `affineChainColor_window_load_le_ceilDiv` | Every color occurs either `floor(M^2/K)` or `ceil(M^2/K)` times in every translated `M x M` window, hence never more than the ceiling. | Verified box-defect capacity certificate, but still an elementary consecutive-residue count rather than standalone novelty. |
| `affineChainColor_finiteGrid_connected` | Same-color finite-grid endpoints admit a same-color path with squared hop at most `M^2 + (M-1)^2`; repetition is allowed. | Application-specific finite-boundary lemma. The exact formulation was not found in the audited sources, but it is elementary and should not carry the paper's novelty claim. |
| `lineColorPeriod` and `lineColor_index_congruent` | Along a lattice line, the color sequence has period `K / gcd(K, dx + M*dy)`, and equal colors force congruent indices modulo that period. | Standard modular-arithmetic structure; not standalone novelty. |
| `lineColor_load_le_ceilDiv_period` | A color occurs at most `ceil(L/T)` times in a length-`L` prefix, with the exact period above. | Direct counting corollary of the modular progression; useful certificate, not standalone novelty. |

## Primary-source prior-art matrix

| Source | What it already establishes | Collision with route A | Remaining gap useful to us |
|---|---|---|---|
| [Blaum, Bruck, and Vardy, 1998](https://authors.library.caltech.edu/records/t4s49-2nn79) | Defines multidimensional `t`-interleaved arrays so every connected cluster of area/volume `t` has distinct labels; gives optimal two-dimensional schemes and lattice interleavers. | Strong collision with generic claims about grid coloring, connected clusters, optimal diversity, and lattice constructions. | It does not model DART spare blocks, mux semantics, finite repair-chain ordering, or our exact load-to-repairability implication. |
| [Etzion and Yaakobi, 2007](https://arxiv.org/abs/0712.4096) | Uses multiple linear colorings of `D`-dimensional arrays to construct codes for box, Lee-sphere, and arbitrary cluster errors; explicitly identifies unresolved coding bounds. | Strong collision with broad claims that affine/linear multidimensional coloring for cluster faults is new. | Their coding objective differs from DART chain capacity and physical routing; a faithful bridge would itself need proof. |
| [Axenovich et al., 2019](https://arxiv.org/abs/1704.00042) | Defines `S`-polychromatic colorings by requiring every translate of `S` to receive every color; studies integers and extensions to `Z^d`, homomorphic constructions, and tiling connections. | Direct conceptual home for translated-window surjectivity. | It does not provide DART-specific routing, spares, mux semantics, or repairability. |
| [Bhoumik et al., DART, 2026](https://doi.org/10.1109/VTS69484.2026.11563352) and its [author-hosted PDF](https://nanocad.ee.ucla.edu/wp-content/papercite-data/pdf/c139.pdf) | Uses sliding-window color diversity plus a greedy traversal fragmentation penalty and edge-aware simulated annealing to form irregular repair chains; evaluates cluster and line faults under spare budgets. | It supplies the actual EDA problem and already treats diversity and compactness jointly. We cannot imply that route A invented the objective or the repair architecture. | DART is heuristic: the audited paper does not give our closed-form worst-case window/line certificates or a machine-checked end-to-end theorem. |
| [Chuang and Marinissen, 2025](https://imec-publications.be/entities/publication/5ca38539-61f0-4a29-99d9-3f02c11b81cd) | Proposes clustered-defect repair with minimal propagation delay and improved repair rate relative to default UCIe. | Any claim about propagation-delay novelty needs a direct comparison with this architecture. | The accessible abstract does not establish a formal worst-case certificate for our coloring construction. |
| [Mehta et al., Polychromatic Colourings in Lean](https://github.com/b-mehta/Polychromatic) | A substantial Lean formalization of polychromatic colorings of integers, including the four-integers/three-colors result and general infrastructure. | Rules out “first Lean formalization of polychromatic coloring.” | Its stated scope is integer polychromatic combinatorics, not DART-compatible repairability or our finite-grid hardware model. |

The audit found no primary source that exactly combines all four route-A
interfaces with DART's repair semantics. Absence from this search is not proof
of novelty; a paper submission still needs a systematic database and citation
chaining pass, especially over TSV/chiplet repair and interleaver patents.

## Claim ledger

### Safe now

- “We formally verify a deterministic affine repair-chain baseline with
  translated-window coverage and balanced box load, finite-grid bounded-hop
  connectivity, and exact line-defect load certificates.”
- “The construction gives a closed-form certified alternative for a restricted
  subproblem motivated by DART.”
- “To our knowledge, the audited literature does not combine these exact
  certificates with DART's spare/mux repair semantics.” This must remain
  qualified by the audit scope.

### Unsafe now

- “We solved an open problem/conjecture.”
- “We invented polychromatic or lattice-interleaver coloring.”
- “This is the first Lean formalization of polychromatic coloring.”
- “The construction guarantees DART repairability.”
- “The bounded-hop witness is a physical repair chain” or “has bounded total
  wirelength.”

## Generalization ladder

Scores use `1` (low) through `5` (high). Novelty risk is reversed: `5` means
high collision risk. These are screening estimates, not acceptance forecasts.

| ID | Candidate theorem/research question | Height | Tractability | EDA relevance | Novelty risk | Role |
|---|---|---:|---:|---:|---:|---|
| A | Rectangular `A x B` windows with a mixed-radix affine construction. | 2 | 5 | 3 | 5 | Library extension only. |
| B | `d`-dimensional boxes with mixed-radix coloring. | 2 | 4 | 3 | 5 | Library extension; prior-art heavy. |
| C | General finite translational tiles and group-homomorphism colorings. | 3 | 3 | 2 | 5 | Mathematical abstraction, not the paper headline. |
| D | Characterize which `alpha*i + beta*j mod K` colorings are surjective on every `M x M` window. | 4 | 2 | 4 | 3 | Interesting algebra/additive-combinatorics direction; scope carefully. |
| E | Exact floor/ceiling balance in every translated `M x M` window for the current construction. | 3 | 5 | 5 | 3 | **Proved baseline:** `affineChainColor_window_count_eq_floor_or_ceil`; not a paper headline. |
| F | Construct a simple/Hamiltonian same-color path with bottleneck, turns, and total-length bounds. | 5 | 2 | 5 | 3 | Major routing theorem; likely paper-critical. |
| G | Prove tight per-chain load bounds for width-`w` strips rather than a single lattice line. | 4 | 4 | 5 | 3 | Best medium-sized mathematical extension. |
| H | Bound per-chain discrepancy for arbitrary connected or bounded-box clusters by area plus a boundary term. | 5 | 2 | 5 | 4 | High value but strong interleaving/discrepancy collision risk. |
| I | For a finite family of defect directions, choose affine coefficients with provably good worst-direction period while preserving window balance. | 5 | 3 | 5 | 3 | Strong co-design question; avoid reducing it to constant search. |
| J | Formalize DART protection windows/spares/mux shifts and prove that certified load plus routing conditions imply repairability. | 5 | 2 | 5 | 2 | Highest-value end-to-end contribution. |

## Recommended question stack

### Headline question

Given local-diversity constraints, a spare budget, and a specified family of
likely line or strip defects, can affine coloring coefficients be selected so
that the worst per-chain defect load has a provably optimal or approximately
optimal bound?

### Supporting questions

1. Which affine coefficients preserve translated-window surjectivity or
   near-exact balance, and how can that feasible family be characterized
   without exhaustive constant search?
2. For a direction, width, length, and phase--and then for unions of such
   defects--what is the exact or tight per-chain load bound?

The system-level endpoint remains an end-to-end repairability envelope: connect
the optimized load certificate and a physical route certificate to paired
spares, protection windows, and second-adjacent mux shifts.

### Falsifiable hypotheses

- **Verified balance baseline:** every translated `M x M` box assigns each
  chain either `floor(M^2/K)` or `ceil(M^2/K)` bumps under the current
  construction.
- **Strip extension:** a width-`w`, length-`L` lattice strip admits a per-chain
  bound that is materially tighter than the trivial sum of `w` independent
  line bounds for relevant DART parameters.
- **Repair implication:** under explicit healthy-spare and nonconflicting-shift
  assumptions, no protection window whose certified per-subchain fault load is
  within capacity causes repair failure.
- **Practical value:** the deterministic construction is competitive with
  DART's heuristic repairability while reducing synthesis time and variance.

## Execution roadmap and gates

1. **Balanced-window theorem -- completed.** The canonical window enumeration
   is proved bijective, and `affineChainColor_window_count_eq_floor_or_ceil`
   gives exact floor/ceiling residue counts. This strengthens diversity into a
   box-defect capacity certificate but is not paper-sufficient alone.
2. **Strip load theorem (medium risk, about 2--4 focused days).** Define a
   finite strip as parallel line prefixes, prove a first compositional bound,
   then seek a sharper bound exploiting phase offsets. Include tight examples.
3. **Coefficient/direction co-design (medium/high risk, about 1--2 weeks).**
   Freeze the admissible affine family and prove a non-enumerative existence or
   approximation result. Stop if the result collapses to a small constant
   search with no structural statement.
4. **Simple physical chains (high risk, about 1--2 weeks).** Replace the
   repeat-permitting connectivity witness by a simple ordering and prove
   bottleneck/length/turn bounds; compare directly with minimal-delay repair
   work.
5. **DART semantic bridge and evaluation (high risk, about 2--4 weeks).** Model
   paired spares, protection windows, second-adjacent subchains, failed spares,
   and mux shifts. Prove a sufficient repair theorem and test whether its
   certificate predicts the original repair simulator's success/failure.

The sensible next implementation is now step 2. The publishable unit is likely
the completed step 1 plus step 2 and either step 4 or step 5, together with a
faithful evaluation. Dimension-only generalizations A--C should be added only
when they support that unit.

## Independent question review

An independent review pass, given the proved theorem surface and the primary
prior-art summary but asked not to edit the project, ranked the candidates as
follows:

1. **I -- coefficient co-design over a defect-direction family** is the best
   headline problem, provided it includes a structural existence,
   lower-bound, optimality, or approximation theorem rather than finite
   enumeration.
2. **G -- tight strip-defect load** is the best near-term research theorem and
   the natural bridge from the existing line result to I.
3. **D -- general affine-window classification** has theoretical height, but
   finite-window surjectivity is a restricted sumset question and is unlikely
   to reduce to a gcd condition alone.
4. **J -- end-to-end DART soundness** has the highest systems value but needs a
   new faithful hardware semantics; it is not a small corollary of route A.

The review rejected A and C as paper headlines: A is a direct mixed-radix
variant, while C is too broad, prior-art dense, and detached from the EDA
semantics. It also emphasized that E--now proved--is a high-value support lemma
but not a standalone novelty contribution, and that arbitrary connected-cluster
discrepancy may have no useful uniform bound without stronger shape
restrictions.

## Publication positioning

- **Current package alone:** suitable as an artifact/demo or a documented
  verified case study, not yet a convincing full research paper.
- **With balanced box/strip loads and DART evaluation:** plausible short
  EDA/test/reliability paper, subject to novelty and experimental results.
- **With an analytic coefficient co-design theorem or strong physical-chain
  bound plus end-to-end semantics:** potentially a stronger EDA or
  formal-methods paper.
- **Formal-methods venue:** requires more than theorem count--prefer an
  executable generator/refinement theorem and audited trust story.
- **ICLR:** not the natural venue unless the central contribution becomes a
  learning/optimization method with substantial empirical evidence. The
  current contribution fits EDA, test/reliability, combinatorics, or formal
  verification much better.
