import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford
import CLRSLean.Chapter_24.Section_24_2_SSSP_In_DAGs
import CLRSLean.Chapter_24.Section_24_3_Dijkstra
import CLRSLean.Chapter_24.Section_24_4_Difference_Constraints

/-! # Chapter 24 - Single-Source Shortest Paths

Chapter 24 opens the shortest-path part of the CLRS graph track.  It builds a
finite weighted directed-graph model on top of the Chapter 22 style graph
vocabulary and formalizes the Bellman-Ford algorithm: the relaxation dynamic
program, the upper-bound property, realizability of estimates by actual walks,
cycle removal under the no-negative-cycle hypothesis, exact correctness after
{lit}`|V| - 1` rounds, convergence, and the {lit}`O(V·E)` work bound.

## Sections

* 24.1 The Bellman-Ford algorithm.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph`,
  {lit}`CLRS.Chapter24.WeightedGraph.walkWeight`,
  {lit}`CLRS.Chapter24.WeightedGraph.IsWalkFrom`,
  {lit}`CLRS.Chapter24.WeightedGraph.relaxDist`,
  {lit}`CLRS.Chapter24.WeightedGraph.relaxDist_le_walkWeight`,
  {lit}`CLRS.Chapter24.WeightedGraph.exists_walk_of_relaxDist`,
  {lit}`CLRS.Chapter24.WeightedGraph.NoNegCycle`,
  {lit}`CLRS.Chapter24.WeightedGraph.exists_simple_le`,
  {lit}`CLRS.Chapter24.WeightedGraph.IsShortestDist`,
  {lit}`CLRS.Chapter24.WeightedGraph.relaxDist_isShortestDist`,
  {lit}`CLRS.Chapter24.WeightedGraph.relaxDist_stabilizes`,
  and {lit}`CLRS.Chapter24.WeightedGraph.bellmanFordWork_le`.

* 24.2 Single-source shortest paths in directed acyclic graphs.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.IsTopoOrder`,
  {lit}`CLRS.Chapter24.WeightedGraph.isAcyclic_of_isTopoOrder`,
  {lit}`CLRS.Chapter24.WeightedGraph.relaxFrom`,
  {lit}`CLRS.Chapter24.WeightedGraph.dagRelax`,
  {lit}`CLRS.Chapter24.WeightedGraph.dagRelax_respects_edge`,
  {lit}`CLRS.Chapter24.WeightedGraph.dagRelax_isShortestDist`,
  {lit}`CLRS.Chapter24.WeightedGraph.sum_outdegree`,
  and {lit}`CLRS.Chapter24.WeightedGraph.dagSSSPWork_eq`.

* 24.3 Dijkstra's algorithm.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.Nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.noNegCycle_of_nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.walkWeight_nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.exists_crossing`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstra_extractMin_correct`,
  {lit}`CLRS.Chapter24.WeightedGraph.DijkstraState`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraInit`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraInit_invariant`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraStep_invariant`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraLoop`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraLoop_invariant`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraLoop_finish`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstraLoop_correct`,
  and {lit}`CLRS.Chapter24.WeightedGraph.dijkstraWork_le_edge_log`.

* 24.4 Difference constraints and shortest paths.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.DiffConstraintSystem`,
  {lit}`CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.IsFeasible`,
  {lit}`CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.constraintGraph`,
  {lit}`CLRS.Chapter24.WeightedGraph.le_add_walkWeight_of_potential`,
  {lit}`CLRS.Chapter24.WeightedGraph.relaxDist_respects_edge`,
  {lit}`CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.noNegCycle_of_feasible`,
  {lit}`CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.feasible_of_noNegCycle`,
  and {lit}`CLRS.Chapter24.WeightedGraph.DiffConstraintSystem.diffConstraint_feasible_iff_noNegCycle`.

## Current Shape

Section 24.1 defines a {lit}`WeightedGraph` as a finite edge set plus a real weight
function, defines walks and walk weights, and models Bellman-Ford as a
synchronous relaxation dynamic program {lit}`relaxDist` valued in {lit}`WithTop ℝ`.  It
proves the upper-bound property ({lit}`relaxDist_le_walkWeight`), realizability of
finite estimates by walks ({lit}`exists_walk_of_relaxDist`), the cycle-removal
shortening lemma under {lit}`NoNegCycle` ({lit}`exists_simple_le`), and, as the headline,
CLRS Theorem 24.4: after {lit}`|V| - 1` rounds the estimates equal the single-source
shortest-path distances {lit}`δ(s, ·)` characterized by {lit}`IsShortestDist`
({lit}`relaxDist_isShortestDist`), together with convergence
({lit}`relaxDist_stabilizes`) and the {lit}`(|V| - 1)·|E| ≤ |V|·|E|` = {lit}`O(V·E)` work bound
({lit}`bellmanFordWork_le`).

Section 24.3 adds Dijkstra's algorithm under nonnegative edge weights.  It shows
nonnegative weights imply {lit}`NoNegCycle` (so Section 24.1's {lit}`δ` applies),
that a walk from a settled to an unsettled vertex crosses the settled frontier
({lit}`exists_crossing`), and proves CLRS Theorem 24.6, the greedy invariant
({lit}`dijkstra_extractMin_correct`): the unsettled vertex of minimum tentative
distance already has the exact shortest-path distance.  It also records the
{lit}`(|V| + |E|)·log|V|` = {lit}`O(E log V)` binary-heap work decomposition
({lit}`dijkstraWork_le_edge_log`).  The file defines an executable state/step/loop
skeleton: {lit}`dijkstraInit` pre-settles the source with distance 0 and pre-relaxes
its outgoing edges so that {lit}`DijkstraInvariant` holds from the start
({lit}`dijkstraInit_invariant`); one-step invariant preservation
({lit}`dijkstraStep_invariant`) lifts the invariant through {lit}`dijkstraLoop`
({lit}`dijkstraLoop_invariant`); and the end-to-end correctness theorem
({lit}`dijkstraLoop_correct`) proves that after {lit}`|V|` iterations every vertex
has its exact shortest-path distance.

Section 24.2 formalizes CLRS's {lit}`DAG-SHORTEST-PATHS`.  It restates the
topological-order predicate over {lit}`WeightedGraph.Adj` ({lit}`IsTopoOrder`), shows a
topological order forces acyclicity ({lit}`isAcyclic_of_isTopoOrder`), and models
the algorithm as a fold of the single-vertex out-edge relaxation {lit}`relaxFrom`
along the order ({lit}`dagRelax`).  The headline is CLRS §24.2 correctness
({lit}`dagRelax_isShortestDist`): a single left-to-right pass already yields
{lit}`δ(s, ·)` characterized by {lit}`IsShortestDist`, obtained from the per-edge upper
bound ({lit}`dagRelax_respects_edge`) telescoped along walks plus realizability.  The
{lit}`|V| + |E|` = {lit}`Θ(V + E)` work count ({lit}`sum_outdegree`, {lit}`dagSSSPWork_eq`)
records that each vertex and each edge is touched exactly once.

Section 24.4 formalizes the connection between difference constraints and shortest
paths (CLRS §24.4).  It defines a {lit}`DiffConstraintSystem` as a finite set of
inequalities {lit}`x_j ≤ x_i + b`, builds the constraint graph
({lit}`constraintGraph`) as a {lit}`WeightedGraph` with a fresh source, proves
the general potential-function lemma
({lit}`le_add_walkWeight_of_potential`) and the Bellman-Ford triangle
inequality ({lit}`relaxDist_respects_edge`), and establishes **CLRS
Theorem 24.9** ({lit}`diffConstraint_feasible_iff_noNegCycle`):
feasibility {lit}`↔` no negative-weight cycle, with the explicit
Bellman-Ford solution {lit}`x i = δ(s, i)`.

## Deferred Work

* Per-edge relaxation ordering and mutable/RAM cost refinement of the abstract
  synchronous relaxation model.

The advertised Bellman-Ford correctness/work chain (Section 24.1), the
DAG-shortest-paths correctness and {lit}`Θ(V + E)` work bound (Section 24.2), the
Dijkstra greedy theorem, executable loop with end-to-end correctness, and
abstract work bound (Section 24.3), and the difference-constraint feasibility
characterisation (Section 24.4) are proved.
-/

namespace CLRS
namespace Chapter24

end Chapter24
end CLRS
