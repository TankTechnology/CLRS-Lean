import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford
import CLRSLean.Chapter_24.Section_24_3_Dijkstra

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

* 24.3 Dijkstra's algorithm.
  Main declarations:
  {lit}`CLRS.Chapter24.WeightedGraph.Nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.noNegCycle_of_nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.walkWeight_nonneg`,
  {lit}`CLRS.Chapter24.WeightedGraph.exists_crossing`,
  {lit}`CLRS.Chapter24.WeightedGraph.dijkstra_extractMin_correct`,
  and {lit}`CLRS.Chapter24.WeightedGraph.dijkstraWork_le_edge_log`.

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
({lit}`dijkstraWork_le_edge_log`).

## Deferred Work

* The executable Dijkstra priority-queue loop that threads the settled set and
  tentative distances (Section 24.3 proves the greedy invariant that makes such
  a loop correct; the concrete loop/state is a separate refinement).
* SSSP in DAGs (Section 24.2) and difference constraints (Section 24.4).
* Per-edge relaxation ordering and mutable/RAM cost refinement of the abstract
  synchronous relaxation model.

The advertised Bellman-Ford correctness/work chain (Section 24.1) and the
Dijkstra greedy-invariant correctness and work bound (Section 24.3) are complete
for the current abstract-cost model, consistent with the Chapter 22 and
Chapter 23 graph track.
-/

namespace CLRS
namespace Chapter24

end Chapter24
end CLRS
