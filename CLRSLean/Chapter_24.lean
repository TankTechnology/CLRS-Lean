import CLRSLean.Chapter_24.Section_24_1_Bellman_Ford

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

## Deferred Work

* Dijkstra's algorithm (Section 24.3) and its {lit}`O(E log V)` binary-heap work
  bound.
* SSSP in DAGs (Section 24.2) and difference constraints (Section 24.4).
* Per-edge relaxation ordering and mutable/RAM cost refinement of the abstract
  synchronous relaxation model.

The advertised Bellman-Ford correctness and work-bound chain for Section 24.1 is
complete for the current abstract-cost model, consistent with the Chapter 22 and
Chapter 23 graph track.
-/

namespace CLRS
namespace Chapter24

end Chapter24
end CLRS
