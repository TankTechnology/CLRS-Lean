import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_2_BFS
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_WhitePath
import CLRSLean.Chapter_22.Section_22_3_DFS_Intervals
import CLRSLean.Chapter_22.Section_22_3_DFS_SCC
import CLRSLean.Chapter_22.Section_22_3_DFS_Bridge
import CLRSLean.Chapter_22.Section_22_4_Topological_Sort
import CLRSLean.Chapter_22.Section_22_5_MergeSort_Congr
import CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components

/-! # Chapter 22 - Elementary Graph Algorithms

Chapter 22 introduces the finite-graph model used by the rest of the graph
algorithm track.  The current development proves reachability correctness for
a fuelled BFS, establishes the DFS color/timestamp/white-path theory needed by
later graph algorithms, proves Kahn topological sort correct for DAGs, and
proves full functional correctness of Kosaraju's SCC algorithm.

The model intentionally mirrors the edge-list style used by CLRS pseudocode:
a finite vertex set plus an adjacency function gives a directed graph, and an
undirected graph is obtained by requiring symmetric adjacency.

## Sections

* 22.1 Representing graphs.
  Main definitions:
  {lit}`CLRS.Chapter22.Graph`,
  {lit}`CLRS.Chapter22.Graph.Adj`,
  {lit}`CLRS.Chapter22.Graph.IsWalk`,
  {lit}`CLRS.Chapter22.Graph.IsPath`,
  {lit}`CLRS.Chapter22.Graph.IsCycle`,
  {lit}`CLRS.Chapter22.Graph.Reachable`,
  {lit}`CLRS.Chapter22.Graph.ConnectedComponent`,
  {lit}`CLRS.Chapter22.Graph.reachable_refl`,
  {lit}`CLRS.Chapter22.Graph.reachable_trans`,
  and {lit}`CLRS.Chapter22.Graph.reachable_adj`.

* 22.2 Breadth-first search.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.bfsAux`,
  {lit}`CLRS.Chapter22.Graph.bfs`,
  {lit}`CLRS.Chapter22.Graph.BFSInvariant`,
  {lit}`CLRS.Chapter22.Graph.bfsInvariant_step`,
  {lit}`CLRS.Chapter22.Graph.bfsAux_sound`,
  {lit}`CLRS.Chapter22.Graph.bfs_sound`,
  and {lit}`CLRS.Chapter22.Graph.bfs_complete`.

* 22.3 Depth-first search.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.DFSState`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit`,
  {lit}`CLRS.Chapter22.Graph.dfs`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_blackens_u`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_preserves_black`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_no_new_gray`,
  {lit}`CLRS.Chapter22.Graph.dfs_all_black`,
  {lit}`CLRS.Chapter22.Graph.dfsVisit_blackens_iff_whiteReachable`,
  {lit}`CLRS.Chapter22.Graph.dfs_parenthesis`,
  {lit}`CLRS.Chapter22.Graph.dfs_intervals_not_cross`,
  {lit}`CLRS.Chapter22.Graph.IsDFSAncestor_reachable`,
  and {lit}`CLRS.Chapter22.Graph.exists_discovery_state`.

* 22.4 Topological sort.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.IsDAG`,
  {lit}`CLRS.Chapter22.Graph.indegree`,
  {lit}`CLRS.Chapter22.Graph.IsTopologicalOrder`,
  {lit}`CLRS.Chapter22.Graph.topologicalSort`,
  and {lit}`CLRS.Chapter22.Graph.topologicalSort_isTopologicalOrder`.

* 22.5 Strongly connected components.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.transpose`,
  {lit}`CLRS.Chapter22.Graph.StronglyConnected`,
  {lit}`CLRS.Chapter22.Graph.IsSCC`,
  {lit}`CLRS.Chapter22.Graph.IsSCCPartition`,
  {lit}`CLRS.Chapter22.Graph.dfsFromListCollect`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents`,
  {lit}`CLRS.Chapter22.Graph.scc_finish_time_order`,
  {lit}`CLRS.Chapter22.Graph.scc_finish_order`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_eq_sccs`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_subset`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_pairwise_disjoint`,
  {lit}`CLRS.Chapter22.Graph.kosarajuComponents_cover`,
  and {lit}`CLRS.Chapter22.Graph.kosarajuComponents_isSCCPartition`.

## Supporting DFS modules

The DFS proof is split by responsibility so downstream developments can import
only the layer they need:

* {lit}`Section_22_3_DFS_WhitePath` develops finite white reachability and proves
  that a sufficiently fuelled visit blackens exactly the white-reachable set.
* {lit}`Section_22_3_DFS_Intervals` develops timestamp, discovery-state, ancestor,
  and parent-edge infrastructure and proves the DFS parenthesis theorem.
* {lit}`Section_22_3_DFS_Bridge` connects local discovery states to the final DFS
  timestamps used by the SCC proof.
* {lit}`Section_22_3_DFS_SCC` packages maximum-finish and first-discovery facts.
* {lit}`Section_22_5_MergeSort_Congr` supplies the comparison congruence used for
  Kosaraju's decreasing-finish-time order.

## Current Shape

Section 22.1 establishes the public graph vocabulary.  Section 22.2 proves that
BFS is both sound (only reachable vertices are reported) and complete (every
reachable vertex is reported).  Section 22.3 gives a functional DFS model,
proves its global color and timestamp invariants, proves the white-path
characterization used by the SCC development, and proves that final DFS
timestamp intervals are disjoint or nested.  Section 22.4 implements Kahn's
algorithm and proves that it returns a valid topological order for every DAG.
Section 22.5 proves the SCC finish-time ordering, proves that each component
collected by Kosaraju is strongly connected and maximal, and concludes that the
returned components form an SCC partition of the vertex set.

## Deferred Work

* Section 22.2: unweighted shortest-path distances and predecessor-tree
  correctness; the current BFS theorem characterizes reachability only.
* Section 22.3: connect strict interval nesting to the parent-forest ancestor
  relation and prove tree/back/forward/cross edge classification.  The timestamp
  parenthesis theorem itself is complete.
* Section 22.4: a DFS finish-time implementation and correctness theorem matching
  the CLRS presentation; the current proved implementation is Kahn's algorithm.
* Algorithm-cost refinements: explicit work measures for the fuelled and
  classically selected functional implementations.

Kosaraju SCC correctness is no longer deferred.  The remaining work is textbook
coverage and executable-cost refinement rather than a gap in the SCC algorithm.
-/

namespace CLRS
namespace Chapter22

end Chapter22
end CLRS
