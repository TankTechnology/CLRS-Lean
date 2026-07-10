import CLRSLean.Chapter_22.Section_22_1_Representing_Graphs
import CLRSLean.Chapter_22.Section_22_2_BFS
import CLRSLean.Chapter_22.Section_22_3_DFS
import CLRSLean.Chapter_22.Section_22_3_DFS_WhitePath
import CLRSLean.Chapter_22.Section_22_3_DFS_Intervals
import CLRSLean.Chapter_22.Section_22_3_DFS_SCC
import CLRSLean.Chapter_22.Section_22_3_DFS_Bridge
import CLRSLean.Chapter_22.Section_22_3_DFS_EdgeClassification
import CLRSLean.Chapter_22.Section_22_4_Topological_Sort
import CLRSLean.Chapter_22.Section_22_5_MergeSort_Congr
import CLRSLean.Chapter_22.Section_22_5_Strongly_Connected_Components

/-! # Chapter 22 - Elementary Graph Algorithms

Chapter 22 introduces the finite-graph model used by the rest of the graph
algorithm track.  The current development proves CLRS BFS shortest-distance and
predecessor-tree correctness, establishes the DFS color/timestamp/white-path
theory needed by later graph algorithms, proves both Kahn and DFS topological
sort correct for DAGs, and proves full functional correctness of Kosaraju's SCC
algorithm.

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
  {lit}`CLRS.Chapter22.Graph.bfs_complete`,
  {lit}`CLRS.Chapter22.Graph.bfsState`,
  {lit}`CLRS.Chapter22.Graph.bfsState_distance_eq_some_iff`,
  {lit}`CLRS.Chapter22.Graph.bfsState_isBFSPredecessorTree`,
  and {lit}`CLRS.Chapter22.Graph.bfsState_correct`.

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
  {lit}`CLRS.Chapter22.Graph.intervalNestedInside_dfs_iff_ancestor`,
  {lit}`CLRS.Chapter22.Graph.DFSEdgeKind`,
  {lit}`CLRS.Chapter22.Graph.dfs_edge_classification_unique`,
  {lit}`CLRS.Chapter22.Graph.dfs_tree_or_forward_edge_iff_timestamps`,
  {lit}`CLRS.Chapter22.Graph.dfs_back_edge_iff_timestamps`,
  {lit}`CLRS.Chapter22.Graph.dfs_cross_edge_iff_timestamps`,
  {lit}`CLRS.Chapter22.Graph.dfs_undirected_edge_tree_or_back`,
  and {lit}`CLRS.Chapter22.Graph.exists_discovery_state`.

* 22.4 Topological sort.
  Main declarations:
  {lit}`CLRS.Chapter22.Graph.IsDAG`,
  {lit}`CLRS.Chapter22.Graph.indegree`,
  {lit}`CLRS.Chapter22.Graph.IsTopologicalOrder`,
  {lit}`CLRS.Chapter22.Graph.topologicalSort`,
  {lit}`CLRS.Chapter22.Graph.topologicalSort_isTopologicalOrder`,
  {lit}`CLRS.Chapter22.Graph.dfs_finish_time_decreases_on_dag_edge`,
  {lit}`CLRS.Chapter22.Graph.dfsTopologicalSort`,
  and {lit}`CLRS.Chapter22.Graph.dfsTopologicalSort_isTopologicalOrder`.

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
  and parent-edge infrastructure and proves the DFS parenthesis theorem plus
  the nesting-to-ancestor direction.
* {lit}`Section_22_3_DFS_Bridge` connects local discovery states to the final DFS
  timestamps used by the SCC proof.
* {lit}`Section_22_3_DFS_SCC` packages maximum-finish and first-discovery facts.
* {lit}`Section_22_3_DFS_EdgeClassification` proves the unique
  tree/back/forward/cross classification, its CLRS timestamp characterizations,
  and the undirected tree-or-back theorem.
* {lit}`Section_22_5_MergeSort_Congr` supplies the comparison congruence used for
  Kosaraju's decreasing-finish-time order.

## Current Shape

Section 22.1 establishes the public graph vocabulary.  Section 22.2 proves that
BFS is sound and complete for reachability, that its distance labels are exact
unweighted shortest-path lengths, and that its parent pointers form a rooted
predecessor tree over exactly the reachable vertices.  Section 22.3 gives a functional DFS model,
proves its global color and timestamp invariants, proves the white-path
characterization used by the SCC development, and proves that final DFS
timestamp intervals are disjoint or nested and that strict nesting is equivalent
to proper ancestry in the final parent forest; every graph edge is then uniquely
classified as tree, back, forward, or cross.  Section 22.4 implements both
Kahn's algorithm and CLRS's decreasing-DFS-finish-time algorithm, and proves
that each returns a valid topological order for every DAG.
Section 22.5 proves the SCC finish-time ordering, proves that each component
collected by Kosaraju is strongly connected and maximal, and concludes that the
returned components form an SCC partition of the vertex set.

## Deferred Work

* Algorithm-cost refinements: explicit work measures for the fuelled and
  classically selected functional implementations.

All advertised Chapter 22 algorithm-correctness chains are complete.  The
remaining work is executable-cost refinement rather than a functional
correctness gap.
-/

namespace CLRS
namespace Chapter22

end Chapter22
end CLRS
