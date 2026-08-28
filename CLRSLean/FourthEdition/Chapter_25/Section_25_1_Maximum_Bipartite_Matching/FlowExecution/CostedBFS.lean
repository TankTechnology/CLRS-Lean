import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS.CostedSupportBFS
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.ResidualSupport
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S5_Residual_Translation

/-!
# Costed residual BFS for matching flows

This file specializes support-indexed residual BFS to the bipartite matching
network.  It also recovers the parent chain produced by that same BFS run and
translates that concrete residual path to a graph augmenting path.  No second
reachability search or arbitrary path choice occurs in the translation.
-/

namespace CLRS

open Finset Classical

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The precomputed matching-flow adjacency covers the residual edges of
every matching state. -/
theorem matchingFlowSupportsResidual {G : BipartiteGraph V}
    (M : Matching V G) :
    SupportsResidual (matchingFlowAdjacency G).adjacency (matchingToFlow M) := by
  intro u v hres
  rw [matchingFlowAdjacency, mem_buildSupportAdjacency]
  exact matchingFlowResidualSupport_covers M hres

/-- Matching residual BFS over an already-built support adjacency. -/
noncomputable def matchingCostedBFSWith {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G) :
    CostedBFSRun (V ⊕ Bool) :=
  costedResidualBFS A (matchingToFlow M)

theorem matchingCostedBFSWith_state {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) :
    (matchingCostedBFSWith A M).state = residualBFS (matchingToFlow M) := by
  exact costedResidualBFS_state A _ cover

theorem matchingCostedBFSWith_work_le {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) :
    (matchingCostedBFSWith A M).work ≤ flowVertexCount V + 4 * A.storage := by
  simpa [matchingCostedBFSWith, flowVertexCount] using
    costedResidualBFS_work_le A (matchingToFlow M) cover

theorem matchingCostedBFSWith_distance {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    (residualBFS (matchingToFlow M)).distance (Sum.inr false) = some d := by
  rw [← matchingCostedBFSWith_state A M cover]
  exact hd

/-- One support-indexed BFS execution for the residual network of `M`. -/
noncomputable def matchingCostedBFS {G : BipartiteGraph V} (M : Matching V G) :
    CostedBFSRun (V ⊕ Bool) :=
  matchingCostedBFSWith (matchingFlowAdjacency G).adjacency M

/-- Erasing the counter gives the established semantic residual BFS state. -/
theorem matchingCostedBFS_state {G : BipartiteGraph V} (M : Matching V G) :
    (matchingCostedBFS M).state = residualBFS (matchingToFlow M) := by
  exact costedResidualBFS_state _ _ (matchingFlowSupportsResidual M)

/-- The actual bucket-scanning execution is linear in the flow vertices and
the two orientations of each capacity-support arc. -/
theorem matchingCostedBFS_work_le {G : BipartiteGraph V} (M : Matching V G) :
    (matchingCostedBFS M).work ≤ flowVertexCount V + 8 * flowArcCount G := by
  have h := costedResidualBFS_work_le (matchingFlowAdjacency G).adjacency
    (matchingToFlow M) (matchingFlowSupportsResidual M)
  rw [matchingFlowAdjacency_storage] at h
  change (matchingCostedBFS M).work ≤
    Fintype.card (V ⊕ Bool) + 8 * flowArcCount G
  change (costedResidualBFS (matchingFlowAdjacency G).adjacency
    (matchingToFlow M)).work ≤ _
  omega

/-- Transport a sink-distance observation from the costed state to the
semantic residual BFS state. -/
theorem matchingCostedBFS_distance {G : BipartiteGraph V} (M : Matching V G)
    {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    (residualBFS (matchingToFlow M)).distance (Sum.inr false) = some d := by
  rw [← matchingCostedBFS_state M]
  exact hd

/-- The exact residual parent path recovered from a matching BFS run,
together with the work used to build its vertex list. -/
structure MatchingBFSPathRecovery {G : BipartiteGraph V} (M : Matching V G)
    where
  path : Flow.ResidualPath (matchingToFlow M) (Sum.inr true) (Sum.inr false)
  work : Nat

/-- Recover a parent path from a BFS over an explicitly supplied, already
built support adjacency. -/
noncomputable def matchingBFSPathRecoveryWith {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    MatchingBFSPathRecovery M := by
  let hd' := matchingCostedBFSWith_distance A M cover hd
  let invariant := residualBFS_distanceInvariant (matchingToFlow M)
  let parentPath := invariant.parentPath_of_distance hd'
  let recovered := BFSParentPath.verticesWithCost parentPath
  exact
    { path :=
        { vertices := recovered.vertices
          chain := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_chain invariant
          head_eq := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_head
          last_eq := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_getLast
          nodup := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_nodup invariant }
      work := recovered.work }

theorem matchingBFSPathRecoveryWith_work {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    (matchingBFSPathRecoveryWith A M cover hd).work = 2 * (d + 1) := by
  simp [matchingBFSPathRecoveryWith, BFSParentPath.verticesWithCost_work]

theorem matchingBFSPathRecoveryWith_work_le {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    (matchingBFSPathRecoveryWith A M cover hd).work ≤
      2 * flowVertexCount V := by
  rw [matchingBFSPathRecoveryWith_work]
  let parentPath :=
    (residualBFS_distanceInvariant (matchingToFlow M)).parentPath_of_distance
      (matchingCostedBFSWith_distance A M cover hd)
  have hnodup := parentPath.vertices_nodup
    (residualBFS_distanceInvariant (matchingToFlow M))
  have hlength : (BFSParentPath.vertices parentPath).length = d + 1 :=
    by simpa [parentPath] using BFSParentPath.vertices_length (h := parentPath)
  have hcard : (BFSParentPath.vertices parentPath).length ≤
      Fintype.card (V ⊕ Bool) :=
    List.Nodup.length_le_card hnodup
  rw [hlength] at hcard
  simpa [flowVertexCount] using Nat.mul_le_mul_left 2 hcard

/-- Recover the source-to-sink parent chain selected by the same costed BFS
state.  List construction uses cons followed by one reversal. -/
noncomputable def matchingBFSPathRecovery {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    MatchingBFSPathRecovery M := by
  let hd' := matchingCostedBFS_distance M hd
  let invariant := residualBFS_distanceInvariant (matchingToFlow M)
  let parentPath := invariant.parentPath_of_distance hd'
  let recovered := BFSParentPath.verticesWithCost parentPath
  exact
    { path :=
        { vertices := recovered.vertices
          chain := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_chain invariant
          head_eq := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_head
          last_eq := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_getLast
          nodup := by
            rw [BFSParentPath.verticesWithCost_vertices]
            exact parentPath.vertices_nodup invariant }
      work := recovered.work }

/-- The recovered list is definitionally tied, modulo the verified erasure,
to the semantic BFS parent chain. -/
theorem matchingBFSPathRecovery_vertices {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    (matchingBFSPathRecovery M hd).path.vertices =
      BFSParentPath.vertices
        ((residualBFS_distanceInvariant (matchingToFlow M)).parentPath_of_distance
          (matchingCostedBFS_distance M hd)) := by
  simp [matchingBFSPathRecovery, BFSParentPath.verticesWithCost_vertices]

/-- Exact work charged for parent-chain construction and final reversal. -/
theorem matchingBFSPathRecovery_work {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    (matchingBFSPathRecovery M hd).work = 2 * (d + 1) := by
  simp [matchingBFSPathRecovery, BFSParentPath.verticesWithCost_work]

/-- Parent recovery is linear in the flow-network vertex count. -/
theorem matchingBFSPathRecovery_work_le {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    (matchingBFSPathRecovery M hd).work ≤ 2 * flowVertexCount V := by
  rw [matchingBFSPathRecovery_work]
  let parentPath :=
    (residualBFS_distanceInvariant (matchingToFlow M)).parentPath_of_distance
      (matchingCostedBFS_distance M hd)
  have hnodup := parentPath.vertices_nodup
    (residualBFS_distanceInvariant (matchingToFlow M))
  have hlength : (BFSParentPath.vertices parentPath).length = d + 1 :=
    by simpa [parentPath] using BFSParentPath.vertices_length (h := parentPath)
  have hcard : (BFSParentPath.vertices parentPath).length ≤ Fintype.card (V ⊕ Bool) :=
    List.Nodup.length_le_card hnodup
  rw [hlength] at hcard
  simpa [flowVertexCount] using Nat.mul_le_mul_left 2 hcard

/-- A concrete residual source-to-sink path in the matching network induces
a graph augmenting path.  The proof consumes the supplied path itself; it
does not replace it with a separately chosen reachability witness. -/
theorem augmentingPathProjection_of_residualPath {G : BipartiteGraph V}
    (M : Matching V G)
    (q : Flow.ResidualPath (matchingToFlow M) (Sum.inr true) (Sum.inr false)) :
    ∃ p : List V, IsAugmentingPath G M p ∧
      p = projectGraphVertices q.vertices := by
  cases hq : q.vertices with
  | nil =>
      have hhead := q.head_eq
      simp [hq] at hhead
  | cons x rest =>
      have hq0 : x = Sum.inr true := by
        simpa [hq] using q.head_eq
      subst x
      cases rest with
      | nil =>
          have hend := q.last_eq
          simp [hq] at hend
      | cons y rest' =>
          have hstep0 :
              Flow.residualEdge (matchingToFlow M) (Sum.inr true) y := by
            have hc := (List.isChain_iff_getElem.mp q.chain) 0 (by simp [hq])
            simpa [hq, toFlowNetwork] using hc
          cases y with
          | inl l =>
              have ⟨hl, hlu⟩ :=
                (matchingToFlow_residualEdge_source M l).mp hstep0
              have hw : (Sum.inl l :: rest').IsChain
                  (Flow.residualEdge (matchingToFlow M)) := by
                have hchain := q.chain
                rw [List.isChain_iff_getElem] at hchain ⊢
                intro i hi
                have hc := hchain (i + 1) (by simp [hq] at hi ⊢; omega)
                simpa [hq, toFlowNetwork] using hc
              have hwnd : (Sum.inl l :: rest').Nodup := by
                have hnd := q.nodup
                rw [hq] at hnd
                exact hnd.of_cons
              have hw0 : (Sum.inl l :: rest')[0]? = some (Sum.inl l) := rfl
              have hwlast :
                  (Sum.inl l :: rest')[(Sum.inl l :: rest').length - 1]? =
                    some (Sum.inr false) := by
                have h1 :
                    (Sum.inr true :: Sum.inl l :: rest')[
                        (Sum.inr true :: Sum.inl l :: rest').length - 1]? =
                      (Sum.inl l :: rest')[(Sum.inl l :: rest').length - 1]? := by
                  simp [List.length_cons]
                have hend := q.last_eq
                rw [hq, List.getLast?_eq_getElem?, h1] at hend
                exact hend
              have hwns : Sum.inr true ∉ Sum.inl l :: rest' := by
                have hnd := q.nodup
                rw [hq, List.nodup_cons] at hnd
                exact hnd.1
              obtain ⟨p, hpn, hpe, hpge, hphead, hplast, hpfw, hpbw, -,
                hproject⟩ :=
                translation_inner M l hl (Sum.inl l :: rest') hw hwnd hw0
                  hwlast hwns
              have hpne : p ≠ [] := fun h => by simp [h] at hpge
              refine ⟨p, ?_, by simpa [projectGraphVertices] using hproject⟩
              refine ⟨hpn, hpe, hpge, ?_, ?_, ?_, ?_, hpfw, hpbw⟩
              · intro h
                have h1 : p.head h = l := by
                  have h2 : p.head? = some (p.head h) :=
                    List.head?_eq_some_head _
                  rw [hphead] at h2
                  exact (Option.some.inj h2).symm
                rw [h1]
                exact hl
              · intro h r
                have h1 : p.head h = l := by
                  have h2 : p.head? = some (p.head h) :=
                    List.head?_eq_some_head _
                  rw [hphead] at h2
                  exact (Option.some.inj h2).symm
                rw [h1]
                exact hlu r
              · intro h
                have h1 : p.getLast? = some (p.getLast h) :=
                  List.getLast?_eq_some_getLast hpne
                exact (hplast _ h1).1
              · intro h l'
                have h1 : p.getLast? = some (p.getLast h) :=
                  List.getLast?_eq_some_getLast hpne
                exact (hplast _ h1).2 l'
          | inr b =>
              exact absurd hstep0
                (matchingToFlow_not_residualEdge_source_inr M b)

/-- The graph projection of a concrete matching residual path is itself an
augmenting path. -/
theorem projectGraphVertices_isAugmentingPath {G : BipartiteGraph V}
    (M : Matching V G)
    (q : Flow.ResidualPath (matchingToFlow M) (Sum.inr true) (Sum.inr false)) :
    IsAugmentingPath G M (projectGraphVertices q.vertices) := by
  obtain ⟨p, hp, hproject⟩ := augmentingPathProjection_of_residualPath M q
  simpa [hproject] using hp

/-- Compatibility existential form of the concrete residual-path
translation. -/
theorem augmentingPath_of_residualPath {G : BipartiteGraph V}
    (M : Matching V G)
    (q : Flow.ResidualPath (matchingToFlow M) (Sum.inr true) (Sum.inr false)) :
    ∃ p : List V, IsAugmentingPath G M p :=
  ⟨projectGraphVertices q.vertices,
    projectGraphVertices_isAugmentingPath M q⟩

/-- Result of the one-pass projection from residual-network vertices to graph
vertices. -/
structure CostedGraphPathProjection (V : Type*) where
  vertices : List V
  work : Nat

/-- Execute the graph-vertex projection, charging one case inspection per
residual-path vertex. -/
def projectGraphVerticesWithCost : List (V ⊕ Bool) →
    CostedGraphPathProjection V
  | [] => ⟨[], 0⟩
  | x :: rest =>
      let tail := projectGraphVerticesWithCost rest
      match x with
      | Sum.inl v => ⟨v :: tail.vertices, tail.work + 1⟩
      | Sum.inr _ => ⟨tail.vertices, tail.work + 1⟩

omit [Fintype V] [DecidableEq V] in
theorem projectGraphVerticesWithCost_vertices (w : List (V ⊕ Bool)) :
    (projectGraphVerticesWithCost w).vertices = projectGraphVertices w := by
  induction w with
  | nil => rfl
  | cons x rest ih =>
      cases x <;> simp [projectGraphVerticesWithCost, projectGraphVertices, ih]

omit [Fintype V] [DecidableEq V] in
theorem projectGraphVerticesWithCost_work (w : List (V ⊕ Bool)) :
    (projectGraphVerticesWithCost w).work = w.length := by
  induction w with
  | nil => rfl
  | cons x rest ih =>
      cases x <;> simp [projectGraphVerticesWithCost, ih]

/-- Execute graph projection for the path recovered from an explicitly
supplied, already-built support adjacency. -/
noncomputable def matchingBFSGraphProjectionWith {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    CostedGraphPathProjection V :=
  projectGraphVerticesWithCost
    (matchingBFSPathRecoveryWith A M cover hd).path.vertices

theorem matchingBFSGraphProjectionWith_isAugmenting {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    IsAugmentingPath G M
      (matchingBFSGraphProjectionWith A M cover hd).vertices := by
  rw [matchingBFSGraphProjectionWith, projectGraphVerticesWithCost_vertices]
  exact projectGraphVertices_isAugmentingPath M
    (matchingBFSPathRecoveryWith A M cover hd).path

/-- The graph projection from an explicitly indexed BFS run is linear in
the flow-network vertex count. -/
theorem matchingBFSGraphProjectionWith_work_le {G : BipartiteGraph V}
    (A : SupportAdjacency (V ⊕ Bool)) (M : Matching V G)
    (cover : SupportsResidual A (matchingToFlow M)) {d : Nat}
    (hd : (matchingCostedBFSWith A M).state.distance (Sum.inr false) = some d) :
    (matchingBFSGraphProjectionWith A M cover hd).work ≤
      flowVertexCount V := by
  rw [matchingBFSGraphProjectionWith, projectGraphVerticesWithCost_work]
  exact List.Nodup.length_le_card
    (matchingBFSPathRecoveryWith A M cover hd).path.nodup

/-- Execute the graph projection of the exact recovered matching-BFS path. -/
noncomputable def matchingBFSGraphProjection {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    CostedGraphPathProjection V :=
  projectGraphVerticesWithCost (matchingBFSPathRecovery M hd).path.vertices

theorem matchingBFSGraphProjection_isAugmenting {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    IsAugmentingPath G M (matchingBFSGraphProjection M hd).vertices := by
  rw [matchingBFSGraphProjection, projectGraphVerticesWithCost_vertices]
  exact projectGraphVertices_isAugmentingPath M
    (matchingBFSPathRecovery M hd).path

/-- The one-pass path projection is linear in the flow-network vertex count. -/
theorem matchingBFSGraphProjection_work_le {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    (matchingBFSGraphProjection M hd).work ≤ flowVertexCount V := by
  rw [matchingBFSGraphProjection, projectGraphVerticesWithCost_work]
  exact List.Nodup.length_le_card
    (matchingBFSPathRecovery M hd).path.nodup

/-- The exact parent path recovered from the costed BFS translates to a graph
augmenting path. -/
theorem augmentingPath_of_matchingBFSPathRecovery {G : BipartiteGraph V}
    (M : Matching V G) {d : Nat}
    (hd : (matchingCostedBFS M).state.distance (Sum.inr false) = some d) :
    ∃ p : List V, IsAugmentingPath G M p :=
  ⟨(matchingBFSGraphProjection M hd).vertices,
    matchingBFSGraphProjection_isAugmenting M hd⟩

end Matchings
end CLRS
