import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.SparseExecution.Timeline

/-!
# Counted BFS parent recovery

The search binds one support-BFS result, tests its stored sink distance, and
follows that result's stored parents. The shortest-path proof describes the
recovered list; it does not choose a second shortest path or rerun BFS.
-/
noncomputable section
namespace CLRS.Chapter26.SparseEK
open Finset Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

def reverseParents (parent : V → Option V) : Nat → V → CostedPathVertices V
  | 0, v => ⟨[v],1⟩
  | d+1, v =>
    match parent v with
    | none => ⟨[v],2⟩
    | some u =>
      let old := reverseParents parent d u
      ⟨v :: old.vertices, old.work + 2⟩

def recoverParents (parent : V → Option V) (d : Nat) (v : V) : CostedPathVertices V :=
  let old := reverseParents parent d v
  ⟨old.vertices.reverse, old.work + old.vertices.length⟩

omit [Fintype V] [DecidableEq V] in
theorem reverseParents_spec {parent : V → Option V} {s v : V} {d : Nat}
    (hp : BFSParentPath parent s v d) :
    (reverseParents parent d v).vertices = hp.vertices.reverse ∧
      (reverseParents parent d v).work = 2*d+1 := by
  induction hp with
  | root => simp [reverseParents, BFSParentPath.vertices]
  | @tail u v d hp hpar ih =>
    simp [reverseParents, hpar, BFSParentPath.vertices, ih, Nat.mul_add, Nat.add_assoc]

theorem recoverParents_spec {parent : V → Option V} {s v : V} {d : Nat}
    (hp : BFSParentPath parent s v d) :
    (recoverParents parent d v).vertices = hp.vertices ∧
      (recoverParents parent d v).work = 3*d+2 := by
  have hs := reverseParents_spec hp
  simp [recoverParents, hs.1, hs.2, BFSParentPath.vertices_length]
  omega

theorem shortest_length_support (φ : Flow V G) (p : ShortestAugmentingPath φ) :
    p.path.edges.length ≤ (support G).card := by
  have hv : p.path.vertices.toFinset ⊆ (residualBFS φ).visited := by
    intro v h
    obtain ⟨i,hi,hv⟩ := List.getElem_of_mem (List.mem_toFinset.mp h)
    have hr := (p.shortest_prefix i hi).1.reachable
    apply (residualBFS_visited_iff_reachable φ v).2
    simpa [hv] using hr
  have hc := Finset.card_le_card hv
  rw [List.toFinset_card_of_nodup p.path.nodup] at hc
  have hs := Finset.card_le_card (residualBFS_visited_subset φ)
  have hi := Finset.card_insert_le G.s ((support G).image Prod.snd)
  have him := Finset.card_image_le (s := support G) (f := Prod.snd)
  rw [Flow.ResidualPath.edges_length]
  omega

/-- Recover the shortest path from the supplied saved BFS state. -/
def recoveredShortest (φ : Flow V G) (b : CostedBFSRun V)
    (hb : b.state = residualBFS φ) (d : Nat) (hd : b.state.distance G.t = some d) :
    ShortestAugmentingPath φ × Nat :=
  let recovered := recoverParents b.state.parent d G.t
  let inv : BFSDistanceInvariant φ G.s b.state := hb.symm ▸ residualBFS_distanceInvariant φ
  let hp := inv.parentPath_of_distance hd
  have hv : recovered.vertices = hp.vertices := (recoverParents_spec hp).1
  let path : Flow.AugmentingPath φ :=
    { vertices := recovered.vertices
      chain := hv ▸ hp.vertices_chain inv
      head_eq := hv ▸ hp.vertices_head
      last_eq := hv ▸ hp.vertices_getLast
      nodup := hv ▸ hp.vertices_nodup inv }
  have hlen : path.edges.length = d := by
    rw [Flow.ResidualPath.edges_length]
    change recovered.vertices.length - 1 = d
    rw [hv, BFSParentPath.vertices_length]
    omega
  (⟨path, by
    rw [hlen]
    exact (bfsState_distance_eq_some_iff φ G.t).1 (by simpa [hb] using hd)⟩,
    recovered.work)

theorem recoveredShortest_work (φ : Flow V G) (b : CostedBFSRun V)
    (hb : b.state = residualBFS φ) (d : Nat) (hd : b.state.distance G.t = some d) :
    (recoveredShortest φ b hb d hd).2 = 3*d+2 := by
  exact (recoverParents_spec ((hb.symm ▸ residualBFS_distanceInvariant φ).parentPath_of_distance hd)).2

theorem recoveredShortest_length (φ : Flow V G) (b : CostedBFSRun V)
    (hb : b.state = residualBFS φ) (d : Nat) (hd : b.state.distance G.t = some d) :
    (recoveredShortest φ b hb d hd).1.path.edges.length = d := by
  simp only [recoveredShortest, Flow.ResidualPath.edges_length]
  rw [(recoverParents_spec ((hb.symm ▸ residualBFS_distanceInvariant φ).parentPath_of_distance hd)).1,
    BFSParentPath.vertices_length]
  omega

structure SearchResult (φ : Flow V G) where
  path : Option (ShortestAugmentingPath φ)
  work : Nat

def search (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (φ : Flow V G) : SearchResult φ :=
  let b := costedResidualBFS A φ
  have hb : b.state = residualBFS φ := costedResidualBFS_state A φ (hA ▸ input.covers φ)
  match hd : b.state.distance G.t with
  | none => ⟨none,b.work+1⟩
  | some d =>
    let p := recoveredShortest φ b hb d hd
    ⟨some p.1,b.work+1+p.2⟩

theorem search_none_iff (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (φ : Flow V G) :
    (search input A hA φ).path = none ↔ ¬ φ.hasAugmentingPath := by
  have hb := costedResidualBFS_state A φ (hA ▸ input.covers φ)
  simp only [search]
  split
  · rename_i hd
    have hd' : (residualBFS φ).distance G.t = none := by simpa [hb] using hd
    simp only [true_iff]
    intro h
    obtain ⟨d,he⟩ := (bfsState_distance_defined_iff_reachable φ G.t).2 h
    simp [hd'] at he
  · rename_i d hd
    have hd' : (residualBFS φ).distance G.t = some d := by simpa [hb] using hd
    simp only [Option.some_ne_none, false_iff, not_not]
    exact (bfsState_distance_defined_iff_reachable φ G.t).1 ⟨d,hd'⟩

theorem search_work_of_none (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (φ : Flow V G)
    (hn : (search input A hA φ).path = none) :
    (search input A hA φ).work = (costedResidualBFS A φ).work+1 := by
  simp only [search] at *
  split at hn <;> simp_all

theorem search_work_le (input : CapacityInput G) (A : SupportAdjacency V)
    (hA : A = (prepare input.arcs).adjacency) (φ : Flow V G) :
    (search input A hA φ).work ≤ 4 + 8 * (support G).card := by
  have hb : (costedResidualBFS A φ).work ≤ 1 + 5 * (support G).card := by
    simpa [hA] using bfs_work_le input φ
  simp only [search]
  split
  · dsimp only
    omega
  · rename_i d hd
    rw [recoveredShortest_work]
    have hp := shortest_length_support φ
      (recoveredShortest φ (costedResidualBFS A φ)
        (costedResidualBFS_state A φ (hA ▸ input.covers φ)) d hd).1
    rw [recoveredShortest_length] at hp
    dsimp only
    omega

end CLRS.Chapter26.SparseEK
