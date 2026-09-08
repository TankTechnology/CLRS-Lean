import CLRSLean.FourthEdition.Chapter_22.Section_22_5_Shortest_Path_Properties
import CLRSLean.FourthEdition.Chapter_20.Section_20_2_BFS

/-!
# Constructed shortest-path predecessor trees

The constructor computes Bellman–Ford distances, retains edges tight for those
values, and runs the existing labelled BFS on that finite graph. It returns
the computed distances and the actual BFS parent/depth maps. No predecessor
certificate is supplied as input. First-discovery depth prevents cycles even
when the tight graph contains zero-weight directed cycles.

Under the same global absence-of-negative-cycles premise as Bellman–Ford,
shortest-walk prefix optimality proves that the tight graph spans exactly the
original reachable vertices. Every returned parent path uses original edges
and telescopes to the computed shortest distance. Source and unreachable
vertices have no parent; all other reachable vertices do.

This is a finite classical graph construction over real-valued distances,
using the existing noncomputable BFS representation. It adds no machine-runtime
claim or negative-cycle detector, and does not alter the older tight-only
predecessor selector.
-/

namespace CLRS.Chapter24.WeightedGraph
variable {V : Type} [Fintype V] [DecidableEq V] (G : WeightedGraph V)

/-- Keep precisely original edges tight for the computed Bellman–Ford values. -/
noncomputable def tightGraph (s : V) : CLRS.Chapter22.Graph V := by
  classical
  exact {
    vertices := Finset.univ
    adj := fun u => Finset.univ.filter (fun v => G.Adj u v ∧
      G.shortestDist s v = G.shortestDist s u + (G.w u v : WithTop ℝ))
    adj_sub := by intros; exact Finset.subset_univ _
    adj_outside := by intro v hv; simp at hv
  }

/-- The auxiliary graph retains every original carrier vertex. -/
@[simp] theorem tightGraph_vertices (s : V) : (G.tightGraph s).vertices = Finset.univ := rfl

/-- Auxiliary adjacency is exactly an original tight edge. -/
@[simp] theorem tightGraph_adj (s u v : V) : (G.tightGraph s).Adj u v ↔
    G.Adj u v ∧ G.shortestDist s v = G.shortestDist s u + (G.w u v : WithTop ℝ) := by
  classical
  simp [tightGraph, CLRS.Chapter22.Graph.Adj]

private theorem singleton_walk (s : V) : G.IsWalkFrom s s [s] :=
  ⟨by simp, rfl, rfl⟩

private theorem tight_reachable_has_walk {s v : V} (h : (G.tightGraph s).Reachable s v) :
    ∃ p, G.IsWalkFrom s v p := by
  induction h with
  | refl => exact ⟨[s], singleton_walk G s⟩
  | @tail u v h huv ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p ++ [v], IsWalkFrom.append_edge G hp ((G.tightGraph_adj s u v).mp huv).1⟩

private theorem shortest_walk_tight_reachable (hNC : G.NoNegCycle) (s : V) (p : List V) :
    ∀ v, G.IsWalkFrom s v p → (walkWeight G.w p : WithTop ℝ) = G.shortestDist s v →
      (G.tightGraph s).Reachable s v := by
  induction p using List.reverseRecOn with
  | nil => intro v hp; exact (IsWalkFrom.ne_nil G hp rfl).elim
  | append_singleton p x ih =>
    intro v hp hw
    have hx : x = v := by simpa using hp.last
    subst v
    by_cases hn : p = []
    · subst p
      have hs : x = s := by simpa using hp.head
      subst x
      exact .refl
    · let u := p.getLast hn
      have hlast : p.getLast? = some u := List.getLast?_eq_some_getLast hn
      have happ := List.isChain_append.mp hp.chain
      have hedge : G.Adj u x :=
        happ.2.2 u (Option.mem_def.mpr hlast) x (by simp)
      have hhead : p.head? = some s := by
        simpa only [List.head?_append_of_ne_nil _ hn] using hp.head
      have hprefix : G.IsWalkFrom s u p := ⟨happ.1, hhead, hlast⟩
      have hweight : walkWeight G.w (p ++ [x]) = walkWeight G.w p + G.w u x :=
        walkWeight_append_singleton G.w p hn x
      have hlower := G.shortestDist_le_walkWeight hNC s u p hprefix
      have htri := G.shortestDist_triangleInequality hNC s u x hedge
      have hprefix_short : (walkWeight G.w p : WithTop ℝ) = G.shortestDist s u := by
        apply le_antisymm
        · apply (WithTop.add_le_add_iff_right (WithTop.coe_ne_top : (G.w u x : WithTop ℝ) ≠ ⊤)).mp
          rw [← hw, hweight] at htri
          simpa only [WithTop.coe_add] using htri
        · exact hlower
      have htight : G.shortestDist s x = G.shortestDist s u + (G.w u x : WithTop ℝ) := by
        rw [← hw, hweight, ← hprefix_short, WithTop.coe_add]
      exact (G.tightGraph s).reachable_trans (ih u hprefix hprefix_short)
        ((G.tightGraph s).reachable_adj ((G.tightGraph_adj s u x).mpr ⟨hedge, htight⟩))

/-- The tight graph reaches exactly the vertices reachable in the weighted graph. -/
theorem tightGraph_reachable_iff (hNC : G.NoNegCycle) (s v : V) :
    (G.tightGraph s).Reachable s v ↔ ∃ p, G.IsWalkFrom s v p := by
  constructor
  · exact tight_reachable_has_walk G
  · intro hr
    obtain htop | ⟨p, hp, hw⟩ := (G.shortestDist_isShortestDist hNC s v).2
    · exact ((G.noPath_iff_top hNC s v).mp htop hr).elim
    · exact shortest_walk_tight_reachable G hNC s p v hp hw

/-- Distances and parent/depth maps returned by the constructed predecessor tree. -/
structure ShortestPathTreeResult (V : Type) where
  distance : V → WithTop ℝ
  parent : V → Option V
  depth : V → Option Nat

/-- Run labelled BFS on the tight graph of actual computed shortest-path distances. -/
noncomputable def shortestPathTree (s : V) : ShortestPathTreeResult V :=
  let labels := (G.tightGraph s).bfsState s (by simp)
  ⟨G.shortestDist s, labels.parent, labels.distance⟩

/-- The returned weighted distances are the computed Bellman–Ford values. -/
@[simp] theorem shortestPathTree_distance (s v : V) :
    (G.shortestPathTree s).distance v = G.shortestDist s v := rfl

/-- The returned source has no predecessor. -/
@[simp] theorem shortestPathTree_source_parent (s : V) :
    (G.shortestPathTree s).parent s = none :=
  (G.tightGraph s).bfsState_source_parent (by simp)

/-- The returned source has depth zero. -/
@[simp] theorem shortestPathTree_source_depth (s : V) :
    (G.shortestPathTree s).depth s = some 0 :=
  ((G.tightGraph s).bfsState_distanceInvariant (by simp)).source_distance

/-- Every returned parent is an original tight edge and decreases depth by one. -/
theorem shortestPathTree_parent_step (s : V) {u v : V}
    (hp : (G.shortestPathTree s).parent v = some u) :
    G.Adj u v ∧ G.shortestDist s v = G.shortestDist s u + (G.w u v : WithTop ℝ) ∧
    ∃ d, (G.shortestPathTree s).depth u = some d ∧
      (G.shortestPathTree s).depth v = some (d + 1) := by
  obtain ⟨he, d, hu, hv⟩ := (G.tightGraph s).bfsState_parent_spec (by simp) hp
  obtain ⟨he, ht⟩ := (G.tightGraph_adj s u v).mp he
  exact ⟨he, ht, d, hu, hv⟩

/-- Following a parent strictly decreases its natural-number depth. -/
theorem shortestPathTree_parent_depth_lt (s : V) {u v : V}
    (hp : (G.shortestPathTree s).parent v = some u) :
    ((G.shortestPathTree s).depth u).getD 0 < ((G.shortestPathTree s).depth v).getD 0 :=
  (G.tightGraph s).bfsState_parent_level_lt (by simp) hp

/-- The actual returned predecessor relation has no directed cycle. -/
theorem shortestPathTree_acyclic (s v : V) :
    ¬ Relation.TransGen (fun u w => (G.shortestPathTree s).parent w = some u) v v :=
  (G.tightGraph s).bfsState_parent_acyclic (by simp) v

/-- Exactly reachable non-source vertices receive a predecessor. -/
theorem shortestPathTree_parent_defined_iff (hNC : G.NoNegCycle) (s v : V) :
    (∃ u, (G.shortestPathTree s).parent v = some u) ↔
      (∃ p, G.IsWalkFrom s v p) ∧ v ≠ s := by
  simpa only [shortestPathTree, G.tightGraph_reachable_iff hNC] using
    (G.tightGraph s).bfsState_parent_defined_iff (s := s) (v := v) (by simp)

/-- Exactly reachable vertices receive a depth. -/
theorem shortestPathTree_depth_defined_iff (hNC : G.NoNegCycle) (s v : V) :
    (∃ d, (G.shortestPathTree s).depth v = some d) ↔ ∃ p, G.IsWalkFrom s v p := by
  simpa only [shortestPathTree, G.tightGraph_reachable_iff hNC] using
    (G.tightGraph s).bfsState_distance_defined_iff_reachable (s := s) (v := v) (by simp)

/-- An unreachable vertex has neither a predecessor nor a depth. -/
theorem shortestPathTree_unreachable (hNC : G.NoNegCycle) (s v : V)
    (hn : ¬ ∃ p, G.IsWalkFrom s v p) :
    (G.shortestPathTree s).parent v = none ∧ (G.shortestPathTree s).depth v = none := by
  constructor
  · cases hp : (G.shortestPathTree s).parent v with
    | none => rfl
    | some u => exact (hn ((G.shortestPathTree_parent_defined_iff hNC s v).mp ⟨u, hp⟩).1).elim
  · cases hd : (G.shortestPathTree s).depth v with
    | none => rfl
    | some d => exact (hn ((G.shortestPathTree_depth_defined_iff hNC s v).mp ⟨d, hd⟩)).elim

private theorem shortestDist_source (hNC : G.NoNegCycle) (s : V) : G.shortestDist s s = 0 := by
  have hle : G.shortestDist s s ≤ 0 := by
    simpa using G.shortestDist_le_walkWeight hNC s s [s] (singleton_walk G s)
  obtain ht | ⟨p, hp, hw⟩ := (G.shortestDist_isShortestDist hNC s s).2
  · rw [ht] at hle
    simp at hle
  · apply le_antisymm hle
    rw [← hw]
    exact_mod_cast hNC s p hp

private theorem parentPath_weight (hNC : G.NoNegCycle) (s : V) {v d}
    (hpath : CLRS.Chapter22.Graph.BFSParentPath (G.shortestPathTree s).parent s v d) :
    ∃ p, G.IsWalkFrom s v p ∧ p.length = d + 1 ∧
      List.IsChain (fun u w => (G.shortestPathTree s).parent w = some u) p ∧
      (walkWeight G.w p : WithTop ℝ) = G.shortestDist s v := by
  induction hpath with
  | root =>
    refine ⟨[s], singleton_walk G s, rfl, by simp, ?_⟩
    simpa using (shortestDist_source G hNC s).symm
  | @tail u v n hpath hp ih =>
    obtain ⟨p, hw, hlen, hchain, hweight⟩ := ih
    obtain ⟨hedge, htight, _⟩ := G.shortestPathTree_parent_step s hp
    refine ⟨p ++ [v], IsWalkFrom.append_edge G hw hedge, ?_, ?_, ?_⟩
    · simp [hlen]
    · apply List.isChain_append.mpr
      refine ⟨hchain, by simp, ?_⟩
      intro a ha b hb
      have hau : a = u := by
        have hh : p.getLast? = some a := Option.mem_def.mp ha
        exact Option.some.inj (hh.symm.trans hw.last)
      have hb' : b = v := by simpa using (Option.mem_def.mp hb).symm
      simpa [hau, hb'] using hp
    · have hn := IsWalkFrom.ne_nil G hw
      have hlast : p.getLast hn = u := by
        simpa only [List.getLast?_eq_some_getLast hn, Option.some.injEq] using hw.last
      rw [walkWeight_append_singleton G.w p hn v, hlast, WithTop.coe_add, hweight]
      exact htight.symm

/-- Actual returned parent pointers recover a source walk of the computed shortest weight. -/
theorem shortestPathTree_path (hNC : G.NoNegCycle) (s : V) {v d}
    (hd : (G.shortestPathTree s).depth v = some d) :
    ∃ p, G.IsWalkFrom s v p ∧ p.length = d + 1 ∧
      List.IsChain (fun u w => (G.shortestPathTree s).parent w = some u) p ∧
      (walkWeight G.w p : WithTop ℝ) = (G.shortestPathTree s).distance v :=
  parentPath_weight G hNC s ((G.tightGraph s).bfsState_parentPath (by simp) hd)

/-- Only the source has depth zero. -/
theorem shortestPathTree_depth_zero_iff (s v : V) :
    (G.shortestPathTree s).depth v = some 0 ↔ v = s := by
  constructor
  · intro hd
    have hr := (G.tightGraph s).bfsState_distance_reachableIn (by simp) hd
    cases hr
    rfl
  · rintro rfl
    exact G.shortestPathTree_source_depth _

/-- A tight direct source edge receives the source as its BFS predecessor. -/
theorem shortestPathTree_parent_of_tight_source_edge (s v : V) (hv : v ≠ s)
    (he : G.Adj s v) (ht : G.shortestDist s v = G.shortestDist s s + (G.w s v : WithTop ℝ)) :
    (G.shortestPathTree s).parent v = some s := by
  have he' : (G.tightGraph s).Adj s v := (G.tightGraph_adj s s v).mpr ⟨he, ht⟩
  have hd : (G.shortestPathTree s).depth v = some 1 := by
    apply (G.tightGraph s).bfsState_distance_eq_some_iff (by simp) |>.mpr
    refine ⟨.tail .refl he', ?_⟩
    intro n hn
    cases n with
    | zero => cases hn; exact (hv rfl).elim
    | succ n => omega
  have hpExists := (G.tightGraph s).bfsState_parent_defined_iff (s := s) (v := v) (by simp)
  obtain ⟨u, hu⟩ := hpExists.mpr ⟨(G.tightGraph s).reachable_adj he', hv⟩
  obtain ⟨_, _, d, hdu, hdv⟩ := G.shortestPathTree_parent_step s hu
  rw [hd] at hdv
  have hd0 : d = 0 := by injection hdv with hh; omega
  rw [hd0] at hdu
  have hus := (G.shortestPathTree_depth_zero_iff s u).mp hdu
  simpa [shortestPathTree, hus] using hu

/-- A source-rooted acyclic predecessor tree realizing shortest weighted paths. -/
structure IsShortestPathPredecessorTree (s : V) (result : ShortestPathTreeResult V) : Prop where
  distance_correct : ∀ v, G.IsShortestDist s v (result.distance v)
  root_parent : result.parent s = none
  root_depth : result.depth s = some 0
  parent_defined_iff : ∀ v, (∃ u, result.parent v = some u) ↔
    (∃ p, G.IsWalkFrom s v p) ∧ v ≠ s
  depth_defined_iff : ∀ v, (∃ d, result.depth v = some d) ↔ ∃ p, G.IsWalkFrom s v p
  parent_step : ∀ u v, result.parent v = some u →
    G.Adj u v ∧ result.distance v = result.distance u + (G.w u v : WithTop ℝ) ∧
    ∃ d, result.depth u = some d ∧ result.depth v = some (d + 1)
  path : ∀ v d, result.depth v = some d →
    ∃ p, G.IsWalkFrom s v p ∧ p.length = d + 1 ∧
      List.IsChain (fun u w => result.parent w = some u) p ∧
      (walkWeight G.w p : WithTop ℝ) = result.distance v
  acyclic : ∀ v, ¬ Relation.TransGen (fun u w => result.parent w = some u) v v

/-- The constructed result satisfies the full weighted predecessor-tree contract. -/
theorem shortestPathTree_correct (hNC : G.NoNegCycle) (s : V) :
    G.IsShortestPathPredecessorTree s (G.shortestPathTree s) := by
  exact {
    distance_correct := G.shortestDist_isShortestDist hNC s
    root_parent := G.shortestPathTree_source_parent s
    root_depth := G.shortestPathTree_source_depth s
    parent_defined_iff := G.shortestPathTree_parent_defined_iff hNC s
    depth_defined_iff := G.shortestPathTree_depth_defined_iff hNC s
    parent_step := fun u v h => G.shortestPathTree_parent_step s h
    path := fun v d h => G.shortestPathTree_path hNC s h
    acyclic := G.shortestPathTree_acyclic s
  }

end CLRS.Chapter24.WeightedGraph
