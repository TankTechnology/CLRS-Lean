import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS
import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.S4_ExecutableBFS.SupportAdjacency
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.S4_Matching_Flow
import CLRSLean.FourthEdition.Chapter_25.Section_25_1_Maximum_Bipartite_Matching.FlowExecution.Model

/-!
# Residual support of a bipartite matching flow

The constructed network has one forward support arc for every left vertex,
graph edge, and right vertex.  Residual search needs at most the two
orientations of those arcs.  This file defines that finite support, proves its
exact cardinality and residual coverage, and builds the indexed adjacency
used by the costed BFS.
-/

namespace CLRS

open Finset Classical

namespace Chapter26

variable {W : Type*} [Fintype W] [DecidableEq W] {N : FlowNetwork W}

/-- Every residual edge is supported by a nonzero capacity in its forward or
reverse direction. -/
theorem Flow.residualEdge_implies_capacity_support (φ : Flow W N) {u v : W}
    (hres : Flow.residualEdge φ u v) : N.c u v ≠ 0 ∨ N.c v u ≠ 0 := by
  by_contra h
  rw [not_or] at h
  have huv : N.c u v = 0 := not_ne_iff.mp h.1
  have hvu : N.c v u = 0 := not_ne_iff.mp h.2
  have hnonneg : 0 ≤ φ.f u v := Flow.nonneg_of_zero_reverse_cap φ u v hvu
  unfold Flow.residualEdge Flow.residualCapacity at hres
  rw [huv] at hres
  linarith

end Chapter26

namespace Matchings

open Chapter26

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Source-to-left support arcs. -/
noncomputable def matchingFlowSourceSupport (G : BipartiteGraph V) :
    Finset ((V ⊕ Bool) × (V ⊕ Bool)) :=
  G.L.image fun l => (Sum.inr true, Sum.inl l)

/-- Embedded left-to-right graph arcs. -/
noncomputable def matchingFlowGraphSupport (G : BipartiteGraph V) :
    Finset ((V ⊕ Bool) × (V ⊕ Bool)) :=
  G.E.image fun e => (Sum.inl e.1, Sum.inl e.2)

/-- Right-to-sink support arcs. -/
noncomputable def matchingFlowSinkSupport (G : BipartiteGraph V) :
    Finset ((V ⊕ Bool) × (V ⊕ Bool)) :=
  G.R.image fun r => (Sum.inl r, Sum.inr false)

/-- All forward support arcs of the matching flow network. -/
noncomputable def matchingFlowForwardSupport (G : BipartiteGraph V) :
    Finset ((V ⊕ Bool) × (V ⊕ Bool)) :=
  matchingFlowSourceSupport G ∪ matchingFlowGraphSupport G ∪
    matchingFlowSinkSupport G

/-- Reverse one directed arc. -/
def reverseArc {α : Type*} (e : α × α) : α × α := (e.2, e.1)

@[simp]
theorem reverseArc_reverseArc {α : Type*} (e : α × α) :
    reverseArc (reverseArc e) = e := by
  rcases e with ⟨u, v⟩
  rfl

theorem reverseArc_injective {α : Type*} : Function.Injective (@reverseArc α) :=
  Function.LeftInverse.injective reverseArc_reverseArc

/-- Candidate residual arcs: both orientations of every forward support arc. -/
noncomputable def matchingFlowResidualSupport (G : BipartiteGraph V) :
    Finset ((V ⊕ Bool) × (V ⊕ Bool)) :=
  matchingFlowForwardSupport G ∪
    (matchingFlowForwardSupport G).image reverseArc

theorem matchingFlowSourceSupport_card (G : BipartiteGraph V) :
    (matchingFlowSourceSupport G).card = G.L.card := by
  exact Finset.card_image_of_injective G.L (by
    intro a b h
    exact Sum.inl.inj (Prod.mk.inj h).2)

theorem matchingFlowGraphSupport_card (G : BipartiteGraph V) :
    (matchingFlowGraphSupport G).card = G.E.card := by
  exact Finset.card_image_of_injective G.E (by
    intro a b h
    exact Prod.ext (Sum.inl.inj (Prod.mk.inj h).1)
      (Sum.inl.inj (Prod.mk.inj h).2))

theorem matchingFlowSinkSupport_card (G : BipartiteGraph V) :
    (matchingFlowSinkSupport G).card = G.R.card := by
  exact Finset.card_image_of_injective G.R (by
    intro a b h
    exact Sum.inl.inj (Prod.mk.inj h).1)

theorem matchingFlowSourceSupport_disjoint_graph (G : BipartiteGraph V) :
    Disjoint (matchingFlowSourceSupport G) (matchingFlowGraphSupport G) := by
  rw [Finset.disjoint_left]
  intro e hs hg
  rcases Finset.mem_image.mp hs with ⟨l, _, rfl⟩
  rcases Finset.mem_image.mp hg with ⟨e, _, h⟩
  simp at h

theorem matchingFlowSourceSupport_disjoint_sink (G : BipartiteGraph V) :
    Disjoint (matchingFlowSourceSupport G) (matchingFlowSinkSupport G) := by
  rw [Finset.disjoint_left]
  intro e hs ht
  rcases Finset.mem_image.mp hs with ⟨l, _, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨r, _, h⟩
  simp at h

theorem matchingFlowGraphSupport_disjoint_sink (G : BipartiteGraph V) :
    Disjoint (matchingFlowGraphSupport G) (matchingFlowSinkSupport G) := by
  rw [Finset.disjoint_left]
  intro e hg ht
  rcases Finset.mem_image.mp hg with ⟨e, _, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨r, _, h⟩
  simp at h

/-- Exact number of forward support arcs. -/
theorem matchingFlowForwardSupport_card (G : BipartiteGraph V) :
    (matchingFlowForwardSupport G).card = flowArcCount G := by
  have hsg := matchingFlowSourceSupport_disjoint_graph G
  have hst := matchingFlowSourceSupport_disjoint_sink G
  have hgt := matchingFlowGraphSupport_disjoint_sink G
  have hus : Disjoint
      (matchingFlowSourceSupport G ∪ matchingFlowGraphSupport G)
      (matchingFlowSinkSupport G) :=
    Finset.disjoint_union_left.mpr ⟨hst, hgt⟩
  rw [matchingFlowForwardSupport,
    Finset.card_union_of_disjoint hus,
    Finset.card_union_of_disjoint hsg,
    matchingFlowSourceSupport_card,
    matchingFlowGraphSupport_card,
    matchingFlowSinkSupport_card]
  rfl

/-- A forward support never contains the reverse of one of its arcs. -/
theorem matchingFlowForwardSupport_no_reverse (G : BipartiteGraph V) {u v : V ⊕ Bool}
    (h : (u, v) ∈ matchingFlowForwardSupport G) :
    (v, u) ∉ matchingFlowForwardSupport G := by
  rw [matchingFlowForwardSupport] at h
  rcases Finset.mem_union.mp h with hsg | ht
  · rcases Finset.mem_union.mp hsg with hs | hg
    · rcases Finset.mem_image.mp hs with ⟨l, hl, huv⟩
      have hu : Sum.inr true = u := congrArg Prod.fst huv
      have hv : Sum.inl l = v := congrArg Prod.snd huv
      subst u
      subst v
      simp [matchingFlowForwardSupport, matchingFlowSourceSupport,
        matchingFlowGraphSupport, matchingFlowSinkSupport]
    · rcases Finset.mem_image.mp hg with ⟨e, he, huv⟩
      have heL := (G.hE_subset e he).1
      have heR := (G.hE_subset e he).2
      have hu : Sum.inl e.1 = u := congrArg Prod.fst huv
      have hv : Sum.inl e.2 = v := congrArg Prod.snd huv
      subst u
      subst v
      intro hrev
      have hrevE : (e.2, e.1) ∈ G.E := by
        simpa [matchingFlowForwardSupport, matchingFlowSourceSupport,
          matchingFlowGraphSupport, matchingFlowSinkSupport] using hrev
      exact G.not_mem_L_of_mem_R heR (G.hE_subset _ hrevE).1
  · rcases Finset.mem_image.mp ht with ⟨r, hr, huv⟩
    have hu : Sum.inl r = u := congrArg Prod.fst huv
    have hv : Sum.inr false = v := congrArg Prod.snd huv
    subst u
    subst v
    simp [matchingFlowForwardSupport, matchingFlowSourceSupport,
      matchingFlowGraphSupport, matchingFlowSinkSupport]

theorem matchingFlowForwardSupport_disjoint_reverse (G : BipartiteGraph V) :
    Disjoint (matchingFlowForwardSupport G)
      ((matchingFlowForwardSupport G).image reverseArc) := by
  rw [Finset.disjoint_left]
  intro e he hre
  rcases Finset.mem_image.mp hre with ⟨x, hx, hxe⟩
  have hxe' : x = reverseArc e := by
    have := congrArg reverseArc hxe
    simpa using this
  subst x
  exact matchingFlowForwardSupport_no_reverse G he hx

/-- Exact number of oriented residual candidates. -/
theorem matchingFlowResidualSupport_card (G : BipartiteGraph V) :
    (matchingFlowResidualSupport G).card = 2 * flowArcCount G := by
  rw [matchingFlowResidualSupport,
    Finset.card_union_of_disjoint (matchingFlowForwardSupport_disjoint_reverse G),
    Finset.card_image_of_injective _ reverseArc_injective,
    matchingFlowForwardSupport_card]
  omega

theorem capacity_ne_zero_iff_mem_matchingFlowForwardSupport
    (G : BipartiteGraph V) (u v : V ⊕ Bool) :
    (toFlowNetwork V G).c u v ≠ 0 ↔ (u, v) ∈ matchingFlowForwardSupport G := by
  cases u with
  | inl a =>
      cases v with
      | inl b =>
          simp [toFlowNetwork, capFunc, matchingFlowForwardSupport,
            matchingFlowSourceSupport, matchingFlowGraphSupport,
            matchingFlowSinkSupport]
      | inr b =>
          cases b <;>
            simp [toFlowNetwork, capFunc, matchingFlowForwardSupport,
              matchingFlowSourceSupport, matchingFlowGraphSupport,
              matchingFlowSinkSupport]
  | inr a =>
      cases a <;> cases v with
      | inl b =>
          simp [toFlowNetwork, capFunc, matchingFlowForwardSupport,
            matchingFlowSourceSupport, matchingFlowGraphSupport,
            matchingFlowSinkSupport]
      | inr b =>
          cases b <;>
            simp [toFlowNetwork, capFunc, matchingFlowForwardSupport,
              matchingFlowSourceSupport, matchingFlowGraphSupport,
              matchingFlowSinkSupport]

/-- Every residual edge of a matching flow lies in the fixed oriented
support. -/
theorem matchingFlowResidualSupport_covers {G : BipartiteGraph V}
    (M : Matching V G) {u v : V ⊕ Bool}
    (hres : Flow.residualEdge (matchingToFlow M) u v) :
    (u, v) ∈ matchingFlowResidualSupport G := by
  rcases Flow.residualEdge_implies_capacity_support (matchingToFlow M) hres with
    hforward | hreverse
  · exact Finset.mem_union_left _
      ((capacity_ne_zero_iff_mem_matchingFlowForwardSupport G u v).1 hforward)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨(v, u),
      (capacity_ne_zero_iff_mem_matchingFlowForwardSupport G v u).1 hreverse,
      rfl⟩

/-- Indexed oriented support for all matching states of `G`. -/
noncomputable def matchingFlowAdjacency (G : BipartiteGraph V) :
    SupportBuild (V ⊕ Bool) :=
  buildSupportAdjacency (matchingFlowResidualSupport G)

theorem matchingFlowAdjacency_work (G : BipartiteGraph V) :
    (matchingFlowAdjacency G).work = 2 * flowArcCount G := by
  rw [matchingFlowAdjacency, buildSupportAdjacency_work,
    matchingFlowResidualSupport_card]

theorem matchingFlowAdjacency_storage (G : BipartiteGraph V) :
    (matchingFlowAdjacency G).adjacency.storage = 2 * flowArcCount G := by
  rw [matchingFlowAdjacency, buildSupportAdjacency_storage,
    matchingFlowResidualSupport_card]

/-- Filtering a pre-indexed bucket by the current matching-flow residual
predicate gives exactly the old semantic residual neighborhood. -/
theorem matchingFlowAdjacency_residualAdj {G : BipartiteGraph V}
    (M : Matching V G) (u : V ⊕ Bool) :
    ((matchingFlowAdjacency G).adjacency.bucket u).filter
        (fun v => Flow.residualEdge (matchingToFlow M) u v) =
      residualAdj (matchingToFlow M) u := by
  ext v
  simp only [Finset.mem_filter, mem_residualAdj]
  constructor
  · exact fun h => h.2
  · intro hres
    refine ⟨?_, hres⟩
    rw [matchingFlowAdjacency, mem_buildSupportAdjacency]
    exact matchingFlowResidualSupport_covers M hres

end Matchings
end CLRS
