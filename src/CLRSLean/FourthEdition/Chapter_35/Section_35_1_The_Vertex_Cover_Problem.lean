import Mathlib

/-!
# 35.1 The Vertex-Cover Problem

This section formalizes the vertex-cover problem and the 2-approximation
guarantee of the **APPROX-VERTEX-COVER** algorithm from CLRS §35.1.  A *vertex
cover* of an undirected graph `G = (V, E)` is a set of vertices `C ⊆ V` that
meets every edge: for every edge `(u, v) ∈ E`, at least one of `u`, `v` lies in
`C`.  The *minimum vertex cover* is the smallest such set.  Computing a minimum
vertex cover is NP-hard, but the greedy APPROX-VERTEX-COVER algorithm always
finds a cover within a factor of two of the optimum.

Main results:

- Definition `Graph`: an edge-based graph model — an edge type with source and
  destination maps into the vertex type.
- Definition `IsVertexCoverOn`: a set of vertices meeting every edge of an edge
  set.
- Definition `IsMatching`: a set of pairwise non-incident edges.
- Definition `IsMaximalMatchingOn`: a matching that meets every edge.
- Definition `approxVertexCoverEdges`: the greedy edge-selection loop of
  APPROX-VERTEX-COVER.
- Definition `approxVertexCover`: the cover returned by APPROX-VERTEX-COVER
  (the endpoints of the selected edges).
- Theorem `approxVertexCoverEdges_maximal`: the greedy loop returns a maximal
  matching.
- Theorem `endpoints_isVertexCover`: the endpoints of a maximal matching form a
  vertex cover.
- Theorem `matching_le_cover` (Lemma 35.1): any vertex cover has size at least
  that of any matching.
- Theorem `endpoints_card`: a matching on a loop-free graph contributes exactly
  two distinct vertices per edge.
- Theorem `approxVertexCover_isVertexCover` (Theorem 35.1): APPROX-VERTEX-COVER
  returns a vertex cover.
- Theorem `approxVertexCover_two_approx` (Theorem 35.1): the returned cover has
  size at most twice that of any vertex cover — in particular, of an optimal
  one.

Notation conventions used in this section:

- `G` : a graph (an edge type with `src`/`dst` endpoint maps)
- `V` : the vertex type
- `E` : the edge type
- `E₀` : the finite set of edges of the graph
- `C` : a candidate vertex cover
- `A` : a set of edges selected by the greedy algorithm
- `Cstar` : an optimal vertex cover
-/
noncomputable section

namespace CLRS

namespace ApproxVertexCover

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/--
An **edge-based graph**: a type `E` of edges together with source and
destination maps into the vertex type `V`.  This is the minimal structure
needed to state vertex covers, matchings, and the greedy algorithm, and matches
the edge model used elsewhere in the repository (cf. the minimum-spanning-tree
sections).
-/
structure Graph (V E : Type) where
  src : E → V
  dst : E → V

namespace Graph

variable (G : Graph V E)

/-- A vertex is *incident* to an edge when it is one of the edge's endpoints. -/
def Incident (v : V) (e : E) : Prop :=
  G.src e = v ∨ G.dst e = v

/-- Two edges are *incident* when they share at least one endpoint. -/
def EdgesIncident (e f : E) : Prop :=
  ∃ v : V, G.Incident v e ∧ G.Incident v f

/--
A **vertex cover** of the edge set `E₀`: a set of vertices `C` meeting every
edge of `E₀`.  For the CLRS graph `G = (V, E)` the edge set is the whole graph
(`E₀ = E`), so every edge has an endpoint in `C` (CLRS §35.1).
-/
def IsVertexCoverOn (E₀ : Finset E) (C : Finset V) : Prop :=
  ∀ e : E, e ∈ E₀ → G.src e ∈ C ∨ G.dst e ∈ C

/--
A **matching**: a set of edges no two of which share an endpoint (CLRS §35.1).
-/
def IsMatching (A : Finset E) : Prop :=
  ∀ ⦃e f : E⦄, e ∈ A → f ∈ A → e ≠ f → ¬ G.EdgesIncident e f

/--
A **maximal matching** of the edge set `E₀`: a matching that meets every edge
of `E₀` — no further edge of `E₀` can be added without sharing an endpoint.
-/
def IsMaximalMatchingOn (E₀ : Finset E) (A : Finset E) : Prop :=
  G.IsMatching A ∧ ∀ e : E, e ∈ E₀ → ∃ f ∈ A, G.EdgesIncident e f

/--
The set of vertices incident to at least one edge of `A`: the endpoints of the
edges in `A`.
-/
def endpoints (A : Finset E) : Finset V :=
  A.image G.src ∪ A.image G.dst

/-- An edge is incident to itself (its source is a common endpoint). -/
theorem edgesIncident_self (e : E) : G.EdgesIncident e e :=
  ⟨G.src e, Or.inl rfl, Or.inl rfl⟩

/-- Edge incidence is symmetric: if `e` and `f` share an endpoint, so do `f`
and `e`. -/
theorem edgesIncident_symm {e f : E} (h : G.EdgesIncident e f) : G.EdgesIncident f e := by
  rcases h with ⟨v, hve, hvf⟩
  exact ⟨v, hvf, hve⟩

/--
The edges of `E₀` that are **not** incident to `e`: the remainder of the edge
set after a greedy step deletes every edge sharing an endpoint with the picked
edge `e`.
-/
def incidentFiltered (E₀ : Finset E) (e : E) : Finset E := by
  classical
  exact E₀.filter (fun f => ¬ G.EdgesIncident e f)

/-- Deleting the edges incident to the picked edge strictly shrinks a nonempty
edge set, because the picked edge itself is deleted. -/
lemma filter_incident_card_lt (E₀ : Finset E) (hne : E₀.Nonempty) :
    (G.incidentFiltered E₀ hne.choose).card < E₀.card := by
  classical
  have henot : hne.choose ∉ G.incidentFiltered E₀ hne.choose := by
    intro hm
    unfold incidentFiltered at hm
    exact (Finset.mem_filter.mp hm).2 (G.edgesIncident_self hne.choose)
  have hsub : G.incidentFiltered E₀ hne.choose ⊆ E₀ := by
    intro f hf
    unfold incidentFiltered at hf
    exact (Finset.mem_filter.mp hf).1
  exact Finset.card_lt_card ⟨hsub, by
    intro hEq
    exact henot (hEq hne.choose_spec)⟩

/--
The **greedy edge-selection loop** of APPROX-VERTEX-COVER: while edges remain,
pick an arbitrary edge, add it to the chosen set, and delete every edge sharing
an endpoint with it.  This returns the *chosen edges*; the cover they induce is
their endpoints.  Each recursive call removes the picked edge, so the remaining
edge set strictly shrinks and the loop terminates (CLRS §35.1,
APPROX-VERTEX-COVER).
-/
noncomputable def approxVertexCoverEdges (G : Graph V E) : (E₀ : Finset E) → Finset E := by
  classical
  exact fun E₀ =>
    if hne : E₀.Nonempty then
      insert hne.choose (approxVertexCoverEdges G (G.incidentFiltered E₀ hne.choose))
    else ∅
termination_by E₀ => E₀.card
decreasing_by
  classical
  exact G.filter_incident_card_lt E₀ hne

/--
The invariants of the greedy loop: the chosen edges form a matching, they meet
every edge of the input (maximality), and they are drawn from the input.  This
is proved by well-founded induction on the size of the remaining edge set, which
decreases at every step.
-/
lemma approxVertexCoverEdges_invariants (E₀ : Finset E) :
    G.IsMatching (approxVertexCoverEdges G E₀) ∧
      (∀ e : E, e ∈ E₀ → ∃ f ∈ approxVertexCoverEdges G E₀, G.EdgesIncident e f) ∧
      approxVertexCoverEdges G E₀ ⊆ E₀ := by
  classical
  let P : Finset E → Prop := fun s =>
    G.IsMatching (approxVertexCoverEdges G s) ∧
      (∀ e : E, e ∈ s → ∃ f ∈ approxVertexCoverEdges G s, G.EdgesIncident e f) ∧
      approxVertexCoverEdges G s ⊆ s
  have hwf : WellFounded (fun a b : Finset E => a.card < b.card) :=
    (measure (fun s : Finset E => s.card)).wf
  have hmain : ∀ s : Finset E, P s := by
    refine hwf.fix (C := P) ?_
    intro s ih
    by_cases hne : s.Nonempty
    · unfold P
      rw [approxVertexCoverEdges.eq_1, dif_pos hne]
      let F : Finset E := G.incidentFiltered s hne.choose
      have hFcard : F.card < s.card := by simpa [F] using G.filter_incident_card_lt s hne
      have ihF : P F := ih F hFcard
      rcases ihF with ⟨hmF, hmaxF, hsubF⟩
      have he_mem : hne.choose ∈ s := hne.choose_spec
      constructor
      · intro e f he hf hnef
        rw [Finset.mem_insert] at he hf
        rcases he with he_eq | he_memR
        · subst e
          rcases hf with hf_eq | hf_memR
          · subst f
            exact False.elim (hnef rfl)
          · have hfF : f ∈ F := hsubF hf_memR
            simp [F, incidentFiltered] at hfF
            exact hfF.2
        · rcases hf with hf_eq | hf_memR
          · subst f
            have heF : e ∈ F := hsubF he_memR
            simp [F, incidentFiltered] at heF
            exact fun h => heF.2 (G.edgesIncident_symm h)
          · exact hmF he_memR hf_memR hnef
      · constructor
        · intro e he_mem
          by_cases hinc : G.EdgesIncident hne.choose e
          · exact ⟨hne.choose, Finset.mem_insert.mpr (Or.inl rfl), G.edgesIncident_symm hinc⟩
          · have heF : e ∈ F := by
              simp [F, incidentFiltered]
              exact ⟨he_mem, hinc⟩
            rcases hmaxF e heF with ⟨f, hfR, hinc'⟩
            exact ⟨f, Finset.mem_insert.mpr (Or.inr hfR), hinc'⟩
        · intro a ha
          rw [Finset.mem_insert] at ha
          rcases ha with ha_eq | ha_memR
          · exact ha_eq.symm ▸ he_mem
          · have haF : a ∈ F := hsubF ha_memR
            simp [F, incidentFiltered] at haF
            exact haF.1
    · have hs : s = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hne ⟨a, ha⟩
      rw [hs]
      unfold P
      rw [approxVertexCoverEdges.eq_1]
      simp [IsMatching]
  exact hmain E₀

/-- The chosen edges of APPROX-VERTEX-COVER form a matching. -/
theorem approxVertexCoverEdges_matching (E₀ : Finset E) :
    G.IsMatching (approxVertexCoverEdges G E₀) :=
  (G.approxVertexCoverEdges_invariants E₀).1

/-- The chosen edges of APPROX-VERTEX-COVER form a maximal matching of the
input edge set: every edge shares an endpoint with some chosen edge. -/
theorem approxVertexCoverEdges_maximal (E₀ : Finset E) :
    G.IsMaximalMatchingOn E₀ (approxVertexCoverEdges G E₀) :=
  ⟨G.approxVertexCoverEdges_matching E₀, (G.approxVertexCoverEdges_invariants E₀).2.1⟩

/-- APPROX-VERTEX-COVER only selects edges from the input edge set. -/
theorem approxVertexCoverEdges_subset (E₀ : Finset E) :
    approxVertexCoverEdges G E₀ ⊆ E₀ :=
  (G.approxVertexCoverEdges_invariants E₀).2.2

/--
The endpoints of a maximal matching form a **vertex cover**: every edge of `E₀`
shares an endpoint with some matched edge, and that shared endpoint is an
endpoint of the cover.
-/
theorem endpoints_isVertexCover (E₀ : Finset E) (A : Finset E)
    (hmax : G.IsMaximalMatchingOn E₀ A) :
    G.IsVertexCoverOn E₀ (G.endpoints A) := by
  rcases hmax with ⟨hm, hmaxe⟩
  intro e he
  rcases hmaxe e he with ⟨f, hfA, hinc⟩
  rcases hinc with ⟨v, hve, hvf⟩
  rcases hve with hve_src | hve_dst
  · left
    rw [hve_src]
    rcases hvf with hvf_src | hvf_dst
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨f, hfA, hvf_src⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨f, hfA, hvf_dst⟩))
  · right
    rw [hve_dst]
    rcases hvf with hvf_src | hvf_dst
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨f, hfA, hvf_src⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨f, hfA, hvf_dst⟩))

/-- A chosen endpoint of an edge lying in the cover. -/
def coverEndpoint (C : Finset V) (e : E) (heC : G.src e ∈ C ∨ G.dst e ∈ C) : V :=
  if h : G.src e ∈ C then G.src e else G.dst e

/-- The chosen endpoint of an edge indeed lies in the cover. -/
lemma coverEndpoint_mem {C : Finset V} {e : E} (heC : G.src e ∈ C ∨ G.dst e ∈ C) :
    G.coverEndpoint C e heC ∈ C := by
  unfold coverEndpoint
  by_cases h : G.src e ∈ C
  · simpa [h]
  · simpa [h] using heC.resolve_left h

/-- The chosen endpoint of an edge is one of the edge's endpoints. -/
lemma coverEndpoint_incident {C : Finset V} {e : E} (heC : G.src e ∈ C ∨ G.dst e ∈ C) :
    G.Incident (G.coverEndpoint C e heC) e := by
  unfold coverEndpoint Incident
  by_cases h : G.src e ∈ C
  · simpa [h]
  · simpa [h]

/--
Distinct edges of a matching choose distinct endpoints in a cover: if the
chosen endpoints coincided, a single vertex would be an endpoint of both edges,
contradicting that the edge set is a matching.
-/
lemma coverEndpoint_ne {A : Finset E} {C : Finset V}
    (hA : G.IsMatching A) {e f : E} (he : e ∈ A) (hf : f ∈ A) (hnef : e ≠ f)
    {se : G.src e ∈ C ∨ G.dst e ∈ C} {sf : G.src f ∈ C ∨ G.dst f ∈ C} :
    G.coverEndpoint C e se ≠ G.coverEndpoint C f sf := by
  intro hEq
  have hend_e : G.Incident (G.coverEndpoint C e se) e := G.coverEndpoint_incident se
  have hend_f : G.Incident (G.coverEndpoint C f sf) f := G.coverEndpoint_incident sf
  have hinc : G.EdgesIncident e f :=
    ⟨G.coverEndpoint C e se, hend_e, by simpa [hEq] using hend_f⟩
  exact hA he hf hnef hinc

/--
**Lemma 35.1 (lower bound).**  Any vertex cover `C` of the edge set `E₀` has
size at least any matching `A` contained in `E₀`: `A.card ≤ C.card`.  Each edge
of `A` contributes a distinct vertex of `C` (a single vertex cannot cover two
distinct edges of a matching), so the chosen-endpoint map is injective.
-/
theorem matching_le_cover {E₀ : Finset E} {A : Finset E} {C : Finset V}
    (hA : G.IsMatching A) (hAsub : A ⊆ E₀) (hC : G.IsVertexCoverOn E₀ C) :
    A.card ≤ C.card := by
  let f : {e // e ∈ A} → {v // v ∈ C} :=
    fun ⟨e, he⟩ => ⟨G.coverEndpoint C e (hC e (hAsub he)), G.coverEndpoint_mem (hC e (hAsub he))⟩
  have hf_inj : Function.Injective f := by
    intro ⟨e, he⟩ ⟨f, hf⟩ hEq
    have hef : e = f := by
      by_contra hne
      have hne' : G.coverEndpoint C e (hC e (hAsub he)) ≠
          G.coverEndpoint C f (hC f (hAsub hf)) :=
        G.coverEndpoint_ne hA he hf hne (se := hC e (hAsub he)) (sf := hC f (hAsub hf))
      apply hne'
      exact congrArg Subtype.val hEq
    exact Subtype.ext hef
  have hcard : Fintype.card {e // e ∈ A} ≤ Fintype.card {v // v ∈ C} :=
    Fintype.card_le_of_injective f hf_inj
  simpa using hcard

/--
On a loop-free graph, a matching `A` contributes exactly two distinct vertices
per edge, so its endpoint set has size `2 * A.card`.  This is the counting step
that turns the matching lower bound into the factor-two approximation.
-/
theorem endpoints_card {A : Finset E}
    (hA : G.IsMatching A) (hloop : ∀ e : E, G.src e ≠ G.dst e) :
    (G.endpoints A).card = 2 * A.card := by
  have hcard_src : (A.image G.src).card = A.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    by_contra hne
    have hinc : G.EdgesIncident a b :=
      ⟨G.src a, Or.inl rfl, Or.inl hab.symm⟩
    exact hA ha hb hne hinc
  have hcard_dst : (A.image G.dst).card = A.card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    by_contra hne
    have hinc : G.EdgesIncident a b :=
      ⟨G.dst a, Or.inr rfl, Or.inr hab.symm⟩
    exact hA ha hb hne hinc
  have hdisj : Disjoint (A.image G.src) (A.image G.dst) := by
    rw [Finset.disjoint_left]
    intro v hvsrc hvdst
    rcases Finset.mem_image.mp hvsrc with ⟨e, heA, hsrc⟩
    rcases Finset.mem_image.mp hvdst with ⟨f, hfA, hdst⟩
    have heq : G.src e = G.dst f := by rw [hsrc, hdst]
    by_cases hef : e = f
    · exact False.elim (hloop e (by simpa [hef] using heq))
    · exact hA heA hfA hef ⟨v, Or.inl hsrc, Or.inr hdst⟩
  calc
    (G.endpoints A).card = ((A.image G.src) ∪ (A.image G.dst)).card := rfl
    _ = (A.image G.src).card + (A.image G.dst).card := by
      rw [Finset.card_union_of_disjoint hdisj]
    _ = A.card + A.card := by rw [hcard_src, hcard_dst]
    _ = 2 * A.card := by omega

/--
The **cover returned by APPROX-VERTEX-COVER**: the endpoints of the edges
chosen by the greedy loop.
-/
def approxVertexCover (E₀ : Finset E) : Finset V :=
  G.endpoints (G.approxVertexCoverEdges E₀)

/--
**Theorem 35.1 (correctness).**  APPROX-VERTEX-COVER returns a vertex cover of
its input edge set: every edge shares an endpoint with a chosen edge, and the
chosen edges' endpoints form the returned cover.
-/
theorem approxVertexCover_isVertexCover (E₀ : Finset E) :
    G.IsVertexCoverOn E₀ (G.approxVertexCover E₀) := by
  unfold approxVertexCover
  exact G.endpoints_isVertexCover E₀ (approxVertexCoverEdges G E₀)
    (G.approxVertexCoverEdges_maximal E₀)

/--
**Theorem 35.1 (2-approximation).**  For every vertex cover `Cstar` of the
input edge set — in particular for an optimal one — the cover returned by
APPROX-VERTEX-COVER has size at most twice `Cstar.card`.  The chosen edges form
a matching `A` with `2 * A.card` endpoints, while any cover needs at least
`A.card` vertices, so the returned cover has size `2 * A.card ≤ 2 * Cstar.card`.
-/
theorem approxVertexCover_two_approx (E₀ : Finset E) (Cstar : Finset V)
    (hCstar : G.IsVertexCoverOn E₀ Cstar) (hloop : ∀ e : E, G.src e ≠ G.dst e) :
    (G.approxVertexCover E₀).card ≤ 2 * Cstar.card := by
  let A := approxVertexCoverEdges G E₀
  have hA_matching : G.IsMatching A := by simpa [A] using G.approxVertexCoverEdges_matching E₀
  have hA_sub : A ⊆ E₀ := by simpa [A] using G.approxVertexCoverEdges_subset E₀
  have hA_le : A.card ≤ Cstar.card := G.matching_le_cover hA_matching hA_sub hCstar
  have hcard : (G.endpoints A).card = 2 * A.card := G.endpoints_card hA_matching hloop
  calc
    (G.endpoints A).card = 2 * A.card := hcard
    _ ≤ 2 * Cstar.card := by omega

end Graph

end ApproxVertexCover

end CLRS
