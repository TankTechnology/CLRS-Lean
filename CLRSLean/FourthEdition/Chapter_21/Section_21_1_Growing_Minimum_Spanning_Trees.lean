import Mathlib

open Finset

/-!
# CLRS Section 21.1 - Growing a minimum spanning tree

This section proves the exchange kernel behind the standard
minimum-spanning-tree cut property:

* replacing a heavier tree edge by a no-heavier edge preserves optimality;
* a light edge crossing a cut is safe, provided the usual tree-exchange
  certificate is available.

The graph-specific fact that a spanning tree plus a crossing edge contains a
replaceable crossing edge is kept as an explicit certificate.  This keeps the
first MST module focused on the reusable proof pattern rather than on a
particular graph representation or union-find implementation.

Main results:

* Theorem {lit}`FiniteGraph.spanning_tree_maximal`: a finite spanning tree is
  maximal among spanning trees under edge-set inclusion.
* Theorems {lit}`FiniteGraph.minimumSpanningTree_of_mstExtending_empty` and
  {lit}`FiniteGraph.minimumSpanningTree_iff_mstExtending_empty`: the abstract
  empty-prefix optimum specification is equivalent to the concrete finite-graph
  minimum-spanning-tree specification.
* Theorem {lit}`FiniteGraph.exists_crossing_tree_edge_preserving_prefix`: a
  spanning tree path across a respecting cut supplies a replaceable crossing
  tree edge outside the accepted prefix.
* Theorem {lit}`safe_edge_of_lightest_crossing`: the CLRS cut property in
  safe-edge form.
-/

namespace CLRS
namespace MST

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- A finite edge-weight sum. -/
def weight (w : E → Nat) (s : Finset E) : Nat :=
  s.sum w

/-- The small amount of graph structure needed to state cuts. -/
structure Graph (V E : Type) where
  src : E → V
  dst : E → V

namespace Graph

/-- An edge crosses a cut when its endpoints are on opposite sides. -/
def Crosses (G : Graph V E) (S : Finset V) (e : E) : Prop :=
  (G.src e ∈ S ∧ G.dst e ∉ S) ∨ (G.dst e ∈ S ∧ G.src e ∉ S)

/-- A cut respects a partial solution when no selected edge crosses it. -/
def Respects (G : Graph V E) (S : Finset V) (A : Finset E) : Prop :=
  ∀ e ∈ A, ¬ G.Crosses S e

/-- The undirected adjacency relation induced by a selected edge set. -/
def AdjIn (G : Graph V E) (A : Finset E) (u v : V) : Prop :=
  ∃ e ∈ A, (G.src e = u ∧ G.dst e = v) ∨ (G.src e = v ∧ G.dst e = u)

/-- Connectivity using only edges from a selected edge set. -/
def ConnectedIn (G : Graph V E) (A : Finset E) (u v : V) : Prop :=
  Relation.ReflTransGen (G.AdjIn A) u v

omit [DecidableEq V] [DecidableEq E] in
theorem connected_refl (G : Graph V E) (A : Finset E) (v : V) :
    G.ConnectedIn A v v :=
  Relation.ReflTransGen.refl

omit [DecidableEq V] [DecidableEq E] in
theorem adjIn_mono {G : Graph V E} {A B : Finset E} (hAB : A ⊆ B)
    {u v : V} (h : G.AdjIn A u v) : G.AdjIn B u v := by
  rcases h with ⟨e, heA, hend⟩
  exact ⟨e, hAB heA, hend⟩

omit [DecidableEq V] [DecidableEq E] in
theorem connected_mono {G : Graph V E} {A B : Finset E} (hAB : A ⊆ B)
    {u v : V} (h : G.ConnectedIn A u v) : G.ConnectedIn B u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpath hadj ih =>
      exact Relation.ReflTransGen.tail ih (Graph.adjIn_mono hAB hadj)

omit [DecidableEq E] in
/--
Any selected-edge connection from one side of a cut to the other uses at least
one selected edge crossing that cut.  This is the lightweight path/cut API used
before introducing a heavier finite walk representation.
-/
theorem connected_crosses_cut {G : Graph V E} {A : Finset E}
    {S : Finset V} {u v : V}
    (hconn : G.ConnectedIn A u v) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e, e ∈ A ∧ G.Crosses S e := by
  induction hconn with
  | refl =>
      exact False.elim (hv hu)
  | tail hpath hadj ih =>
      rcases hadj with ⟨e, heA, hend⟩
      rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
      · by_cases hsrcS : G.src e ∈ S
        · exact ⟨e, heA, Or.inl ⟨hsrcS, by simpa [hdst] using hv⟩⟩
        · exact ih (by simpa [← hsrc] using hsrcS)
      · by_cases hdstS : G.dst e ∈ S
        · exact ⟨e, heA, Or.inr ⟨hdstS, by simpa [hsrc] using hv⟩⟩
        · exact ih (by simpa [← hdst] using hdstS)

end Graph

/-! ## Concrete finite graph specification -/

/-- A concrete finite graph: finite vertex and edge sets plus endpoint maps. -/
structure FiniteGraph (V E : Type) [DecidableEq V] [DecidableEq E]
    extends Graph V E where
  vertices : Finset V
  edges : Finset E
  src_mem : ∀ e ∈ edges, src e ∈ vertices
  dst_mem : ∀ e ∈ edges, dst e ∈ vertices

namespace FiniteGraph

/-- The selected edges span the finite vertex set. -/
def Spans (G : FiniteGraph V E) (A : Finset E) : Prop :=
  ∀ u ∈ G.vertices, ∀ v ∈ G.vertices, G.toGraph.ConnectedIn A u v

/-- A forest is characterized by the standard cycle-test property: removing any
selected edge disconnects its endpoints. -/
def IsForest (G : FiniteGraph V E) (A : Finset E) : Prop :=
  ∀ e ∈ A, ¬ G.toGraph.ConnectedIn (A.erase e) (G.src e) (G.dst e)

/-- A finite-graph spanning tree: selected graph edges, spanning all vertices,
and acyclic in the edge-removal sense. -/
def IsSpanningTree (G : FiniteGraph V E) (A : Finset E) : Prop :=
  A ⊆ G.edges ∧ G.Spans A ∧ G.IsForest A

/-- A concrete minimum spanning tree for a finite graph and edge-weight map. -/
def IsMinimumSpanningTree (G : FiniteGraph V E) (w : E → Nat)
    (T : Finset E) : Prop :=
  G.IsSpanningTree T ∧ ∀ U, G.IsSpanningTree U → weight w T ≤ weight w U

private theorem subset_erase_of_subset_of_not_mem {A T : Finset E} {e : E}
    (hAT : A ⊆ T) (heA : e ∉ A) : A ⊆ T.erase e := by
  intro x hxA
  exact Finset.mem_erase.mpr ⟨fun hxe => heA (hxe ▸ hxA), hAT hxA⟩

/-- A spanning tree is maximal under edge-set inclusion among spanning trees.
This is the concrete graph fact used by the abstract Kruskal theorem. -/
theorem spanning_tree_maximal (G : FiniteGraph V E) {K T : Finset E}
    (hK : G.IsSpanningTree K) (hT : G.IsSpanningTree T) (hKT : K ⊆ T) :
    T = K := by
  by_contra hne
  have h_extra : ∃ e, e ∈ T ∧ e ∉ K := by
    by_contra h
    have hTK : T ⊆ K := by
      intro e heT
      by_contra heK
      exact h ⟨e, heT, heK⟩
    exact hne (Finset.Subset.antisymm hTK hKT)
  rcases h_extra with ⟨e, heT, heK⟩
  have h_edge : e ∈ G.edges := hT.1 heT
  have hsrc : G.src e ∈ G.vertices := G.src_mem e h_edge
  have hdst : G.dst e ∈ G.vertices := G.dst_mem e h_edge
  have hconnK : G.toGraph.ConnectedIn K (G.src e) (G.dst e) :=
    hK.2.1 (G.src e) hsrc (G.dst e) hdst
  have hK_erase : K ⊆ T.erase e :=
    subset_erase_of_subset_of_not_mem hKT heK
  have hconnT : G.toGraph.ConnectedIn (T.erase e) (G.src e) (G.dst e) :=
    Graph.connected_mono hK_erase hconnK
  exact hT.2.2 e heT hconnT

/--
A spanning tree path between the endpoints of an edge crossing a cut contains
a tree edge crossing that same cut.
-/
theorem exists_crossing_tree_edge_of_cut (G : FiniteGraph V E)
    {T : Finset E} {S : Finset V} {e : E}
    (hT : G.IsSpanningTree T) (he : e ∈ G.edges)
    (hcross : G.toGraph.Crosses S e) :
    ∃ f, f ∈ T ∧ G.toGraph.Crosses S f := by
  have hsrc : G.src e ∈ G.vertices := G.src_mem e he
  have hdst : G.dst e ∈ G.vertices := G.dst_mem e he
  rcases hcross with ⟨hsrcS, hdstNot⟩ | ⟨hdstS, hsrcNot⟩
  · exact Graph.connected_crosses_cut
      (hT.2.1 (G.src e) hsrc (G.dst e) hdst) hsrcS hdstNot
  · exact Graph.connected_crosses_cut
      (hT.2.1 (G.dst e) hdst (G.src e) hsrc) hdstS hsrcNot

/--
If the cut respects a prefix {lit}`A`, then the crossing tree edge found on the tree
path is outside {lit}`A`.  Consequently deleting it while inserting the crossing
edge preserves the prefix edge set.
-/
theorem exists_crossing_tree_edge_preserving_prefix (G : FiniteGraph V E)
    {A T : Finset E} {S : Finset V} {e : E}
    (hT : G.IsSpanningTree T) (hAT : A ⊆ T)
    (hrespects : G.toGraph.Respects S A)
    (he : e ∈ G.edges) (hcross : G.toGraph.Crosses S e) :
    ∃ f, f ∈ T ∧ G.toGraph.Crosses S f ∧
      A ⊆ insert e (T.erase f) := by
  rcases G.exists_crossing_tree_edge_of_cut hT he hcross with
    ⟨f, hfT, hfCross⟩
  have hf_not_A : f ∉ A := by
    intro hfA
    exact hrespects f hfA hfCross
  refine ⟨f, hfT, hfCross, ?_⟩
  intro x hxA
  exact Finset.mem_insert_of_mem
    (Finset.mem_erase.mpr ⟨fun hxf => hf_not_A (hxf ▸ hxA), hAT hxA⟩)

end FiniteGraph

/-- A family of feasible spanning trees over the edge type. -/
structure Problem (E : Type) [DecidableEq E] where
  IsSpanningTree : Finset E → Prop

namespace FiniteGraph

def toProblem (G : FiniteGraph V E) : Problem E where
  IsSpanningTree := G.IsSpanningTree

end FiniteGraph

/-- {lit}`T` is a minimum feasible tree among all trees extending {lit}`A`. -/
structure IsMSTExtending (P : Problem E) (w : E → Nat)
    (A T : Finset E) : Prop where
  tree : P.IsSpanningTree T
  includes : A ⊆ T
  optimal : ∀ U, P.IsSpanningTree U → A ⊆ U → weight w T ≤ weight w U

namespace FiniteGraph

/--
The abstract empty-prefix optimum specification is the concrete finite-graph
minimum-spanning-tree specification.
-/
theorem minimumSpanningTree_of_mstExtending_empty (G : FiniteGraph V E)
    {w : E → Nat} {T : Finset E}
    (h : IsMSTExtending G.toProblem w ∅ T) :
    G.IsMinimumSpanningTree w T := by
  refine ⟨h.tree, ?_⟩
  intro U hUtree
  exact h.optimal U hUtree (by simp)

/--
Conversely, a concrete finite-graph MST is an abstract optimum extending the
empty prefix.  This is useful when switching from textbook finite-graph
statements back to the reusable Kruskal induction interface.
-/
theorem mstExtending_empty_of_minimumSpanningTree (G : FiniteGraph V E)
    {w : E → Nat} {T : Finset E}
    (h : G.IsMinimumSpanningTree w T) :
    IsMSTExtending G.toProblem w ∅ T := by
  refine ⟨h.1, ?_, ?_⟩
  · simp
  · intro U hUtree _hUextends
    exact h.2 U hUtree

/--
The empty-prefix abstract MST specification is equivalent to the concrete
finite-graph minimum-spanning-tree specification.
-/
theorem minimumSpanningTree_iff_mstExtending_empty (G : FiniteGraph V E)
    {w : E → Nat} {T : Finset E} :
    G.IsMinimumSpanningTree w T ↔ IsMSTExtending G.toProblem w ∅ T := by
  constructor
  · exact G.mstExtending_empty_of_minimumSpanningTree
  · exact G.minimumSpanningTree_of_mstExtending_empty

end FiniteGraph

/-- An edge is safe for {lit}`A` if every optimum extending {lit}`A` can be turned into
an optimum extending {lit}`A ∪ {e}` without losing optimality for the old prefix.

The second conjunct is what lets a Kruskal-style induction keep global
optimality for the original prefix, not only optimality for the growing prefix.
-/
def SafeEdge (P : Problem E) (w : E → Nat) (A : Finset E) (e : E) : Prop :=
  ∀ T, IsMSTExtending P w A T →
    ∃ T', IsMSTExtending P w (insert e A) T' ∧ IsMSTExtending P w A T'

lemma IsMSTExtending.extend_insert_of_mem {P : Problem E} {w : E → Nat}
    {A T : Finset E} {e : E} (hT : IsMSTExtending P w A T) (he : e ∈ T) :
    IsMSTExtending P w (insert e A) T := by
  refine ⟨hT.tree, Finset.insert_subset he hT.includes, ?_⟩
  intro U hUtree hUextends
  apply hT.optimal U hUtree
  intro x hx
  exact hUextends (Finset.mem_insert_of_mem hx)

private lemma weight_insert_erase_le (w : E → Nat) {T : Finset E} {e f : E}
    (hf : f ∈ T) (he : e ∉ T) (hwe : w e ≤ w f) :
    weight w (insert e (T.erase f)) ≤ weight w T := by
  have he_not_erase : e ∉ T.erase f := by
    intro h
    exact he (Finset.mem_of_mem_erase h)
  have hf_not_erase : f ∉ T.erase f := Finset.notMem_erase f T
  calc
    weight w (insert e (T.erase f))
        = w e + weight w (T.erase f) := by
          simp [weight, he_not_erase]
    _ ≤ w f + weight w (T.erase f) := by omega
    _ = weight w T := by
          unfold weight
          exact Finset.add_sum_erase T w hf

/-- The CLRS exchange step: if adding {lit}`e` and dropping {lit}`f` gives another
spanning tree and {lit}`e` is no heavier than {lit}`f`, then the exchanged tree is still
minimum. -/
theorem mst_exchange_preserves_prefix {P : Problem E} {w : E → Nat} {A T : Finset E}
    {e f : E} (hT : IsMSTExtending P w A T)
    (hf : f ∈ T) (he : e ∉ T)
    (h_tree : P.IsSpanningTree (insert e (T.erase f)))
    (h_extends : A ⊆ insert e (T.erase f)) (h_weight : w e ≤ w f) :
    IsMSTExtending P w A (insert e (T.erase f)) := by
  refine ⟨h_tree, ?_, ?_⟩
  · exact h_extends
  · intro U hUtree hUextends
    exact (weight_insert_erase_le w hf he h_weight).trans
      (hT.optimal U hUtree hUextends)

/-- The same exchange step, packaged for the enlarged prefix. -/
theorem mst_exchange_step {P : Problem E} {w : E → Nat} {A T : Finset E}
    {e f : E} (hT : IsMSTExtending P w A T)
    (hf : f ∈ T) (he : e ∉ T)
    (h_tree : P.IsSpanningTree (insert e (T.erase f)))
    (h_extends : A ⊆ insert e (T.erase f)) (h_weight : w e ≤ w f) :
    IsMSTExtending P w (insert e A) (insert e (T.erase f)) := by
  exact (mst_exchange_preserves_prefix hT hf he h_tree h_extends h_weight).extend_insert_of_mem
    (Finset.mem_insert_self e (T.erase f))

/-- A cut certificate packages the graph-specific part of the CLRS proof.

For every optimum tree extending {lit}`A` that does not already contain {lit}`e`, the
certificate provides a tree edge {lit}`f` crossing the same cut such that replacing
{lit}`f` by {lit}`e` is feasible and preserves {lit}`A`.  The light-edge condition then gives
{lit}`w e ≤ w f`.
-/
structure CutCertificate (G : Graph V E) (P : Problem E) (w : E → Nat)
    (A : Finset E) (S : Finset V) (e : E) : Prop where
  crosses : G.Crosses S e
  respects : G.Respects S A
  lightest : ∀ f, G.Crosses S f → w e ≤ w f
  exchange :
    ∀ T, IsMSTExtending P w A T → e ∉ T →
      ∃ f, f ∈ T ∧ G.Crosses S f ∧
        P.IsSpanningTree (insert e (T.erase f)) ∧
        A ⊆ insert e (T.erase f)


omit [DecidableEq V] in
/-- CLRS cut property in safe-edge form. -/
theorem safe_edge_of_lightest_crossing {G : Graph V E} {P : Problem E}
    {w : E → Nat} {A : Finset E} {S : Finset V} {e : E}
    (hcut : CutCertificate G P w A S e) :
    SafeEdge P w A e := by
  intro T hT
  by_cases heT : e ∈ T
  · exact ⟨T, hT.extend_insert_of_mem heT, hT⟩
  · rcases hcut.exchange T hT heT with
      ⟨f, hfT, hf_crosses, h_tree, h_extends⟩
    exact ⟨insert e (T.erase f),
      mst_exchange_step hT hfT heT h_tree h_extends
        (hcut.lightest f hf_crosses),
      mst_exchange_preserves_prefix hT hfT heT h_tree h_extends
        (hcut.lightest f hf_crosses)⟩

/-- A direct existence wrapper for using a safe edge in a larger proof. -/
theorem exists_mst_containing_safe_edge {P : Problem E} {w : E → Nat}
    {A T : Finset E} {e : E} (hsafe : SafeEdge P w A e)
    (hT : IsMSTExtending P w A T) :
    ∃ T', IsMSTExtending P w (insert e A) T' :=
  let ⟨T', hT', _⟩ := hsafe T hT
  ⟨T', hT'⟩

end MST
end CLRS
