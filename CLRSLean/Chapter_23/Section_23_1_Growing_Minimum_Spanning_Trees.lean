import Mathlib

open Finset

/-!
# CLRS Section 23.1 - Growing a minimum spanning tree

This section proves the exchange kernel behind the standard
minimum-spanning-tree cut property:

* replacing a heavier tree edge by a no-heavier edge preserves optimality;
* a light edge crossing a cut is safe, provided the usual tree-exchange
  certificate is available.

The graph-specific fact that a spanning tree plus a crossing edge contains a
replaceable crossing edge is kept as an explicit certificate.  This keeps the
first MST module focused on the reusable proof pattern rather than on a
particular graph representation or union-find implementation.
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

end FiniteGraph

/-- A family of feasible spanning trees over the edge type. -/
structure Problem (E : Type) [DecidableEq E] where
  IsSpanningTree : Finset E → Prop

namespace FiniteGraph

def toProblem (G : FiniteGraph V E) : Problem E where
  IsSpanningTree := G.IsSpanningTree

end FiniteGraph

/-- `T` is a minimum feasible tree among all trees extending `A`. -/
structure IsMSTExtending (P : Problem E) (w : E → Nat)
    (A T : Finset E) : Prop where
  tree : P.IsSpanningTree T
  includes : A ⊆ T
  optimal : ∀ U, P.IsSpanningTree U → A ⊆ U → weight w T ≤ weight w U

/-- An edge is safe for `A` if every optimum extending `A` can be turned into
an optimum extending `A ∪ {e}` without losing optimality for the old prefix.

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

/-- The CLRS exchange step: if adding `e` and dropping `f` gives another
spanning tree and `e` is no heavier than `f`, then the exchanged tree is still
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

For every optimum tree extending `A` that does not already contain `e`, the
certificate provides a tree edge `f` crossing the same cut such that replacing
`f` by `e` is feasible and preserves `A`.  The light-edge condition then gives
`w e ≤ w f`.
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
