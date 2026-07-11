import CLRSLean.Chapter_23.Section_23_1_Growing_Minimum_Spanning_Trees

open Finset

/-!
# CLRS Section 23.2 - Kruskal and Prim

This section builds on the safe-edge theorem from Section 23.1.  It contains the
mathematical Kruskal pass, cut-certificate induction, finite-graph wrappers, and
the component-oracle interface.  It also isolates the sorted-edge-order
lightness argument used by CLRS: once previously processed edges are known not
to cross the current component cut, the current edge is light by sorted order.
Union-find implementation correctness is deliberately deferred: the current
proof works at the mathematical cycle-test interface level.

Closure results:

- Theorem {lit}`FiniteGraph.canonicalSimplePath_unique`: a selected forest has
  a unique simple path between connected endpoints.
- Theorem {lit}`FiniteGraph.exists_crossing_exchangePath_of_spanningTree`: the
  canonical tree path automatically yields a crossing exchange edge.
- Theorem {lit}`FiniteGraph.cutCertificate_of_lightest_crossing_auto`: finite
  cut certificates no longer require a manual cycle-exchange witness.
- Theorem
  {lit}`FiniteGraph.kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty`:
  a sorted complete exact-component Kruskal scan returns an MST, with local
  lightness and exchange discharged inside the recursion.
- Theorem {lit}`FiniteGraph.prim_minimum_spanning_tree`: every complete CLRS
  Prim light-edge trace returns an MST.

The nested implementation modules now provide the incremental stateful
union-find scan, executable indexed-queue Prim, and algorithm-level work
bounds.  Mutable/RAM semantics and concrete array-heap refinement remain.
-/

namespace CLRS
namespace MST

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-! ## Component-based cycle-test interface -/

/-- A mathematical component oracle for the current selected edge set.  It is
exactly the specification a union-find implementation should refine. -/
structure ComponentOracle (G : Graph V E) where
  component : Finset E → V → Finset V
  mem_self : ∀ A v, v ∈ component A v
  closed_src :
    ∀ A root e, e ∈ A → G.src e ∈ component A root → G.dst e ∈ component A root
  closed_dst :
    ∀ A root e, e ∈ A → G.dst e ∈ component A root → G.src e ∈ component A root

namespace ComponentOracle

omit [DecidableEq V] [DecidableEq E] in
theorem respects (C : ComponentOracle G) (A : Finset E) (root : V) :
    G.Respects (C.component A root) A := by
  intro e he hcross
  rcases hcross with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
  · exact hdst (C.closed_src A root e he hsrc)
  · exact hsrc (C.closed_dst A root e he hdst)

end ComponentOracle

/-! ## Exact component oracles -/

/--
An exact component oracle returns precisely the vertices connected to the root
by the currently selected edge set.
-/
def ExactComponentOracle (G : Graph V E) (C : ComponentOracle G) : Prop :=
  ∀ A root v, v ∈ C.component A root ↔ G.ConnectedIn A root v

namespace Graph

omit [DecidableEq V] [DecidableEq E] in
/-- The undirected adjacency relation is symmetric. -/
theorem adjIn_symm {G : Graph V E} {A : Finset E} {u v : V}
    (h : G.AdjIn A u v) :
    G.AdjIn A v u := by
  rcases h with ⟨e, heA, hend⟩
  refine ⟨e, heA, ?_⟩
  rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
  · exact Or.inr ⟨hsrc, hdst⟩
  · exact Or.inl ⟨hsrc, hdst⟩

omit [DecidableEq V] [DecidableEq E] in
/-- Connectivity induced by selected undirected edges is symmetric. -/
theorem connected_symm {G : Graph V E} {A : Finset E} {u v : V}
    (h : G.ConnectedIn A u v) :
    G.ConnectedIn A v u := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hpath hadj ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          (Graph.adjIn_symm hadj))
        ih

omit [DecidableEq V] [DecidableEq E] in
/-- Connectivity induced by selected edges is transitive. -/
theorem connected_trans {G : Graph V E} {A : Finset E} {u v x : V}
    (huv : G.ConnectedIn A u v) (hvx : G.ConnectedIn A v x) :
    G.ConnectedIn A u x :=
  Relation.ReflTransGen.trans huv hvx

omit [DecidableEq V] [DecidableEq E] in
/-- Any selected edge connects its own endpoints. -/
theorem connected_of_mem_edge {G : Graph V E} {A : Finset E} {e : E}
    (he : e ∈ A) :
    G.ConnectedIn A (G.src e) (G.dst e) := by
  exact Relation.ReflTransGen.tail Relation.ReflTransGen.refl
    ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩

omit [DecidableEq V] [DecidableEq E] in
/--
If every edge of {lit}`B` has endpoints already connected in {lit}`A`, then one
adjacency step in {lit}`B` can be simulated by an {lit}`A`-connection.
-/
theorem connected_of_adjIn_of_edge_connected {G : Graph V E} {A B : Finset E}
    (hedge : ∀ e, e ∈ B → G.ConnectedIn A (G.src e) (G.dst e))
    {u v : V} (hadj : G.AdjIn B u v) :
    G.ConnectedIn A u v := by
  rcases hadj with ⟨e, heB, hend⟩
  have hconn := hedge e heB
  rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
  · simpa [hsrc, hdst] using hconn
  · have hconn' := Graph.connected_symm hconn
    simpa [hsrc, hdst] using hconn'

omit [DecidableEq V] [DecidableEq E] in
/--
If every edge of {lit}`B` has endpoints connected in {lit}`A`, then every
{lit}`B`-path can be transported to an {lit}`A`-path.
-/
theorem connected_of_edgewise_connected {G : Graph V E} {A B : Finset E}
    (hedge : ∀ e, e ∈ B → G.ConnectedIn A (G.src e) (G.dst e))
    {u v : V} (h : G.ConnectedIn B u v) :
    G.ConnectedIn A u v := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail _ hadj ih =>
      exact Graph.connected_trans ih
        (Graph.connected_of_adjIn_of_edge_connected hedge hadj)

omit [DecidableEq V] in
/--
Any path after inserting one edge either already existed before the insertion
or crosses the inserted edge once, with old paths on both sides.
-/
theorem connected_insert_edge_cases {G : Graph V E} {A : Finset E} {e : E}
    {u v : V} (h : G.ConnectedIn (insert e A) u v) :
    G.ConnectedIn A u v ∨
      (G.ConnectedIn A u (G.src e) ∧ G.ConnectedIn A (G.dst e) v) ∨
      (G.ConnectedIn A u (G.dst e) ∧ G.ConnectedIn A (G.src e) v) := by
  induction h with
  | refl =>
      exact Or.inl Relation.ReflTransGen.refl
  | tail _ hadj ih =>
      rcases hadj with ⟨f, hf, hend⟩
      rw [Finset.mem_insert] at hf
      rcases hf with hfe | hfA
      · subst f
        rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
        · subst hsrc
          subst hdst
          rcases ih with hA | ⟨⟨hus, hdy⟩ | ⟨hud, hsy⟩⟩
          · exact Or.inr (Or.inl ⟨hA, Relation.ReflTransGen.refl⟩)
          · have hsd : G.ConnectedIn A (G.src e) (G.dst e) :=
              Graph.connected_trans (Graph.connected_symm hdy)
                Relation.ReflTransGen.refl
            exact Or.inl (Graph.connected_trans hus hsd)
          · exact Or.inl hud
        · subst hsrc
          subst hdst
          rcases ih with hA | ⟨⟨hus, hdy⟩ | ⟨hud, hsy⟩⟩
          · exact Or.inr (Or.inr ⟨hA, Relation.ReflTransGen.refl⟩)
          · exact Or.inl hus
          · have hds : G.ConnectedIn A (G.dst e) (G.src e) :=
              Graph.connected_trans (Graph.connected_symm hsy)
                Relation.ReflTransGen.refl
            exact Or.inl (Graph.connected_trans hud hds)
      · have hadjA : G.AdjIn A _ _ := ⟨f, hfA, hend⟩
        rcases ih with hA | ⟨⟨hus, hdy⟩ | ⟨hud, hsy⟩⟩
        · exact Or.inl (Relation.ReflTransGen.tail hA hadjA)
        · exact Or.inr (Or.inl ⟨hus, Relation.ReflTransGen.tail hdy hadjA⟩)
        · exact Or.inr (Or.inr ⟨hud, Relation.ReflTransGen.tail hsy hadjA⟩)

/-! ## Canonical simple paths in selected forests -/

/-- The loop-free simple graph induced by a selected edge set.  The explicit
inequality removes self-loops without changing connectivity inside a forest. -/
def selectedSimpleGraph (G : Graph V E) (A : Finset E) : SimpleGraph V where
  Adj u v := u ≠ v ∧ G.AdjIn A u v
  symm := ⟨by
    intro u v h
    exact ⟨Ne.symm h.1, Graph.adjIn_symm h.2⟩⟩
  loopless := ⟨by
    intro v h
    exact h.1 rfl⟩

omit [DecidableEq V] [DecidableEq E] in
/-- A selected-simple-graph walk gives a connection in the original labelled
edge model. -/
theorem connectedIn_of_selectedWalk {G : Graph V E} {A : Finset E}
    {u v : V} (p : (G.selectedSimpleGraph A).Walk u v) :
    G.ConnectedIn A u v := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u x v hadj p ih =>
      exact Relation.ReflTransGen.head hadj.2 ih

omit [DecidableEq V] in
/-- If a simple-graph walk avoids one endpoint of a labelled edge, every step
of the walk remains available after that labelled edge is erased. -/
theorem connectedIn_erase_of_selectedWalk_avoids_vertex
    {G : Graph V E} {T : Finset E} {u v z : V} {f : E}
    (p : (G.selectedSimpleGraph T).Walk u v)
    (hz : z ∉ p.support)
    (hfz : G.src f = z ∨ G.dst f = z) :
    G.ConnectedIn (T.erase f) u v := by
  induction p with
  | nil => exact Relation.ReflTransGen.refl
  | @cons u x v hadj p ih =>
      rcases hadj.2 with ⟨g, hgT, hend⟩
      have hgf : g ≠ f := by
        intro hgf
        have hzmem : z ∈ (SimpleGraph.Walk.cons hadj p).support := by
          have hxmem : x ∈ p.support := p.start_mem_support
          rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩ <;>
            rcases hfz with hsrcz | hdstz <;>
            simp_all [SimpleGraph.Walk.support_cons]
        exact hz hzmem
      have hadjErase : G.AdjIn (T.erase f) u x :=
        ⟨g, Finset.mem_erase.mpr ⟨hgf, hgT⟩, hend⟩
      have hzTail : z ∉ p.support := by
        intro hzTail
        exact hz (by simp [hzTail])
      exact Relation.ReflTransGen.head hadjErase (ih hzTail)

omit [DecidableEq V] in
/-- Reachability after deleting one unlabelled simple edge maps back to
labelled connectivity after erasing the corresponding selected edge. -/
theorem connectedIn_erase_of_reachable_delete_selectedEdge
    {G : Graph V E} {T : Finset E} {u v x y : V} {f : E}
    (hfEnds :
      (G.src f = u ∧ G.dst f = v) ∨ (G.src f = v ∧ G.dst f = u))
    (hreach :
      ((G.selectedSimpleGraph T).deleteEdges {s(u, v)}).Reachable x y) :
    G.ConnectedIn (T.erase f) x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hpath hadj ih =>
      rw [SimpleGraph.deleteEdges_adj] at hadj
      rcases hadj with ⟨hselected, hpair⟩
      rcases hselected.2 with ⟨g, hgT, hgEnds⟩
      have hgf : g ≠ f := by
        intro hgf
        apply hpair
        simp only [Set.mem_singleton_iff]
        subst g
        rcases hfEnds with ⟨hfu, hfv⟩ | ⟨hfv, hfu⟩ <;>
          rcases hgEnds with ⟨hga, hgb⟩ | ⟨hgb, hga⟩ <;>
          simp_all
      exact Relation.ReflTransGen.tail ih
        ⟨g, Finset.mem_erase.mpr ⟨hgf, hgT⟩, hgEnds⟩

/-- A labelled edge on a simple selected path that crosses a cut, together
with the two connections that remain after erasing that edge.  This is the
generic endpoint form of {lit}`ExchangePath`. -/
def PathExchange (G : Graph V E) (T : Finset E) (u v : V) (f : E) : Prop :=
  (G.ConnectedIn (T.erase f) (G.src f) u ∧
    G.ConnectedIn (T.erase f) v (G.dst f)) ∨
  (G.ConnectedIn (T.erase f) (G.src f) v ∧
    G.ConnectedIn (T.erase f) u (G.dst f))

omit [DecidableEq V] in
/-- Reversing the endpoint order preserves a path-exchange witness. -/
theorem PathExchange.swap {G : Graph V E} {T : Finset E} {u v : V} {f : E}
    (h : G.PathExchange T u v f) : G.PathExchange T v u f := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- A simple selected path whose endpoints lie on opposite sides of a cut has
a crossing labelled edge whose deletion leaves the path prefix and suffix
connected. -/
theorem exists_pathExchange_of_simplePath_crosses
    {G : Graph V E} {T : Finset E} {S : Finset V} {u v : V}
    (p : (G.selectedSimpleGraph T).Walk u v) (hp : p.IsPath)
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ f, f ∈ T ∧ G.Crosses S f ∧ G.PathExchange T u v f := by
  induction p with
  | nil => exact False.elim (hv hu)
  | @cons u x v hadj p ih =>
      rw [SimpleGraph.Walk.cons_isPath_iff] at hp
      rcases hp with ⟨hp, huAvoids⟩
      rcases hadj.2 with ⟨g, hgT, hend⟩
      by_cases hx : x ∈ S
      · rcases ih hp hx hv with ⟨f, hfT, hfCross, hfPath⟩
        have hgNotCross : ¬ G.Crosses S g := by
          rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩ <;>
            simp [Graph.Crosses, hsrc, hdst, hu, hx]
        have hgf : g ≠ f := by
          intro hgf
          exact hgNotCross (by simpa [hgf] using hfCross)
        have hux : G.ConnectedIn (T.erase f) u x :=
          Relation.ReflTransGen.single
            ⟨g, Finset.mem_erase.mpr ⟨hgf, hgT⟩, hend⟩
        refine ⟨f, hfT, hfCross, ?_⟩
        rcases hfPath with ⟨hfx, hvf⟩ | ⟨hfv, hxf⟩
        · exact Or.inl ⟨Graph.connected_trans hfx (Graph.connected_symm hux), hvf⟩
        · exact Or.inr ⟨hfv, Graph.connected_trans hux hxf⟩
      · have hsuffix : G.ConnectedIn (T.erase g) x v :=
          Graph.connectedIn_erase_of_selectedWalk_avoids_vertex p huAvoids
            (by
              rcases hend with ⟨hsrc, _⟩ | ⟨_, hdst⟩
              · exact Or.inl hsrc
              · exact Or.inr hdst)
        have hgCross : G.Crosses S g := by
          rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
          · exact Or.inl ⟨by simpa [hsrc] using hu, by simpa [hdst] using hx⟩
          · exact Or.inr ⟨by simpa [hdst] using hu, by simpa [hsrc] using hx⟩
        refine ⟨g, hgT, hgCross, ?_⟩
        rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
        · exact Or.inl ⟨
            by simpa [hsrc] using (Graph.connected_refl G (T.erase g) u),
            by simpa [hdst] using (Graph.connected_symm hsuffix)⟩
        · exact Or.inr ⟨
            by simpa [hsrc] using hsuffix,
            by simpa [hdst] using (Graph.connected_refl G (T.erase g) u)⟩

/--
A path-decomposition certificate for the CLRS tree-exchange step.  After
removing tree edge {lit}`f`, the endpoints of the new edge {lit}`e` reconnect
the two sides of {lit}`f`, in one of the two undirected orientations.
-/
def ExchangePath (G : Graph V E) (T : Finset E) (e f : E) : Prop :=
  (G.ConnectedIn (T.erase f) (G.src f) (G.src e) ∧
    G.ConnectedIn (T.erase f) (G.dst e) (G.dst f)) ∨
  (G.ConnectedIn (T.erase f) (G.src f) (G.dst e) ∧
    G.ConnectedIn (T.erase f) (G.src e) (G.dst f))

/--
Cycle-style exchange witness: after deleting tree edge {lit}`f`, inserting the
new edge {lit}`e` reconnects the endpoints of {lit}`f`.  This is the compact
connectivity fact a future finite path/cycle API should produce.
-/
def InsertedEdgeConnection (G : Graph V E) (T : Finset E) (e f : E) : Prop :=
  G.ConnectedIn (insert e (T.erase f)) (G.src f) (G.dst f)

omit [DecidableEq V] in
/--
An {lit}`ExchangePath` certificate reconnects the endpoints of the deleted tree
edge after the new edge is inserted.
-/
theorem exchangePath_connected_insert {G : Graph V E} {T : Finset E} {e f : E}
    (hpath : G.ExchangePath T e f) :
    G.ConnectedIn (insert e (T.erase f)) (G.src f) (G.dst f) := by
  have hmono : T.erase f ⊆ insert e (T.erase f) :=
    Finset.subset_insert e (T.erase f)
  have he_conn :
      G.ConnectedIn (insert e (T.erase f)) (G.src e) (G.dst e) :=
    Graph.connected_of_mem_edge (Finset.mem_insert_self e (T.erase f))
  rcases hpath with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
  · have h₁ := Graph.connected_mono hmono hleft
    have h₂ := Graph.connected_mono hmono hright
    exact Graph.connected_trans (Graph.connected_trans h₁ he_conn) h₂
  · have h₁ := Graph.connected_mono hmono hleft
    have h₂ := Graph.connected_mono hmono hright
    exact Graph.connected_trans (Graph.connected_trans h₁
      (Graph.connected_symm he_conn)) h₂

omit [DecidableEq V] in
/-- An {lit}`ExchangePath` certificate is an inserted-edge connection. -/
theorem insertedEdgeConnection_of_exchangePath {G : Graph V E} {T : Finset E}
    {e f : E} (hpath : G.ExchangePath T e f) :
    G.InsertedEdgeConnection T e f :=
  Graph.exchangePath_connected_insert hpath

omit [DecidableEq V] in
/--
Conversely, if inserting {lit}`e` reconnects the endpoints of {lit}`f`, and
those endpoints were not already connected after erasing {lit}`f`, then the
connection decomposes into an {lit}`ExchangePath` certificate.
-/
theorem exchangePath_of_insert_connected {G : Graph V E} {T : Finset E} {e f : E}
    (hconn :
      G.ConnectedIn (insert e (T.erase f)) (G.src f) (G.dst f))
    (hnot :
      ¬ G.ConnectedIn (T.erase f) (G.src f) (G.dst f)) :
    G.ExchangePath T e f := by
  rcases Graph.connected_insert_edge_cases hconn with hbase |
      (⟨hleft, hright⟩ | ⟨hleft, hright⟩)
  · exact False.elim (hnot hbase)
  · exact Or.inl ⟨hleft, hright⟩
  · exact Or.inr ⟨hleft, hright⟩

omit [DecidableEq V] in
/--
Equivalence between the path-decomposition certificate and the compact
cycle-style inserted-edge connection, assuming deleting {lit}`f` really
separates its endpoints.
-/
theorem exchangePath_iff_insertedEdgeConnection {G : Graph V E} {T : Finset E}
    {e f : E}
    (hnot : ¬ G.ConnectedIn (T.erase f) (G.src f) (G.dst f)) :
    G.ExchangePath T e f ↔ G.InsertedEdgeConnection T e f := by
  constructor
  · exact Graph.insertedEdgeConnection_of_exchangePath
  · intro hconn
    exact Graph.exchangePath_of_insert_connected hconn hnot

end Graph

/-- The executable-style cycle test induced by a component oracle: accept an
edge iff its destination is outside the source component. -/
def acceptByComponent (G : Graph V E) (C : ComponentOracle G)
    (A : Finset E) (e : E) : Bool :=
  decide (G.dst e ∉ C.component A (G.src e))

omit [DecidableEq E] in
private theorem not_mem_component_of_accept {G : Graph V E} {C : ComponentOracle G}
    {A : Finset E} {e : E} (h : acceptByComponent G C A e = true) :
    G.dst e ∉ C.component A (G.src e) := by
  simpa [acceptByComponent] using h

omit [DecidableEq E] in
private theorem mem_component_of_reject {G : Graph V E} {C : ComponentOracle G}
    {A : Finset E} {e : E} (h : acceptByComponent G C A e = false) :
    G.dst e ∈ C.component A (G.src e) := by
  by_contra hmem
  have htrue : acceptByComponent G C A e = true := by
    simp [acceptByComponent, hmem]
  simp [h] at htrue

/-- Accepted component edges induce the cut used in the CLRS proof. -/
theorem cut_certificate_of_component_oracle {G : Graph V E} {P : Problem E}
    {w : E → Nat} (C : ComponentOracle G) {A : Finset E} {e : E}
    (haccept : acceptByComponent G C A e = true)
    (hlight :
      ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ T, IsMSTExtending P w A T → e ∉ T →
        ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
          P.IsSpanningTree (insert e (T.erase f)) ∧
          A ⊆ insert e (T.erase f)) :
    CutCertificate G P w A (C.component A (G.src e)) e := by
  refine ⟨?_, C.respects A (G.src e), hlight, hexchange⟩
  exact Or.inl ⟨C.mem_self A (G.src e), not_mem_component_of_accept haccept⟩

omit [DecidableEq V] [DecidableEq E] in
/--
An edge whose endpoints are already connected by the current selected edge set
cannot cross any exact component cut for that selected edge set.
-/
theorem not_crosses_component_of_connected {G : Graph V E}
    {C : ComponentOracle G} (hexact : ExactComponentOracle G C)
    {A : Finset E} {root : V} {e : E}
    (hconn : G.ConnectedIn A (G.src e) (G.dst e)) :
    ¬ G.Crosses (C.component A root) e := by
  intro hcross
  rcases hcross with ⟨hsrc, hdst⟩ | ⟨hdst, hsrc⟩
  · have hrootSrc : G.ConnectedIn A root (G.src e) :=
      (hexact A root (G.src e)).1 hsrc
    have hrootDst : G.ConnectedIn A root (G.dst e) :=
      Graph.connected_trans hrootSrc hconn
    exact hdst ((hexact A root (G.dst e)).2 hrootDst)
  · have hrootDst : G.ConnectedIn A root (G.dst e) :=
      (hexact A root (G.dst e)).1 hdst
    have hdstSrc : G.ConnectedIn A (G.dst e) (G.src e) :=
      Graph.connected_symm hconn
    have hrootSrc : G.ConnectedIn A root (G.src e) :=
      Graph.connected_trans hrootDst hdstSrc
    exact hsrc ((hexact A root (G.src e)).2 hrootSrc)

omit [DecidableEq V] [DecidableEq E] in
/--
If an edge is either selected already or internally connected by the selected
edge set, it cannot cross an exact component cut.
-/
theorem not_crosses_component_of_mem_or_connected {G : Graph V E}
    {C : ComponentOracle G} (hexact : ExactComponentOracle G C)
    {A : Finset E} {root : V} {e : E}
    (haccounted : e ∈ A ∨ G.ConnectedIn A (G.src e) (G.dst e)) :
    ¬ G.Crosses (C.component A root) e := by
  rcases haccounted with heA | hconn
  · exact C.respects A root e heA
  · exact not_crosses_component_of_connected hexact hconn

/-! ## Sorted-order lightness certificates -/

/--
An edge list is sorted in nondecreasing weight order.

This CLRS-facing predicate is deliberately small: the head is no heavier than
every later edge, and the tail is sorted recursively.
-/
def WeightSorted (w : E → Nat) : List E → Prop
  | [] => True
  | e :: es => (∀ f, f ∈ es → w e ≤ w f) ∧ WeightSorted w es

omit [DecidableEq E] in
/-- A suffix of a sorted edge list is sorted. -/
theorem weightSorted_suffix_of_append (w : E → Nat)
    (processed rest : List E) :
    WeightSorted w (processed ++ rest) → WeightSorted w rest := by
  induction processed with
  | nil =>
      intro hsorted
      simpa using hsorted
  | cons _ processed ih =>
      intro hsorted
      exact ih hsorted.2

omit [DecidableEq E] in
/-- In a sorted nonempty edge list, the head is no heavier than any member. -/
theorem weightSorted_head_le_of_mem {w : E → Nat} {e f : E}
    {suffix : List E} (hsorted : WeightSorted w (e :: suffix))
    (hf : f ∈ e :: suffix) :
    w e ≤ w f := by
  rw [List.mem_cons] at hf
  rcases hf with hfe | hfSuffix
  · simp [hfe]
  · exact hsorted.1 f hfSuffix

omit [DecidableEq V] [DecidableEq E] in
/--
If every crossing edge appears in {lit}`processed ++ e :: suffix`, and the
processed edge prefix contains no crossing edge for the current cut, then every
crossing edge appears at or after {lit}`e`.
-/
theorem crossing_mem_current_suffix_of_prefix_excludes
    {G : Graph V E} {S : Finset V} {processed suffix : List E} {e f : E}
    (hall :
      ∀ g, G.Crosses S g → g ∈ processed ++ e :: suffix)
    (hprefix :
      ∀ g, g ∈ processed → ¬ G.Crosses S g)
    (hcross : G.Crosses S f) :
    f ∈ e :: suffix := by
  have hfAll := hall f hcross
  rcases List.mem_append.mp hfAll with hfPrefix | hfSuffix
  · exact False.elim ((hprefix f hfPrefix) hcross)
  · exact hfSuffix

omit [DecidableEq V] [DecidableEq E] in
/--
Sorted edge order plus the processed-prefix exclusion invariant proves the
lightness side condition for the current Kruskal cut.

This isolates the CLRS sorted-order argument from the graph-specific proof that
previously processed edges do not cross the current component cut.
-/
theorem lightest_crossing_of_sorted_prefix {G : Graph V E} {w : E → Nat}
    {S : Finset V} {processed suffix : List E} {e : E}
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f, G.Crosses S f → f ∈ processed ++ e :: suffix)
    (hprefix :
      ∀ f, f ∈ processed → ¬ G.Crosses S f) :
    ∀ f, G.Crosses S f → w e ≤ w f := by
  intro f hcross
  have hsuffixSorted :
      WeightSorted w (e :: suffix) :=
    weightSorted_suffix_of_append w processed (e :: suffix) hsorted
  have hfSuffix :
      f ∈ e :: suffix :=
    crossing_mem_current_suffix_of_prefix_excludes
      (G := G) (S := S) (processed := processed) (suffix := suffix)
      (e := e) hall hprefix hcross
  exact weightSorted_head_le_of_mem hsuffixSorted hfSuffix

/--
Component-oracle cut certificate where the lightness field is discharged from
sorted edge order and a processed-prefix exclusion invariant.
-/
theorem cut_certificate_of_component_oracle_sorted_prefix
    {G : Graph V E} {P : Problem E} {w : E → Nat} (C : ComponentOracle G)
    {A : Finset E} {e : E} {processed suffix : List E}
    (haccept : acceptByComponent G C A e = true)
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f, G.Crosses (C.component A (G.src e)) f →
        f ∈ processed ++ e :: suffix)
    (hprefix :
      ∀ f, f ∈ processed →
        ¬ G.Crosses (C.component A (G.src e)) f)
    (hexchange :
      ∀ T, IsMSTExtending P w A T → e ∉ T →
        ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
          P.IsSpanningTree (insert e (T.erase f)) ∧
          A ⊆ insert e (T.erase f)) :
    CutCertificate G P w A (C.component A (G.src e)) e := by
  exact cut_certificate_of_component_oracle C haccept
    (lightest_crossing_of_sorted_prefix hsorted hall hprefix)
    hexchange


/-! ## Kruskal-style safe-edge induction -/

/-- A mathematical Kruskal pass over a fixed edge order.

The Boolean {lit}`accept A e` abstracts the cycle test: when it returns true, the
edge is inserted into the current forest; otherwise it is skipped.
-/
def kruskal (accept : Finset E → E → Bool) : List E → Finset E → Finset E
  | [], A => A
  | e :: es, A => kruskal accept es (if accept A e then insert e A else A)

/-- Prim's mathematical edge-accumulation pass.  The dynamic light-edge and
cut obligations are carried by `FiniteGraph.PrimTrace` below. -/
def prim : List E → Finset E → Finset E
  | [], A => A
  | e :: es, A => prim es (insert e A)

/-- Splitting an edge order into a processed prefix and a remaining suffix is
compatible with the mathematical Kruskal pass. -/
theorem kruskal_append (accept : Finset E → E → Bool)
    (processed suffix : List E) (A : Finset E) :
    kruskal accept (processed ++ suffix) A =
      kruskal accept suffix (kruskal accept processed A) := by
  induction processed generalizing A with
  | nil => rfl
  | cons e processed ih =>
      simp only [List.cons_append, kruskal]
      by_cases hacc : accept A e = true
      · simp only [if_pos hacc]
        exact ih (insert e A)
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        simp only [if_neg (by simpa [hfalse])]
        exact ih A

/-- The proof obligation needed by the abstract Kruskal induction: every edge
accepted by the cycle test is safe for the current prefix.  In a concrete graph
development this is discharged by a cut-property certificate. -/
structure KruskalCertificate (P : Problem E) (w : E → Nat)
    (accept : Finset E → E → Bool) : Prop where
  safe : ∀ A e, accept A e = true → SafeEdge P w A e

/-- A CLRS-style certificate for Kruskal: each accepted edge has a cut
certificate showing it is light across some cut respecting the current forest. -/
structure KruskalCutCertificate (G : Graph V E) (P : Problem E) (w : E → Nat)
    (accept : Finset E → E → Bool) : Prop where
  cut : ∀ A e, accept A e = true → ∃ S, CutCertificate G P w A S e

omit [DecidableEq V] in
theorem kruskal_certificate_of_cut_certificates {G : Graph V E} {P : Problem E}
    {w : E → Nat} {accept : Finset E → E → Bool}
    (cert : KruskalCutCertificate G P w accept) :
    KruskalCertificate P w accept := by
  refine ⟨?_⟩
  intro A e hacc
  rcases cert.cut A e hacc with ⟨S, hcut⟩
  exact safe_edge_of_lightest_crossing hcut

theorem kruskal_cut_certificate_of_component_oracle {G : Graph V E}
    {P : Problem E} {w : E → Nat} (C : ComponentOracle G)
    (hlight :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f)) :
    KruskalCutCertificate G P w (acceptByComponent G C) := by
  refine ⟨?_⟩
  intro A e hacc
  exact ⟨C.component A (G.src e),
    cut_certificate_of_component_oracle C hacc
      (hlight A e hacc) (hexchange A e hacc)⟩

theorem kruskal_extends_start (accept : Finset E → E → Bool)
    (edges : List E) (A : Finset E) :
    A ⊆ kruskal accept edges A := by
  induction edges generalizing A with
  | nil =>
      simp [kruskal]
  | cons e es ih =>
      by_cases hacc : accept A e = true
      · have hA : A ⊆ insert e A := Finset.subset_insert e A
        exact hA.trans (by simpa [kruskal, hacc] using ih (insert e A))
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        simpa [kruskal, hfalse] using ih A

/-- Kruskal never selects an edge outside the initial set or the scanned edge
list. -/
theorem kruskal_subset_of_start_and_edges (accept : Finset E → E → Bool)
    (edges : List E) {A B : Finset E}
    (hA : A ⊆ B) (hedges : ∀ e, e ∈ edges → e ∈ B) :
    kruskal accept edges A ⊆ B := by
  induction edges generalizing A with
  | nil =>
      simpa [kruskal] using hA
  | cons e es ih =>
      by_cases hacc : accept A e = true
      · have heB : e ∈ B := hedges e (by simp)
        have hinsert : insert e A ⊆ B := Finset.insert_subset heB hA
        have htail : ∀ f, f ∈ es → f ∈ B := by
          intro f hf
          exact hedges f (by simp [hf])
        simpa [kruskal, hacc] using ih hinsert htail
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        have htail : ∀ f, f ∈ es → f ∈ B := by
          intro f hf
          exact hedges f (by simp [hf])
        simpa [kruskal, hfalse] using ih hA htail

/--
After a Kruskal prefix has been processed by an exact component oracle, every
processed edge is accounted for: it is either selected in the current forest or
its endpoints are already connected in that forest.
-/
theorem processed_edge_mem_or_connected_of_exact_component_kruskal
    {G : Graph V E} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C) (processed : List E)
    (A : Finset E) :
    ∀ f, f ∈ processed →
      f ∈ kruskal (acceptByComponent G C) processed A ∨
        G.ConnectedIn (kruskal (acceptByComponent G C) processed A)
          (G.src f) (G.dst f) := by
  induction processed generalizing A with
  | nil =>
      intro f hf
      simp at hf
  | cons e es ih =>
      intro f hf
      rw [List.mem_cons] at hf
      by_cases hacc : acceptByComponent G C A e = true
      · rcases hf with hfe | hfes
        · left
          subst f
          have heInsert : e ∈ insert e A := Finset.mem_insert_self e A
          have hsubset :
              insert e A ⊆ kruskal (acceptByComponent G C) es (insert e A) :=
            kruskal_extends_start (acceptByComponent G C) es (insert e A)
          simpa [kruskal, hacc] using hsubset heInsert
        · simpa [kruskal, hacc] using ih (insert e A) f hfes
      · have hfalse : acceptByComponent G C A e = false := by
          cases h : acceptByComponent G C A e <;> simp [h] at hacc ⊢
        rcases hf with hfe | hfes
        · right
          subst f
          have hmem : G.dst e ∈ C.component A (G.src e) :=
            mem_component_of_reject hfalse
          have hconnA : G.ConnectedIn A (G.src e) (G.dst e) :=
            (hexact A (G.src e) (G.dst e)).1 hmem
          have hsubset : A ⊆ kruskal (acceptByComponent G C) es A :=
            kruskal_extends_start (acceptByComponent G C) es A
          have hconnFinal :
              G.ConnectedIn (kruskal (acceptByComponent G C) es A)
                (G.src e) (G.dst e) :=
            Graph.connected_mono hsubset hconnA
          simpa [kruskal, hfalse] using hconnFinal
        · simpa [kruskal, hfalse] using ih A f hfes

/--
After an exact-component Kruskal pass, every processed edge has connected
endpoints in the final selected set.
-/
theorem processed_edge_connected_of_exact_component_kruskal
    {G : Graph V E} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C) (processed : List E)
    (A : Finset E) :
    ∀ f, f ∈ processed →
      G.ConnectedIn (kruskal (acceptByComponent G C) processed A)
        (G.src f) (G.dst f) := by
  intro f hf
  rcases processed_edge_mem_or_connected_of_exact_component_kruskal C hexact
      processed A f hf with hmem | hconn
  · exact Graph.connected_of_mem_edge hmem
  · exact hconn

/--
Exact components derive the processed-prefix exclusion invariant needed by the
sorted-order Kruskal lightness proof.
-/
theorem processed_prefix_excludes_of_exact_component_kruskal
    {G : Graph V E} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C) (processed : List E)
    (A : Finset E) (root : V) :
    ∀ f, f ∈ processed →
      ¬ G.Crosses
        (C.component (kruskal (acceptByComponent G C) processed A) root) f := by
  intro f hf
  exact not_crosses_component_of_mem_or_connected hexact
    (processed_edge_mem_or_connected_of_exact_component_kruskal C hexact
      processed A f hf)

/--
Kruskal's sorted edge order proves lightness without a standalone prefix
exclusion hypothesis when the component oracle is exact.
-/
theorem lightest_crossing_of_exact_component_kruskal_prefix
    {G : Graph V E} {w : E → Nat} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C)
    {processed suffix : List E} {A : Finset E} {e : E}
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f,
        G.Crosses
            (C.component (kruskal (acceptByComponent G C) processed A)
              (G.src e)) f →
          f ∈ processed ++ e :: suffix) :
    ∀ f,
      G.Crosses
          (C.component (kruskal (acceptByComponent G C) processed A)
            (G.src e)) f →
        w e ≤ w f := by
  exact lightest_crossing_of_sorted_prefix hsorted hall
    (processed_prefix_excludes_of_exact_component_kruskal C hexact
      processed A (G.src e))

/--
Exact-component cut certificate for the current Kruskal edge.  This packages
the derived processed-prefix exclusion invariant with the sorted edge order.
-/
theorem cut_certificate_of_exact_component_kruskal_prefix
    {G : Graph V E} {P : Problem E} {w : E → Nat} (C : ComponentOracle G)
    (hexact : ExactComponentOracle G C)
    {processed suffix : List E} {A : Finset E} {e : E}
    (haccept :
      acceptByComponent G C
          (kruskal (acceptByComponent G C) processed A) e = true)
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f,
        G.Crosses
            (C.component (kruskal (acceptByComponent G C) processed A)
              (G.src e)) f →
          f ∈ processed ++ e :: suffix)
    (hexchange :
      ∀ T,
        IsMSTExtending P w
            (kruskal (acceptByComponent G C) processed A) T →
          e ∉ T →
            ∃ f, f ∈ T ∧
              G.Crosses
                  (C.component
                    (kruskal (acceptByComponent G C) processed A)
                    (G.src e)) f ∧
                P.IsSpanningTree (insert e (T.erase f)) ∧
                kruskal (acceptByComponent G C) processed A ⊆
                  insert e (T.erase f)) :
    CutCertificate G P w
      (kruskal (acceptByComponent G C) processed A)
      (C.component (kruskal (acceptByComponent G C) processed A) (G.src e))
      e := by
  exact cut_certificate_of_component_oracle C haccept
    (lightest_crossing_of_exact_component_kruskal_prefix C hexact
      hsorted hall)
    hexchange

private theorem optimal_for_smaller_prefix {P : Problem E} {w : E → Nat}
    {A₀ A T T' : Finset E} (hA₀A : A₀ ⊆ A)
    (hcur : IsMSTExtending P w A T) (hbase : IsMSTExtending P w A₀ T)
    (hnew : IsMSTExtending P w A T') :
    IsMSTExtending P w A₀ T' := by
  refine ⟨hnew.tree, ?_, ?_⟩
  · exact hA₀A.trans hnew.includes
  · intro U hUtree hUincludes
    exact (hnew.optimal T hcur.tree hcur.includes).trans
      (hbase.optimal U hUtree hUincludes)

theorem kruskal_preserves_mst {P : Problem E} {w : E → Nat}
    {accept : Finset E → E → Bool} (cert : KruskalCertificate P w accept)
    (edges : List E) {A₀ A T : Finset E} (hA₀A : A₀ ⊆ A)
    (hcur : IsMSTExtending P w A T) (hbase : IsMSTExtending P w A₀ T) :
    ∃ T', IsMSTExtending P w (kruskal accept edges A) T' ∧
      IsMSTExtending P w A₀ T' := by
  induction edges generalizing A T with
  | nil =>
      exact ⟨T, by simpa [kruskal] using hcur, hbase⟩
  | cons e es ih =>
      by_cases hacc : accept A e = true
      · rcases cert.safe A e hacc T hcur with ⟨T₁, hnext, hprefix⟩
        have hbase₁ : IsMSTExtending P w A₀ T₁ :=
          optimal_for_smaller_prefix hA₀A hcur hbase hprefix
        have hA₀next : A₀ ⊆ insert e A :=
          hA₀A.trans (Finset.subset_insert e A)
        simpa [kruskal, hacc] using ih hA₀next hnext hbase₁
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        simpa [kruskal, hfalse] using ih hA₀A hcur hbase

/-- Mathematical Kruskal optimality.

If the accept rule only accepts safe edges, the initial prefix has an optimum,
and the final selected edge set is itself a maximal spanning tree, then the
Kruskal result is an optimum extending the initial prefix.  The final maximality
assumption is the graph-specific fact that a spanning tree cannot be properly
extended by another spanning tree; concrete graph modules can prove it from the
usual cardinality characterization of spanning trees.
-/
theorem kruskal_optimal {P : Problem E} {w : E → Nat}
    {accept : Finset E → E → Bool} (cert : KruskalCertificate P w accept)
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal accept edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal accept edges A₀ ⊆ T →
        T = kruskal accept edges A₀) :
    IsMSTExtending P w A₀ (kruskal accept edges A₀) := by
  rcases kruskal_preserves_mst cert edges (Subset.rfl : A₀ ⊆ A₀) hstart hstart with
    ⟨T, hfinal, hglobal⟩
  have hT : T = kruskal accept edges A₀ :=
    hfinal_maximal T hfinal.tree hfinal.includes
  refine ⟨hfinal_tree, ?_, ?_⟩
  · simpa [← hT] using hglobal.includes
  · intro U hUtree hUincludes
    simpa [hT] using hglobal.optimal U hUtree hUincludes

omit [DecidableEq V] in
/-- Kruskal optimality stated directly from CLRS cut certificates. -/
theorem kruskal_optimal_of_cut_certificates {G : Graph V E} {P : Problem E}
    {w : E → Nat} {accept : Finset E → E → Bool}
    (cert : KruskalCutCertificate G P w accept) (edges : List E)
    {A₀ T₀ : Finset E} (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal accept edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal accept edges A₀ ⊆ T →
        T = kruskal accept edges A₀) :
    IsMSTExtending P w A₀ (kruskal accept edges A₀) := by
  exact kruskal_optimal (kruskal_certificate_of_cut_certificates cert)
    edges hstart hfinal_tree hfinal_maximal

theorem kruskal_optimal_of_component_oracle {G : Graph V E} {P : Problem E}
    {w : E → Nat} (C : ComponentOracle G)
    (hlight :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal (acceptByComponent G C) edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal (acceptByComponent G C) edges A₀ ⊆ T →
        T = kruskal (acceptByComponent G C) edges A₀) :
    IsMSTExtending P w A₀ (kruskal (acceptByComponent G C) edges A₀) := by
  exact kruskal_optimal_of_cut_certificates
    (kruskal_cut_certificate_of_component_oracle C hlight hexchange)
    edges hstart hfinal_tree hfinal_maximal

/-- A verified executable cycle test.  A union-find implementation should
provide an {lit}`accept` function and prove that it agrees with the component oracle. -/
structure CycleTestImplementation (G : Graph V E) (C : ComponentOracle G) where
  accept : Finset E → E → Bool
  correct : ∀ A e, accept A e = acceptByComponent G C A e

/-- The canonical executable cycle test associated to a component oracle. -/
def componentCycleTest (G : Graph V E) (C : ComponentOracle G) :
    CycleTestImplementation G C where
  accept := acceptByComponent G C
  correct := by
    intro A e
    rfl

theorem kruskal_optimal_of_cycle_test {G : Graph V E} {P : Problem E}
    {w : E → Nat} {C : ComponentOracle G}
    (impl : CycleTestImplementation G C)
    (hlight :
      ∀ A e, impl.accept A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, impl.accept A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending P w A₀ T₀)
    (hfinal_tree : P.IsSpanningTree (kruskal impl.accept edges A₀))
    (hfinal_maximal :
      ∀ T, P.IsSpanningTree T → kruskal impl.accept edges A₀ ⊆ T →
        T = kruskal impl.accept edges A₀) :
    IsMSTExtending P w A₀ (kruskal impl.accept edges A₀) := by
  have hsame : impl.accept = acceptByComponent G C := by
    funext A e
    exact impl.correct A e
  have hlight' :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ f, G.Crosses (C.component A (G.src e)) f → w e ≤ w f := by
    intro A e hacc
    exact hlight A e (by simpa [hsame] using hacc)
  have hexchange' :
      ∀ A e, acceptByComponent G C A e = true →
        ∀ T, IsMSTExtending P w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.Crosses (C.component A (G.src e)) f ∧
            P.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f) := by
    intro A e hacc
    exact hexchange A e (by simpa [hsame] using hacc)
  have hfinal_tree' :
      P.IsSpanningTree (kruskal (acceptByComponent G C) edges A₀) := by
    simpa [hsame] using hfinal_tree
  have hfinal_maximal' :
      ∀ T, P.IsSpanningTree T → kruskal (acceptByComponent G C) edges A₀ ⊆ T →
        T = kruskal (acceptByComponent G C) edges A₀ := by
    intro T hT hsub
    simpa [hsame] using hfinal_maximal T hT (by simpa [hsame] using hsub)
  simpa [hsame] using
    (kruskal_optimal_of_component_oracle (G := G) (P := P) (w := w) C
      hlight' hexchange' edges hstart hfinal_tree' hfinal_maximal')

namespace FiniteGraph

/-- The empty edge set is a forest. -/
theorem isForest_empty (G : FiniteGraph V E) :
    G.IsForest ∅ := by
  intro e he
  simp at he

/-- Forest adjacency cannot be a self-loop. -/
theorem ne_of_adjIn_of_isForest (G : FiniteGraph V E) {A : Finset E}
    (hforest : G.IsForest A) {u v : V} (hadj : G.toGraph.AdjIn A u v) :
    u ≠ v := by
  intro huv
  subst v
  rcases hadj with ⟨e, heA, hend⟩
  apply hforest e heA
  rcases hend with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
  · simpa [hsrc, hdst] using
      (Graph.connected_refl G.toGraph (A.erase e) u)
  · simpa [hsrc, hdst] using
      (Graph.connected_refl G.toGraph (A.erase e) u)

/-- Connectivity in a forest lifts to reachability in its loop-free simple
graph view. -/
theorem reachable_selectedSimpleGraph_of_connected (G : FiniteGraph V E)
    {A : Finset E} (hforest : G.IsForest A) {u v : V}
    (hconn : G.toGraph.ConnectedIn A u v) :
    (G.toGraph.selectedSimpleGraph A).Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  induction hconn with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath hadj ih =>
      exact Relation.ReflTransGen.tail ih
        ⟨G.ne_of_adjIn_of_isForest hforest hadj, hadj⟩

/-- The simple-graph view of a selected forest is acyclic: every unlabelled
edge is a bridge because erasing its unique labelled representative
disconnects its endpoints. -/
theorem selectedSimpleGraph_isAcyclic (G : FiniteGraph V E)
    {A : Finset E} (hforest : G.IsForest A) :
    (G.toGraph.selectedSimpleGraph A).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro edge hedge
  obtain ⟨u, v⟩ := edge
  have hadj : (G.toGraph.selectedSimpleGraph A).Adj u v :=
    (G.toGraph.selectedSimpleGraph A).mem_edgeSet.mp hedge
  rcases hadj.2 with ⟨f, hfA, hfEnds⟩
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  have hconn : G.toGraph.ConnectedIn (A.erase f) u v :=
    Graph.connectedIn_erase_of_reachable_delete_selectedEdge hfEnds hreach
  apply hforest f hfA
  rcases hfEnds with ⟨hsrc, hdst⟩ | ⟨hsrc, hdst⟩
  · simpa [hsrc, hdst] using hconn
  · simpa [hsrc, hdst] using (Graph.connected_symm hconn)

/-- The canonical simple path selected from a finite forest connection.  The
choice is noncomputable, but its result is a genuine Mathlib path and therefore
contains no repeated vertices. -/
noncomputable def canonicalSimplePath (G : FiniteGraph V E) {A : Finset E}
    (hforest : G.IsForest A) {u v : V}
    (hconn : G.toGraph.ConnectedIn A u v) :
    (G.toGraph.selectedSimpleGraph A).Path u v := by
  have hreach : (G.toGraph.selectedSimpleGraph A).Reachable u v :=
    G.reachable_selectedSimpleGraph_of_connected hforest hconn
  let p := Classical.choose hreach.exists_isPath
  exact ⟨p, Classical.choose_spec hreach.exists_isPath⟩

/-- The canonical forest path is the unique simple path between its endpoints. -/
theorem canonicalSimplePath_unique (G : FiniteGraph V E) {A : Finset E}
    (hforest : G.IsForest A) {u v : V}
    (hconn : G.toGraph.ConnectedIn A u v)
    (p : (G.toGraph.selectedSimpleGraph A).Path u v) :
    p = G.canonicalSimplePath hforest hconn :=
  (G.selectedSimpleGraph_isAcyclic hforest).path_unique _ _

/-- The canonical tree path automatically supplies the crossing edge and
{lit}`ExchangePath` certificate required by the CLRS exchange argument. -/
theorem exists_crossing_exchangePath_of_spanningTree
    (G : FiniteGraph V E) {T : Finset E} {S : Finset V} {e : E}
    (hT : G.IsSpanningTree T) (heG : e ∈ G.edges)
    (hcross : G.toGraph.Crosses S e) :
    ∃ f, f ∈ T ∧ G.toGraph.Crosses S f ∧
      G.toGraph.ExchangePath T e f := by
  have hsrc : G.src e ∈ G.vertices := G.src_mem e heG
  have hdst : G.dst e ∈ G.vertices := G.dst_mem e heG
  have hconn : G.toGraph.ConnectedIn T (G.src e) (G.dst e) :=
    hT.2.1 (G.src e) hsrc (G.dst e) hdst
  let p := G.canonicalSimplePath hT.2.2 hconn
  rcases hcross with hcross | hcross
  · rcases Graph.exists_pathExchange_of_simplePath_crosses
        p.1 p.2 hcross.1 hcross.2 with ⟨f, hfT, hfCross, hfPath⟩
    exact ⟨f, hfT, hfCross, by simpa [Graph.ExchangePath, Graph.PathExchange] using hfPath⟩
  · have hpReverse : p.1.reverse.IsPath := p.2.reverse
    rcases Graph.exists_pathExchange_of_simplePath_crosses
        p.1.reverse hpReverse hcross.1 hcross.2 with
      ⟨f, hfT, hfCross, hfPath⟩
    have hfPath' : G.toGraph.PathExchange T (G.src e) (G.dst e) f :=
      Graph.PathExchange.swap hfPath
    exact ⟨f, hfT, hfCross,
      by simpa [Graph.ExchangePath, Graph.PathExchange] using hfPath'⟩

private theorem connected_insert_erase_self_eq
    {A : Finset E} {e : E} (heA : e ∉ A) :
    (insert e A).erase e = A := by
  ext x
  by_cases hxe : x = e
  · subst x
    simp [heA]
  · simp [hxe]

private theorem erase_insert_comm_of_ne {A : Finset E} {e f : E}
    (hef : e ≠ f) :
    (insert e A).erase f = insert e (A.erase f) := by
  ext x
  by_cases hxf : x = f
  · subst x
    simp [Ne.symm hef]
  · simp [hxf]

omit [DecidableEq V] in
private theorem connected_insert_bridge_case_left
    {G : Graph V E} {A : Finset E} {e f : E} (hfA : f ∈ A)
    (hleft : G.ConnectedIn (A.erase f) (G.src f) (G.src e))
    (hright : G.ConnectedIn (A.erase f) (G.dst e) (G.dst f)) :
    G.ConnectedIn A (G.src e) (G.dst e) := by
  have h₁ : G.ConnectedIn A (G.src e) (G.src f) :=
    Graph.connected_symm (Graph.connected_mono (Finset.erase_subset f A) hleft)
  have hf : G.ConnectedIn A (G.src f) (G.dst f) :=
    Graph.connected_of_mem_edge hfA
  have h₂ : G.ConnectedIn A (G.dst f) (G.dst e) :=
    Graph.connected_symm (Graph.connected_mono (Finset.erase_subset f A) hright)
  exact Graph.connected_trans (Graph.connected_trans h₁ hf) h₂

omit [DecidableEq V] in
private theorem connected_insert_bridge_case_right
    {G : Graph V E} {A : Finset E} {e f : E} (hfA : f ∈ A)
    (hleft : G.ConnectedIn (A.erase f) (G.src f) (G.dst e))
    (hright : G.ConnectedIn (A.erase f) (G.src e) (G.dst f)) :
    G.ConnectedIn A (G.src e) (G.dst e) := by
  have h₁ : G.ConnectedIn A (G.src e) (G.dst f) :=
    Graph.connected_mono (Finset.erase_subset f A) hright
  have hf : G.ConnectedIn A (G.dst f) (G.src f) :=
    Graph.connected_symm (Graph.connected_of_mem_edge hfA)
  have h₂ : G.ConnectedIn A (G.src f) (G.dst e) :=
    Graph.connected_mono (Finset.erase_subset f A) hleft
  exact Graph.connected_trans (Graph.connected_trans h₁ hf) h₂

/--
Inserting an edge whose endpoints are disconnected preserves the edge-removal
forest invariant.
-/
theorem isForest_insert_of_not_connected (G : FiniteGraph V E)
    {A : Finset E} {e : E} (hforest : G.IsForest A)
    (hnot : ¬ G.toGraph.ConnectedIn A (G.src e) (G.dst e)) :
    G.IsForest (insert e A) := by
  have heA : e ∉ A := by
    intro he
    exact hnot (Graph.connected_of_mem_edge he)
  intro f hf hconn
  rw [Finset.mem_insert] at hf
  rcases hf with hfe | hfA
  · subst f
    have herase : (insert e A).erase e = A :=
      connected_insert_erase_self_eq (A := A) (e := e) heA
    exact hnot (by simpa [herase] using hconn)
  · have hfe : f ≠ e := by
      intro h
      exact heA (h ▸ hfA)
    have hef : e ≠ f := Ne.symm hfe
    have herase : (insert e A).erase f = insert e (A.erase f) :=
      erase_insert_comm_of_ne hef
    have hconn' :
        G.toGraph.ConnectedIn (insert e (A.erase f)) (G.src f) (G.dst f) := by
      simpa [herase] using hconn
    rcases Graph.connected_insert_edge_cases hconn' with hbase |
        ⟨⟨hleft, hright⟩ | ⟨hleft, hright⟩⟩
    · exact hforest f hfA hbase
    · exact hnot (connected_insert_bridge_case_left hfA hleft hright)
    · exact hnot (connected_insert_bridge_case_right hfA hleft hright)

/-- The edge-removal forest invariant is downward closed under edge subsets. -/
theorem isForest_mono (G : FiniteGraph V E) {A B : Finset E}
    (hforest : G.IsForest B) (hAB : A ⊆ B) :
    G.IsForest A := by
  intro e heA hconn
  have hsubset : A.erase e ⊆ B.erase e := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, hAB (Finset.mem_of_mem_erase hx)⟩
  exact hforest e (hAB heA) (Graph.connected_mono hsubset hconn)

/--
Finite-graph bridge from a cycle-style connection to the reusable
{lit}`ExchangePath` certificate.  In a spanning tree, deleting {lit}`f`
disconnects its endpoints; if inserting {lit}`e` reconnects them, Lean can
decompose that connection into the two sides of the exchange path.
-/
theorem exchangePath_of_insert_connects_erased_edge (G : FiniteGraph V E)
    {T : Finset E} {e f : E}
    (hT : G.IsSpanningTree T) (hfT : f ∈ T)
    (hconn :
      G.toGraph.ConnectedIn (insert e (T.erase f)) (G.src f) (G.dst f)) :
    G.toGraph.ExchangePath T e f := by
  exact Graph.exchangePath_of_insert_connected hconn (hT.2.2 f hfT)

/--
Named finite-graph wrapper for the compact inserted-edge connection interface.
In a spanning tree, erasing {lit}`f` disconnects its endpoints, so the compact
cycle-style witness is equivalent to an {lit}`ExchangePath` certificate.
-/
theorem exchangePath_iff_insertedEdgeConnection_of_spanningTree
    (G : FiniteGraph V E) {T : Finset E} {e f : E}
    (hT : G.IsSpanningTree T) (hfT : f ∈ T) :
    G.toGraph.ExchangePath T e f ↔ G.toGraph.InsertedEdgeConnection T e f :=
  Graph.exchangePath_iff_insertedEdgeConnection (hT.2.2 f hfT)

/--
Finite-graph bridge from the named inserted-edge connection to the reusable
{lit}`ExchangePath` certificate.
-/
theorem exchangePath_of_insertedEdgeConnection (G : FiniteGraph V E)
    {T : Finset E} {e f : E}
    (hT : G.IsSpanningTree T) (hfT : f ∈ T)
    (hconn : G.toGraph.InsertedEdgeConnection T e f) :
    G.toGraph.ExchangePath T e f :=
  (G.exchangePath_iff_insertedEdgeConnection_of_spanningTree hT hfT).2 hconn

/--
If a path-decomposition certificate says that new edge {lit}`e` reconnects the
two components produced by deleting tree edge {lit}`f`, then replacing
{lit}`f` by {lit}`e` preserves the finite-graph spanning-tree property.
-/
theorem spanningTree_exchange_of_path_certificate (G : FiniteGraph V E)
    {T : Finset E} {e f : E}
    (hT : G.IsSpanningTree T) (heG : e ∈ G.edges) (hfT : f ∈ T)
    (hpath : G.toGraph.ExchangePath T e f) :
    G.IsSpanningTree (insert e (T.erase f)) := by
  have hnew_subset : insert e (T.erase f) ⊆ G.edges := by
    intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with hxe | hxT
    · exact hxe ▸ heG
    · exact hT.1 (Finset.mem_of_mem_erase hxT)
  have hnot_connected :
      ¬ G.toGraph.ConnectedIn (T.erase f) (G.src e) (G.dst e) := by
    intro he_conn
    have hf_conn : G.toGraph.ConnectedIn (T.erase f) (G.src f) (G.dst f) := by
      rcases hpath with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact Graph.connected_trans (Graph.connected_trans hleft he_conn) hright
      · exact Graph.connected_trans (Graph.connected_trans hleft
          (Graph.connected_symm he_conn)) hright
    exact hT.2.2 f hfT hf_conn
  have hforest_erase : G.IsForest (T.erase f) :=
    G.isForest_mono hT.2.2 (Finset.erase_subset f T)
  have hforest_new : G.IsForest (insert e (T.erase f)) :=
    G.isForest_insert_of_not_connected hforest_erase hnot_connected
  have hedge :
      ∀ g, g ∈ T →
        G.toGraph.ConnectedIn (insert e (T.erase f)) (G.src g) (G.dst g) := by
    intro g hgT
    by_cases hgf : g = f
    · subst g
      exact Graph.exchangePath_connected_insert hpath
    · have hgErase : g ∈ T.erase f := Finset.mem_erase.mpr ⟨hgf, hgT⟩
      have hgNew : g ∈ insert e (T.erase f) := Finset.mem_insert_of_mem hgErase
      exact Graph.connected_of_mem_edge hgNew
  have hspans_new : G.Spans (insert e (T.erase f)) := by
    intro u hu v hv
    exact Graph.connected_of_edgewise_connected hedge (hT.2.1 u hu v hv)
  exact ⟨hnew_subset, hspans_new, hforest_new⟩

/--
Cut-local exchange certificate from an explicit path-decomposition certificate.
This packages the reusable finite-graph part needed by the CLRS safe-edge
theorem.
-/
theorem cut_exchange_certificate (G : FiniteGraph V E)
    {A T : Finset E} {S : Finset V} {e f : E}
    (hT : G.IsSpanningTree T) (hAT : A ⊆ T)
    (hrespects : G.toGraph.Respects S A)
    (heG : e ∈ G.edges) (hfT : f ∈ T)
    (hfCross : G.toGraph.Crosses S f)
    (hpath : G.toGraph.ExchangePath T e f) :
    f ∈ T ∧ G.toGraph.Crosses S f ∧
      G.IsSpanningTree (insert e (T.erase f)) ∧
      A ⊆ insert e (T.erase f) := by
  have hf_not_A : f ∉ A := by
    intro hfA
    exact hrespects f hfA hfCross
  refine ⟨hfT, hfCross,
    G.spanningTree_exchange_of_path_certificate hT heG hfT hpath, ?_⟩
  intro x hxA
  exact Finset.mem_insert_of_mem
    (Finset.mem_erase.mpr ⟨fun hxf => hf_not_A (hxf ▸ hxA), hAT hxA⟩)

/--
Existential replacement form: once a crossing tree edge is accompanied by an
{lit}`ExchangePath` certificate, Lean constructs the exchanged spanning tree
and proves that the accepted prefix is preserved.
-/
theorem exists_replacement_spanning_tree_of_cut (G : FiniteGraph V E)
    {A T : Finset E} {S : Finset V} {e : E}
    (hT : G.IsSpanningTree T) (hAT : A ⊆ T)
    (hrespects : G.toGraph.Respects S A) (heG : e ∈ G.edges)
    (hpath :
      ∃ f, f ∈ T ∧ G.toGraph.Crosses S f ∧
        G.toGraph.ExchangePath T e f) :
    ∃ f, f ∈ T ∧ G.toGraph.Crosses S f ∧
      G.IsSpanningTree (insert e (T.erase f)) ∧
      A ⊆ insert e (T.erase f) := by
  rcases hpath with ⟨f, hfT, hfCross, hcert⟩
  exact ⟨f, G.cut_exchange_certificate hT hAT hrespects heG hfT hfCross hcert⟩

/--
Finite-graph cut certificate from a light crossing edge and explicit exchange
paths for optimum trees.  This is the bridge between the mathematical
path/cycle exchange argument and the abstract safe-edge theorem.
-/
theorem cutCertificate_of_lightest_crossing (G : FiniteGraph V E)
    {w : E → Nat} {A : Finset E} {S : Finset V} {e : E}
    (heG : e ∈ G.edges) (hcross : G.toGraph.Crosses S e)
    (hrespects : G.toGraph.Respects S A)
    (hlight : ∀ f, G.toGraph.Crosses S f → w e ≤ w f)
    (hexchangePath :
      ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
        ∃ f, f ∈ T ∧ G.toGraph.Crosses S f ∧
          G.toGraph.ExchangePath T e f) :
    CutCertificate G.toGraph G.toProblem w A S e := by
  refine ⟨hcross, hrespects, hlight, ?_⟩
  intro T hT heT
  rcases hexchangePath T hT heT with ⟨f, hfT, hfCross, hpath⟩
  rcases G.cut_exchange_certificate hT.tree hT.includes hrespects
      heG hfT hfCross hpath with
    ⟨hfT', hfCross', htree, hextends⟩
  exact ⟨f, hfT', hfCross', htree, hextends⟩

/-- Finite-graph cut certificate with the exchange path generated
automatically from the canonical simple path in each optimum tree. -/
theorem cutCertificate_of_lightest_crossing_auto (G : FiniteGraph V E)
    {w : E → Nat} {A : Finset E} {S : Finset V} {e : E}
    (heG : e ∈ G.edges) (hcross : G.toGraph.Crosses S e)
    (hrespects : G.toGraph.Respects S A)
    (hlight : ∀ f, G.toGraph.Crosses S f → w e ≤ w f) :
    CutCertificate G.toGraph G.toProblem w A S e := by
  exact G.cutCertificate_of_lightest_crossing heG hcross hrespects hlight
    (by
      intro T hT _heT
      exact G.exists_crossing_exchangePath_of_spanningTree hT.tree heG hcross)

/-- The finite-graph CLRS cut property with no user-supplied cycle-exchange
certificate. -/
theorem safeEdge_of_lightest_crossing_auto (G : FiniteGraph V E)
    {w : E → Nat} {A : Finset E} {S : Finset V} {e : E}
    (heG : e ∈ G.edges) (hcross : G.toGraph.Crosses S e)
    (hrespects : G.toGraph.Respects S A)
    (hlight : ∀ f, G.toGraph.Crosses S f → w e ≤ w f) :
    SafeEdge G.toProblem w A e :=
  safe_edge_of_lightest_crossing
    (G.cutCertificate_of_lightest_crossing_auto heG hcross hrespects hlight)

/-- Exact-component Kruskal prefix certificate with both processed-prefix
lightness and the tree-exchange witness discharged internally. -/
theorem cutCertificate_of_exactComponentKruskalPrefix_auto
    (G : FiniteGraph V E) {w : E → Nat}
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    {processed suffix : List E} {A : Finset E} {e : E}
    (heG : e ∈ G.edges)
    (haccept :
      acceptByComponent G.toGraph C
          (kruskal (acceptByComponent G.toGraph C) processed A) e = true)
    (hsorted : WeightSorted w (processed ++ e :: suffix))
    (hall :
      ∀ f,
        G.toGraph.Crosses
            (C.component (kruskal (acceptByComponent G.toGraph C) processed A)
              (G.src e)) f →
          f ∈ processed ++ e :: suffix) :
    CutCertificate G.toGraph G.toProblem w
      (kruskal (acceptByComponent G.toGraph C) processed A)
      (C.component (kruskal (acceptByComponent G.toGraph C) processed A)
        (G.src e)) e := by
  have hnotMem :
      G.dst e ∉ C.component
        (kruskal (acceptByComponent G.toGraph C) processed A) (G.src e) :=
    not_mem_component_of_accept haccept
  have hcross :
      G.toGraph.Crosses
        (C.component (kruskal (acceptByComponent G.toGraph C) processed A)
          (G.src e)) e :=
    Or.inl ⟨C.mem_self _ _, hnotMem⟩
  exact G.cutCertificate_of_lightest_crossing_auto heG hcross
    (C.respects _ _)
    (lightest_crossing_of_exact_component_kruskal_prefix C hexact hsorted hall)

/-- Recursive safe-edge induction for one fixed sorted Kruskal edge order.
The processed-prefix exclusion and cycle-exchange certificate are both
constructed at the point where an edge is accepted. -/
private theorem kruskal_preserves_mst_sorted_exact_aux
    (G : FiniteGraph V E) {w : E → Nat}
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (processed suffix : List E) {A₀ T : Finset E}
    (hsorted : WeightSorted w (processed ++ suffix))
    (hall : ∀ S f, G.toGraph.Crosses S f → f ∈ processed ++ suffix)
    (hedges : ∀ e, e ∈ processed ++ suffix → e ∈ G.edges)
    (hcur : IsMSTExtending G.toProblem w
      (kruskal (acceptByComponent G.toGraph C) processed A₀) T)
    (hbase : IsMSTExtending G.toProblem w A₀ T) :
    ∃ T', IsMSTExtending G.toProblem w A₀ T' ∧
      IsMSTExtending G.toProblem w
        (kruskal (acceptByComponent G.toGraph C) (processed ++ suffix) A₀) T' := by
  induction suffix generalizing processed T with
  | nil =>
      exact ⟨T, hbase, by simpa using hcur⟩
  | cons e suffix ih =>
      let accept := acceptByComponent G.toGraph C
      let A := kruskal accept processed A₀
      by_cases hacc : accept A e = true
      · have heG : e ∈ G.edges := hedges e (by simp)
        have hcut : CutCertificate G.toGraph G.toProblem w A
            (C.component A (G.src e)) e := by
          simpa [accept, A] using
            (G.cutCertificate_of_exactComponentKruskalPrefix_auto C hexact
              heG hacc hsorted (by
                intro f hf
                exact hall _ f hf))
        rcases (safe_edge_of_lightest_crossing hcut) T hcur with
          ⟨T₁, hnext, hprefix⟩
        have hA₀A : A₀ ⊆ A := by
          exact kruskal_extends_start accept processed A₀
        have hbase₁ : IsMSTExtending G.toProblem w A₀ T₁ :=
          optimal_for_smaller_prefix hA₀A hcur hbase hprefix
        have hprocessed :
            kruskal accept (processed ++ [e]) A₀ = insert e A := by
          rw [kruskal_append]
          simp [kruskal, hacc, A]
        have hnext' : IsMSTExtending G.toProblem w
            (kruskal accept (processed ++ [e]) A₀) T₁ := by
          rw [hprocessed]
          exact hnext
        have hsorted' : WeightSorted w ((processed ++ [e]) ++ suffix) := by
          simpa [List.append_assoc] using hsorted
        have hall' : ∀ S f, G.toGraph.Crosses S f →
            f ∈ (processed ++ [e]) ++ suffix := by
          intro S f hf
          simpa [List.append_assoc] using hall S f hf
        have hedges' : ∀ f, f ∈ (processed ++ [e]) ++ suffix →
            f ∈ G.edges := by
          intro f hf
          exact hedges f (by simpa [List.append_assoc] using hf)
        have hrec := ih (processed := processed ++ [e]) (T := T₁)
          hsorted' hall' hedges' hnext' hbase₁
        simpa [List.append_assoc] using hrec
      · have hfalse : accept A e = false := by
          cases h : accept A e <;> simp [h] at hacc ⊢
        have hprocessed : kruskal accept (processed ++ [e]) A₀ = A := by
          rw [kruskal_append]
          simp [kruskal, hfalse, A]
        have hcur' : IsMSTExtending G.toProblem w
            (kruskal accept (processed ++ [e]) A₀) T := by
          rw [hprocessed]
          exact hcur
        have hsorted' : WeightSorted w ((processed ++ [e]) ++ suffix) := by
          simpa [List.append_assoc] using hsorted
        have hall' : ∀ S f, G.toGraph.Crosses S f →
            f ∈ (processed ++ [e]) ++ suffix := by
          intro S f hf
          simpa [List.append_assoc] using hall S f hf
        have hedges' : ∀ f, f ∈ (processed ++ [e]) ++ suffix →
            f ∈ G.edges := by
          intro f hf
          exact hedges f (by simpa [List.append_assoc] using hf)
        have hrec := ih (processed := processed ++ [e]) (T := T)
          hsorted' hall' hedges' hcur' hbase
        simpa [List.append_assoc] using hrec

/-- A sorted exact-component Kruskal pass preserves an optimum witness while
deriving every local light-edge and exchange obligation internally. -/
theorem kruskal_preserves_mst_of_sorted_exact_component
    (G : FiniteGraph V E) {w : E → Nat}
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) {A₀ T₀ : Finset E}
    (hsorted : WeightSorted w edges)
    (hall : ∀ S f, G.toGraph.Crosses S f → f ∈ edges)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hstart : IsMSTExtending G.toProblem w A₀ T₀) :
    ∃ T, IsMSTExtending G.toProblem w A₀ T ∧
      IsMSTExtending G.toProblem w
        (kruskal (acceptByComponent G.toGraph C) edges A₀) T := by
  simpa using
    (kruskal_preserves_mst_sorted_exact_aux G C hexact [] edges
      hsorted hall hedges hstart hstart)

/-- Prefix-local sorted lightness plus canonical exchange paths prove
Kruskal optimality once the accepted set is known to be a spanning tree. -/
theorem kruskal_optimal_of_sorted_exact_component
    (G : FiniteGraph V E) {w : E → Nat}
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) {A₀ T₀ : Finset E}
    (hsorted : WeightSorted w edges)
    (hall : ∀ S f, G.toGraph.Crosses S f → f ∈ edges)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal : G.IsSpanningTree
      (kruskal (acceptByComponent G.toGraph C) edges A₀)) :
    IsMSTExtending G.toProblem w A₀
      (kruskal (acceptByComponent G.toGraph C) edges A₀) := by
  rcases G.kruskal_preserves_mst_of_sorted_exact_component C hexact edges
      hsorted hall hedges hstart with ⟨T, hglobal, hprefix⟩
  have hEq : T = kruskal (acceptByComponent G.toGraph C) edges A₀ :=
    G.spanning_tree_maximal hfinal hprefix.tree hprefix.includes
  simpa [hEq] using hglobal

/--
An exact-component Kruskal pass preserves the forest invariant: every accepted
edge joins two previously disconnected components.
-/
theorem kruskal_forest_of_exact_component (G : FiniteGraph V E)
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) {A : Finset E} (hforest : G.IsForest A) :
    G.IsForest (kruskal (acceptByComponent G.toGraph C) edges A) := by
  induction edges generalizing A with
  | nil =>
      simpa [kruskal] using hforest
  | cons e es ih =>
      by_cases hacc : acceptByComponent G.toGraph C A e = true
      · have hnot_mem : G.dst e ∉ C.component A (G.src e) :=
          not_mem_component_of_accept hacc
        have hnot_connected :
            ¬ G.toGraph.ConnectedIn A (G.src e) (G.dst e) := by
          intro hconn
          exact hnot_mem ((hexact A (G.src e) (G.dst e)).2 hconn)
        have hforest_insert : G.IsForest (insert e A) :=
          G.isForest_insert_of_not_connected hforest hnot_connected
        simpa [kruskal, hacc] using ih hforest_insert
      · have hfalse : acceptByComponent G.toGraph C A e = false := by
          cases h : acceptByComponent G.toGraph C A e <;> simp [h] at hacc ⊢
        simpa [kruskal, hfalse] using ih hforest

/-- A finite-graph Kruskal run selects only graph edges, provided the initial
set and scanned list contain only graph edges. -/
theorem kruskal_subset_edges (G : FiniteGraph V E)
    {accept : Finset E → E → Bool} (edges : List E) {A : Finset E}
    (hA : A ⊆ G.edges) (hedges : ∀ e, e ∈ edges → e ∈ G.edges) :
    kruskal accept edges A ⊆ G.edges :=
  CLRS.MST.kruskal_subset_of_start_and_edges accept edges hA hedges

/--
If the edge list contains every graph edge and the full graph is connected,
then an exact-component Kruskal pass spans the finite graph.
-/
theorem kruskal_spans_of_complete_exact_component (G : FiniteGraph V E)
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) (A : Finset E)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    G.Spans (kruskal (acceptByComponent G.toGraph C) edges A) := by
  intro u hu v hv
  refine Graph.connected_of_edgewise_connected ?_ (hconnected u hu v hv)
  intro e heG
  exact processed_edge_connected_of_exact_component_kruskal C hexact edges A e
    (hcomplete e heG)

/--
A complete exact-component Kruskal scan starting from a forest returns a
spanning tree of a connected finite graph.
-/
theorem kruskal_spanning_tree_of_complete_exact_component
    (G : FiniteGraph V E) (C : ComponentOracle G.toGraph)
    (hexact : ExactComponentOracle G.toGraph C) (edges : List E)
    {A : Finset E}
    (hA : A ⊆ G.edges) (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges)
    (hforest : G.IsForest A) :
    G.IsSpanningTree (kruskal (acceptByComponent G.toGraph C) edges A) := by
  exact ⟨G.kruskal_subset_edges edges hA hedges,
    G.kruskal_spans_of_complete_exact_component C hexact edges A hcomplete
      hconnected,
    G.kruskal_forest_of_exact_component C hexact edges hforest⟩

/-- End-to-end Kruskal optimality from a sorted complete edge order.  Unlike
the older generic wrapper, this theorem constructs prefix-local lightness and
cycle exchange internally and discharges the final spanning-tree condition. -/
theorem kruskal_optimal_of_sorted_complete_exact_component
    (G : FiniteGraph V E) {w : E → Nat}
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) {A₀ T₀ : Finset E}
    (hsorted : WeightSorted w edges)
    (hall : ∀ S f, G.toGraph.Crosses S f → f ∈ edges)
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hA₀ : A₀ ⊆ G.edges) (hforest : G.IsForest A₀)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    IsMSTExtending G.toProblem w A₀
      (kruskal (acceptByComponent G.toGraph C) edges A₀) := by
  exact G.kruskal_optimal_of_sorted_exact_component C hexact edges hsorted
    hall hedges hstart
    (G.kruskal_spanning_tree_of_complete_exact_component C hexact edges hA₀
      hedges hcomplete hconnected hforest)

/-- Reader-facing minimum-spanning-tree theorem for sorted complete Kruskal
from the empty forest, with no manual lightness or exchange hypotheses. -/
theorem kruskal_minimum_spanning_tree_of_sorted_complete_exact_component_empty
    (G : FiniteGraph V E) {w : E → Nat}
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (edges : List E) {T₀ : Finset E}
    (hsorted : WeightSorted w edges)
    (hall : ∀ S f, G.toGraph.Crosses S f → f ∈ edges)
    (hstart : IsMSTExtending G.toProblem w ∅ T₀)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    G.IsMinimumSpanningTree w
      (kruskal (acceptByComponent G.toGraph C) edges ∅) := by
  exact G.minimumSpanningTree_of_mstExtending_empty
    (G.kruskal_optimal_of_sorted_complete_exact_component C hexact edges
      hsorted hall hstart (by simp) G.isForest_empty hedges hcomplete hconnected)

/-- Finite-graph Kruskal optimality.  The concrete spanning-tree definition
discharges the abstract maximality side condition. -/
theorem kruskal_optimal (G : FiniteGraph V E) {w : E → Nat}
    {accept : Finset E → E → Bool}
    (cert : KruskalCertificate G.toProblem w accept)
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal accept edges A₀)) :
    IsMSTExtending G.toProblem w A₀ (kruskal accept edges A₀) := by
  exact CLRS.MST.kruskal_optimal cert edges hstart hfinal_tree
    (by
      intro T hT hsub
      exact G.spanning_tree_maximal hfinal_tree hT hsub)

theorem kruskal_optimal_of_component_oracle (G : FiniteGraph V E)
    {w : E → Nat} (C : ComponentOracle G.toGraph)
    (hlight :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal (acceptByComponent G.toGraph C) edges A₀)) :
    IsMSTExtending G.toProblem w A₀
      (kruskal (acceptByComponent G.toGraph C) edges A₀) := by
  exact CLRS.MST.kruskal_optimal_of_component_oracle (G := G.toGraph)
    (P := G.toProblem) (w := w) C hlight hexchange edges hstart hfinal_tree
    (by
      intro T hT hsub
      exact G.spanning_tree_maximal hfinal_tree hT hsub)

/--
Finite-graph Kruskal optimality with the final spanning-tree side condition
discharged from exact components, a complete edge scan, graph connectedness,
and an initial forest.
-/
theorem kruskal_optimal_of_complete_exact_component (G : FiniteGraph V E)
    {w : E → Nat} (C : ComponentOracle G.toGraph)
    (hexact : ExactComponentOracle G.toGraph C)
    (hlight :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hA₀ : A₀ ⊆ G.edges) (hforest : G.IsForest A₀)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    IsMSTExtending G.toProblem w A₀
      (kruskal (acceptByComponent G.toGraph C) edges A₀) := by
  exact G.kruskal_optimal_of_component_oracle C hlight hexchange edges hstart
    (G.kruskal_spanning_tree_of_complete_exact_component C hexact edges hA₀
      hedges hcomplete hconnected hforest)

/-- Standard empty-prefix form of the complete exact-component Kruskal theorem. -/
theorem kruskal_optimal_of_complete_exact_component_empty (G : FiniteGraph V E)
    {w : E → Nat} (C : ComponentOracle G.toGraph)
    (hexact : ExactComponentOracle G.toGraph C)
    (hlight :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w ∅ T₀)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    IsMSTExtending G.toProblem w ∅
      (kruskal (acceptByComponent G.toGraph C) edges ∅) := by
  exact G.kruskal_optimal_of_complete_exact_component C hexact hlight hexchange
    edges hstart (by simp) G.isForest_empty hedges hcomplete hconnected

/--
Reader-facing finite-graph MST theorem for a complete exact-component Kruskal
scan from the empty prefix.
-/
theorem kruskal_minimum_spanning_tree_of_complete_exact_component_empty
    (G : FiniteGraph V E) {w : E → Nat} (C : ComponentOracle G.toGraph)
    (hexact : ExactComponentOracle G.toGraph C)
    (hlight :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, acceptByComponent G.toGraph C A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w ∅ T₀)
    (hedges : ∀ e, e ∈ edges → e ∈ G.edges)
    (hcomplete : ∀ e, e ∈ G.edges → e ∈ edges)
    (hconnected : G.Spans G.edges) :
    G.IsMinimumSpanningTree w
      (kruskal (acceptByComponent G.toGraph C) edges ∅) := by
  exact G.minimumSpanningTree_of_mstExtending_empty
    (G.kruskal_optimal_of_complete_exact_component_empty C hexact hlight
      hexchange edges hstart hedges hcomplete hconnected)

theorem kruskal_optimal_of_cycle_test (G : FiniteGraph V E)
    {w : E → Nat} {C : ComponentOracle G.toGraph}
    (impl : CycleTestImplementation G.toGraph C)
    (hlight :
      ∀ A e, impl.accept A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, impl.accept A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {A₀ T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w A₀ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal impl.accept edges A₀)) :
    IsMSTExtending G.toProblem w A₀ (kruskal impl.accept edges A₀) := by
  exact CLRS.MST.kruskal_optimal_of_cycle_test (G := G.toGraph)
    (P := G.toProblem) (w := w) impl hlight hexchange edges hstart hfinal_tree
    (by
      intro T hT hsub
      exact G.spanning_tree_maximal hfinal_tree hT hsub)

/--
Reader-facing finite-graph MST theorem for any Kruskal cycle-test
implementation, once the accepted edge set is known to be a spanning tree.
-/
theorem kruskal_minimum_spanning_tree_of_cycle_test (G : FiniteGraph V E)
    {w : E → Nat} {C : ComponentOracle G.toGraph}
    (impl : CycleTestImplementation G.toGraph C)
    (hlight :
      ∀ A e, impl.accept A e = true →
        ∀ f, G.toGraph.Crosses (C.component A (G.src e)) f → w e ≤ w f)
    (hexchange :
      ∀ A e, impl.accept A e = true →
        ∀ T, IsMSTExtending G.toProblem w A T → e ∉ T →
          ∃ f, f ∈ T ∧ G.toGraph.Crosses (C.component A (G.src e)) f ∧
            G.IsSpanningTree (insert e (T.erase f)) ∧
            A ⊆ insert e (T.erase f))
    (edges : List E) {T₀ : Finset E}
    (hstart : IsMSTExtending G.toProblem w ∅ T₀)
    (hfinal_tree : G.IsSpanningTree (kruskal impl.accept edges ∅)) :
    G.IsMinimumSpanningTree w (kruskal impl.accept edges ∅) := by
  exact G.minimumSpanningTree_of_mstExtending_empty
    (G.kruskal_optimal_of_cycle_test impl hlight hexchange edges hstart
      hfinal_tree)

/-! ## Prim's algorithm -/

/-- A CLRS-valid Prim edge trace.  At every step, the next graph edge crosses
the cut induced by the current root component and is light among all edges
crossing that cut. -/
def PrimTrace (G : FiniteGraph V E) (C : ComponentOracle G.toGraph)
    (w : E → Nat) (root : V) : List E → Finset E → Prop
  | [], _ => True
  | e :: es, A =>
      e ∈ G.edges ∧
      G.toGraph.Crosses (C.component A root) e ∧
      (∀ f, G.toGraph.Crosses (C.component A root) f → w e ≤ w f) ∧
      PrimTrace G C w root es (insert e A)

/-- A complete Prim run packages the dynamic light-edge trace and final
coverage of the finite graph. -/
structure PrimCertificate (G : FiniteGraph V E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : V)
    (start : Finset E) (choices : List E) : Prop where
  root_mem : root ∈ G.vertices
  trace : G.PrimTrace C w root choices start
  spans : G.Spans (prim choices start)

/-- A valid Prim trace selects only graph edges when its initial edge set does. -/
theorem prim_subset_edges_of_trace (G : FiniteGraph V E)
    {C : ComponentOracle G.toGraph} {w : E → Nat} {root : V}
    {choices : List E} {A : Finset E}
    (htrace : G.PrimTrace C w root choices A) (hA : A ⊆ G.edges) :
    prim choices A ⊆ G.edges := by
  induction choices generalizing A with
  | nil => simpa [prim] using hA
  | cons e choices ih =>
      simp only [PrimTrace] at htrace
      have hinsert : insert e A ⊆ G.edges :=
        Finset.insert_subset htrace.1 hA
      simpa [prim] using ih htrace.2.2.2 hinsert

/-- Exact root components make every Prim edge join two previously
disconnected components, so a valid Prim trace preserves the forest invariant. -/
theorem prim_forest_of_trace (G : FiniteGraph V E)
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {w : E → Nat} {root : V} {choices : List E} {A : Finset E}
    (htrace : G.PrimTrace C w root choices A) (hforest : G.IsForest A) :
    G.IsForest (prim choices A) := by
  induction choices generalizing A with
  | nil => simpa [prim] using hforest
  | cons e choices ih =>
      simp only [PrimTrace] at htrace
      have hnot : ¬ G.toGraph.ConnectedIn A (G.src e) (G.dst e) := by
        intro hconn
        exact (not_crosses_component_of_connected hexact hconn) htrace.2.1
      have hinsert : G.IsForest (insert e A) :=
        G.isForest_insert_of_not_connected hforest hnot
      simpa [prim] using ih htrace.2.2.2 hinsert

/-- Safe-edge induction for a CLRS-valid Prim trace.  Each step reuses the
finite-graph automatic cut-property theorem. -/
theorem prim_preserves_mst (G : FiniteGraph V E)
    {C : ComponentOracle G.toGraph} {w : E → Nat} {root : V}
    {choices : List E} {A₀ A T : Finset E}
    (htrace : G.PrimTrace C w root choices A)
    (hA₀A : A₀ ⊆ A)
    (hcur : IsMSTExtending G.toProblem w A T)
    (hbase : IsMSTExtending G.toProblem w A₀ T) :
    ∃ T', IsMSTExtending G.toProblem w (prim choices A) T' ∧
      IsMSTExtending G.toProblem w A₀ T' := by
  induction choices generalizing A T with
  | nil => exact ⟨T, by simpa [prim] using hcur, hbase⟩
  | cons e choices ih =>
      simp only [PrimTrace] at htrace
      have hsafe : SafeEdge G.toProblem w A e :=
        G.safeEdge_of_lightest_crossing_auto htrace.1 htrace.2.1
          (C.respects A root) htrace.2.2.1
      rcases hsafe T hcur with ⟨T₁, hnext, hprefix⟩
      have hbase₁ : IsMSTExtending G.toProblem w A₀ T₁ :=
        optimal_for_smaller_prefix hA₀A hcur hbase hprefix
      have hA₀next : A₀ ⊆ insert e A :=
        hA₀A.trans (Finset.subset_insert e A)
      simpa [prim] using
        ih htrace.2.2.2 hA₀next hnext hbase₁

/-- A complete exact-component Prim certificate produces a spanning tree. -/
theorem prim_spanning_tree_of_certificate (G : FiniteGraph V E)
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {w : E → Nat} {root : V} {choices : List E} {A : Finset E}
    (cert : G.PrimCertificate C w root A choices)
    (hA : A ⊆ G.edges) (hforest : G.IsForest A) :
    G.IsSpanningTree (prim choices A) := by
  exact ⟨G.prim_subset_edges_of_trace cert.trace hA, cert.spans,
    G.prim_forest_of_trace hexact cert.trace hforest⟩

/-- CLRS Prim correctness: every complete dynamic light-edge trace returns an
optimum extending its initial forest. -/
theorem prim_optimal (G : FiniteGraph V E)
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {w : E → Nat} {root : V} {choices : List E} {A T₀ : Finset E}
    (cert : G.PrimCertificate C w root A choices)
    (hstart : IsMSTExtending G.toProblem w A T₀)
    (hA : A ⊆ G.edges) (hforest : G.IsForest A) :
    IsMSTExtending G.toProblem w A (prim choices A) := by
  rcases G.prim_preserves_mst cert.trace (Subset.rfl : A ⊆ A)
      hstart hstart with ⟨T, hprefix, hglobal⟩
  have hfinal : G.IsSpanningTree (prim choices A) :=
    G.prim_spanning_tree_of_certificate hexact cert hA hforest
  have hEq : T = prim choices A :=
    G.spanning_tree_maximal hfinal hprefix.tree hprefix.includes
  simpa [hEq] using hglobal

/-- Reader-facing minimum-spanning-tree theorem for Prim from the empty
forest.  Dynamic cut crossing, lightness, acyclicity, and optimality are all
discharged by the certificate and the shared cut-property stack. -/
theorem prim_minimum_spanning_tree (G : FiniteGraph V E)
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {w : E → Nat} {root : V} {choices : List E} {T₀ : Finset E}
    (cert : G.PrimCertificate C w root ∅ choices)
    (hstart : IsMSTExtending G.toProblem w ∅ T₀) :
    G.IsMinimumSpanningTree w (prim choices ∅) := by
  exact G.minimumSpanningTree_of_mstExtending_empty
    (G.prim_optimal hexact cert hstart (by simp) G.isForest_empty)

end FiniteGraph

end MST
end CLRS
