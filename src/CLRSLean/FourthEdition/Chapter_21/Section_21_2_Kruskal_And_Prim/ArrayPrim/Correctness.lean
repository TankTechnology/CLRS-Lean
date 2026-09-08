import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.ArrayPrim.Execution
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S2_StatefulKruskal

/-!
# Incremental array Prim constructs an MST

The proof follows the stored queue invariant and the real chosen parent edges.
The component oracle is used only in propositions, never by this execution.
Connectedness and the existing all-edge-label closure condition are graph
assumptions. No completed certificate, spanning conclusion, or operation-count
premise is supplied by a caller.
-/
namespace CLRS.MST.ExecutablePrim.ArrayPrim
open Finset
variable {n : Nat} {E : Type} [LinearOrder E]

theorem Invariant.crossing_key {G : FiniteGraph (Fin n) E} {adj : Adjacency G}
    {w : E → Nat} {S : Finset (Fin n)} {q : Cells n E} (h : Invariant adj w S q)
    {e : E} (he : e ∈ G.edges) (hc : G.toGraph.Crosses S e) :
    ∃ v, (read q v).active = true ∧ (read q v).key ≤ (w e : Key) := by
  let v := outsideVertex G.toGraph S e
  have hv := (h.active v).2 (outsideVertex_not_mem hc)
  refine ⟨v,hv,?_⟩
  rcases hc with hc | hc
  · apply h.covers (G.src e) hc.1 v e _ hv
    apply (adj.mem_iff _ _ _).2
    exact ⟨he, Or.inl ⟨rfl, by simp [v, outsideVertex, hc.1]⟩⟩
  · apply h.covers (G.dst e) hc.1 v e _ hv
    apply (adj.mem_iff _ _ _).2
    exact ⟨he, Or.inr ⟨rfl, by simp [v, outsideVertex, hc.2]⟩⟩

theorem Invariant.stop_covers {G : FiniteGraph (Fin n) E} {adj : Adjacency G}
    {w : E → Nat} {S : Finset (Fin n)} {q : Cells n E} (h : Invariant adj w S q)
    (indices : List (Fin n)) (hfull : ∀ v, v ∈ indices)
    (root : Fin n) (hroot : root ∈ G.vertices) (hrS : root ∈ S)
    (hconnected : G.Spans G.edges)
    (hstop : (scan q indices).choice = none ∨ ∃ u c,
      (scan q indices).choice = some (u,c) ∧ c.parent = none) :
    G.vertices ⊆ S := by
  intro v hv
  by_contra hvS
  obtain ⟨e,he,hcross⟩ := Graph.connected_crosses_cut
    (hconnected root hroot v hv) hrS hvS
  obtain ⟨x,hx,hkey⟩ := h.crossing_key he hcross
  rcases hstop with hn | ⟨u,c,hs,hp⟩
  · have hf := (scan_none q indices).1 hn x (hfull x)
    simp [hf] at hx
  · obtain ⟨_,rfl,_,hmin⟩ := scan_some q indices u c hs
    have ht := h.none_key u hp
    have hm := (hmin x (hfull x) hx).trans hkey
    rw [ht] at hm
    simp at hm

omit [LinearOrder E] in
private theorem endpoints_insert {G : Graph (Fin n) E} {S : Finset (Fin n)} {e : E}
    (hc : G.Crosses S e) :
    G.src e ∈ insert (outsideVertex G S e) S ∧
      G.dst e ∈ insert (outsideVertex G S e) S := by
  rcases hc with hc | hc <;> simp [outsideVertex, hc.1, hc.2]

/-- Sufficient fuel constructs both the light-edge trace and terminal coverage. -/
theorem run_correct {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (indices : List (Fin n)) (hfull : ∀ v, v ∈ indices)
    (hexact : ExactComponentOracle G.toGraph C)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (hroot : root ∈ G.vertices) (hconnected : G.Spans G.edges)
    (fuel : Nat) (A : Finset E) (q : Cells n E)
    (hinv : Invariant adj w (C.component A root) q)
    (hA : ∀ f ∈ A, G.src f ∈ C.component A root ∧ G.dst f ∈ C.component A root)
    (hfuel : (G.vertices \ C.component A root).card ≤ fuel) :
    G.PrimTrace C w root (run adj w indices fuel q).edges A ∧
      G.vertices ⊆ C.component (prim (run adj w indices fuel q).edges A) root := by
  induction fuel generalizing A q with
  | zero =>
    refine ⟨trivial, ?_⟩
    have hz : G.vertices \ C.component A root = ∅ :=
      Finset.card_eq_zero.mp (by omega)
    exact Finset.sdiff_eq_empty_iff_subset.mp hz
  | succ fuel ih =>
    cases hs : (scan q indices).choice with
    | none =>
      have hc := hinv.stop_covers indices hfull root hroot (C.mem_self A root)
        hconnected (Or.inl hs)
      simpa [run, hs, prim] using And.intro (show G.PrimTrace C w root [] A from trivial) hc
    | some pair =>
      rcases pair with ⟨u,c⟩
      cases hp : c.parent with
      | none =>
        have hc := hinv.stop_covers indices hfull root hroot (C.mem_self A root)
          hconnected (Or.inr ⟨u,c,hs,hp⟩)
        simpa [run, hs, hp, prim] using And.intro (show G.PrimTrace C w root [] A from trivial) hc
      | some e =>
        obtain ⟨he,hcross,houtside,hlight⟩ := hinv.selected indices hfull hs hp
        have hcomp : C.component (insert e A) root = insert u (C.component A root) := by
          rw [component_insert_crossing hexact hcross hA, houtside]
        have hnext : Invariant adj w (C.component (insert e A) root)
            (advance adj w q u).cells := by
          rw [hcomp]
          exact advance_invariant adj w _ q u hinv
        have hnextA : ∀ f ∈ insert e A,
            G.src f ∈ C.component (insert e A) root ∧ G.dst f ∈ C.component (insert e A) root := by
          intro f hf
          rw [hcomp]
          rcases mem_insert.mp hf with rfl | hf
          · simpa [houtside] using endpoints_insert hcross
          · exact ⟨mem_insert_of_mem (hA f hf).1, mem_insert_of_mem (hA f hf).2⟩
        have hprogress := crossing_uncovered_lt hexact he hcross
        have rest := ih (insert e A) (advance adj w q u).cells hnext hnextA (by omega)
        constructor
        · simp only [run, hs, hp]
          exact ⟨he,hcross,fun f hc => hlight f (hall A f hc) hc,rest.1⟩
        · simpa [run, hs, hp, prim] using rest.2

/-- The exact component of the empty selected-edge set is the singleton root. -/
theorem component_empty {G : FiniteGraph (Fin n) E} (C : ComponentOracle G.toGraph)
    (hexact : ExactComponentOracle G.toGraph C) (root : Fin n) :
    C.component ∅ root = {root} := by
  ext v
  rw [hexact, Graph.connected_empty_iff]
  simp [eq_comm]

theorem execute_correct {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hexact : ExactComponentOracle G.toGraph C)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (hroot : root ∈ G.vertices) (hconnected : G.Spans G.edges) :
    G.PrimTrace C w root (execute adj w root).edges ∅ ∧
      G.vertices ⊆ C.component (prim (execute adj w root).edges ∅) root := by
  have hindex := indexPrefix_spec n (Nat.le_refl n)
  have hinv : Invariant adj w (C.component ∅ root)
      (advance adj w (initialCells n).1 root).cells := by
    rw [component_empty C hexact root]
    simpa using advance_invariant adj w ∅ (initialCells n).1 root (initialCells_invariant adj w)
  apply run_correct adj C w root (indexPrefix n n).1
    (fun v => (hindex.2.2 v).2 v.isLt) hexact hall hroot hconnected n ∅ _ hinv
  · simp
  · exact (Finset.card_le_card (Finset.subset_univ _)).trans (by simp)

/-- The same cached-array execution is a minimum spanning tree. -/
theorem execute_minimum_spanning_tree {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hexact : ExactComponentOracle G.toGraph C)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (hroot : root ∈ G.vertices) (hconnected : G.Spans G.edges) :
    G.IsMinimumSpanningTree w (prim (execute adj w root).edges ∅) := by
  have hc := execute_correct adj C w root hexact hall hroot hconnected
  exact minimum_spanning_tree_of_trace_covers hexact hroot hconnected hc.1 hc.2

end CLRS.MST.ExecutablePrim.ArrayPrim
