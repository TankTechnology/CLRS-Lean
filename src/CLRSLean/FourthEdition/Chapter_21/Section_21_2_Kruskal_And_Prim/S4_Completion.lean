import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S3_ExecutablePrim

/-!
# Terminal coverage and MST correctness for executable Prim

Each certified crossing edge strictly decreases the number of vertices outside
the exact root component. The concrete frontier queue cannot stop while a
crossing graph edge remains: its finite key would contradict a minimum parentless
vertex having an infinite key. Sufficient fuel therefore constructs a full Prim
certificate, including spanning.

The final MST theorem constructs its initial optimum witness from a complete
Kruskal forest scan and natural-weight minimization. It retains the existing
all-edge-label closure hypothesis of the source Prim trace. Queue and component
oracle running costs are separate from these completion theorems.
-/

namespace CLRS.MST.ExecutablePrim
open Finset
variable {n : Nat} {E : Type} [LinearOrder E]

theorem component_mono {G : FiniteGraph (Fin n) E} {C : ComponentOracle G.toGraph}
    (hexact : ExactComponentOracle G.toGraph C) {A B : Finset E} (h : A ⊆ B)
    (root : Fin n) : C.component A root ⊆ C.component B root := by
  intro v hv
  exact (hexact B root v).2 (Graph.connected_mono h ((hexact A root v).1 hv))

theorem crossing_outside_mem_insert {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {A : Finset E} {root : Fin n} {e : E}
    (hc : G.toGraph.Crosses (C.component A root) e) :
    outsideVertex G.toGraph (C.component A root) e ∈ C.component (insert e A) root := by
  have hm := component_mono hexact (Finset.subset_insert e A) root
  unfold outsideVertex
  split
  · rename_i hs
    exact C.closed_src (insert e A) root e (mem_insert_self _ _) (hm hs)
  · rename_i hs
    rcases hc with hc | hc
    · exact (hs hc.1).elim
    · exact C.closed_dst (insert e A) root e (mem_insert_self _ _) (hm hc.1)

/-- A selected crossing edge strictly reduces the actual number of uncovered vertices. -/
theorem crossing_uncovered_lt {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {A : Finset E} {root : Fin n} {e : E} (he : e ∈ G.edges)
    (hc : G.toGraph.Crosses (C.component A root) e) :
    (G.vertices \ C.component (insert e A) root).card <
      (G.vertices \ C.component A root).card := by
  have hm := component_mono hexact (Finset.subset_insert e A) root
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨(by intro v hv; exact mem_sdiff.mpr ⟨(mem_sdiff.mp hv).1, fun h => (mem_sdiff.mp hv).2 (hm h)⟩), ?_⟩
  intro heq
  have hv : outsideVertex G.toGraph (C.component A root) e ∈
      G.vertices \ C.component A root :=
    mem_sdiff.mpr ⟨outsideVertex_mem_vertices he, outsideVertex_not_mem hc⟩
  rw [← heq] at hv
  exact (mem_sdiff.mp hv).2 (crossing_outside_mem_insert hexact hc)

/-- Generic completion for any light-edge provider that stops only after coverage. -/
theorem run_covers {G : FiniteGraph (Fin n) E} {C : ComponentOracle G.toGraph}
    {w : E → Nat} {root : Fin n} (provider : QueueProvider G C w root)
    (hexact : ExactComponentOracle G.toGraph C)
    (hstop : ∀ A, provider.choose A = none → G.vertices ⊆ C.component A root)
    (fuel : Nat) (A : Finset E)
    (hfuel : (G.vertices \ C.component A root).card ≤ fuel) :
    G.vertices ⊆ C.component (prim (run provider fuel A) A) root := by
  induction fuel generalizing A with
  | zero =>
      have hz : G.vertices \ C.component A root = ∅ := by
        apply Finset.card_eq_zero.mp
        omega
      simpa [run, prim] using Finset.sdiff_eq_empty_iff_subset.mp hz
  | succ fuel ih =>
      cases hc : provider.choose A with
      | none => simpa [run, hc, prim] using hstop A hc
      | some pair =>
          rcases pair with ⟨u, e⟩
          have cert := provider.correct A u e hc
          have hg := crossing_uncovered_lt hexact cert.edge_mem cert.crosses
          simpa [run, hc, prim] using ih (insert e A) (by omega)

theorem run_spans {G : FiniteGraph (Fin n) E} {C : ComponentOracle G.toGraph}
    {w : E → Nat} {root : Fin n} (provider : QueueProvider G C w root)
    (hexact : ExactComponentOracle G.toGraph C)
    (hstop : ∀ A, provider.choose A = none → G.vertices ⊆ C.component A root)
    (fuel : Nat) (A : Finset E)
    (hfuel : (G.vertices \ C.component A root).card ≤ fuel) :
    G.Spans (prim (run provider fuel A) A) := by
  have hcover := run_covers provider hexact hstop fuel A hfuel
  intro u hu v hv
  exact Graph.connected_trans (Graph.connected_symm ((hexact _ root u).1 (hcover hu)))
    ((hexact _ root v).1 (hcover hv))

omit [LinearOrder E] in
theorem Queue.decreaseKey_none_key {q : Queue n E}
    (hq : ∀ x, q.parent x = none → q.key x = ⊤) (v : Fin n) (k : Nat) (e : E) :
    ∀ x, (q.decreaseKey v k e).parent x = none → (q.decreaseKey v k e).key x = ⊤ := by
  intro x hp
  by_cases hk : (k : Key) < q.key v
  · simp only [Queue.decreaseKey, if_pos hk] at hp ⊢
    by_cases hx : x = v
    · subst x; simp at hp
    · simpa [Function.update, hx] using hq x (by simpa [Function.update, hx] using hp)
  · simpa only [Queue.decreaseKey, if_neg hk] using hq x (by simpa [Queue.decreaseKey, hk] using hp)

theorem buildQueue_none_key (G : FiniteGraph (Fin n) E) (w : E → Nat)
    (S : Finset (Fin n)) (edges : List E) :
    ∀ x, (buildQueue G w S edges).parent x = none → (buildQueue G w S edges).key x = ⊤ := by
  induction edges with
  | nil => simp [buildQueue, Queue.initial]
  | cons e es ih =>
      simp only [buildQueue, relaxEdge]
      split
      · exact Queue.decreaseKey_none_key ih _ _ _
      · exact ih

omit [LinearOrder E] in
theorem Queue.exists_extractMin_of_mem {q : Queue n E} {v : Fin n} (hv : v ∈ q.members) :
    ∃ u q', q.extractMin = some (u, q') := by
  cases he : q.extractMin with
  | some p => exact ⟨p.1, p.2, rfl⟩
  | none =>
      unfold Queue.extractMin at he
      split at he
      · rename_i hm
        have hz := (extractMinList_eq_none_iff q.key (q.members.sort (· ≤ ·))).1 hm
        have hvl := (q.members.mem_sort (· ≤ ·)).2 hv
        simp [hz] at hvl
      · contradiction

theorem frontierQueue_choose_exists {G : FiniteGraph (Fin n) E} {w : E → Nat}
    {S : Finset (Fin n)} {e : E} (he : e ∈ G.edges) (hc : G.toGraph.Crosses S e) :
    ∃ u f, (frontierQueue G w S).choose = some (u, f) := by
  let q := frontierQueue G w S
  have inv := frontierQueue_invariant G w S
  let v := outsideVertex G.toGraph S e
  have hv : v ∈ q.members := by
    rw [inv.members_eq]
    exact mem_sdiff.mpr ⟨outsideVertex_mem_vertices he, outsideVertex_not_mem hc⟩
  obtain ⟨u, q', hu⟩ := Queue.exists_extractMin_of_mem hv
  have hkey := (Queue.extractMin_key_le hu hv).trans
    (inv.covers e ((G.edges.mem_sort (· ≤ ·)).2 he) hc)
  cases hp : q.parent u with
  | none =>
      have ht : q.key u = ⊤ := buildQueue_none_key G w S _ u hp
      rw [ht] at hkey
      simp at hkey
  | some f => exact ⟨u, f, by change q.choose = _; simp [Queue.choose, hu, hp]⟩

theorem frontierQueue_none_covers {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} {w : E → Nat} {root : Fin n}
    (hroot : root ∈ G.vertices) (hconnected : G.Spans G.edges) (A : Finset E)
    (hnone : (frontierQueue G w (C.component A root)).choose = none) :
    G.vertices ⊆ C.component A root := by
  intro v hv
  by_contra hvout
  obtain ⟨e, he, hc⟩ := Graph.connected_crosses_cut
    (hconnected root hroot v hv) (C.mem_self A root) hvout
  obtain ⟨u, f, hchoose⟩ := frontierQueue_choose_exists (w := w) he hc
  rw [hnone] at hchoose
  contradiction


/-- A sufficient-fuel run constructs the full certificate, including spanning. -/
theorem run_certificate {G : FiniteGraph (Fin n) E} {C : ComponentOracle G.toGraph}
    {w : E → Nat} {root : Fin n} (provider : QueueProvider G C w root)
    (hexact : ExactComponentOracle G.toGraph C) (hroot : root ∈ G.vertices)
    (hstop : ∀ A, provider.choose A = none → G.vertices ⊆ C.component A root)
    (fuel : Nat) (A : Finset E)
    (hfuel : (G.vertices \ C.component A root).card ≤ fuel) :
    G.PrimCertificate C w root A (run provider fuel A) :=
  ⟨hroot, run_refines_PrimTrace provider fuel A, run_spans provider hexact hstop fuel A hfuel⟩

theorem frontierRun_certificate (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (hexact : ExactComponentOracle G.toGraph C) (hroot : root ∈ G.vertices)
    (hconnected : G.Spans G.edges) (fuel : Nat) (A : Finset E)
    (hfuel : (G.vertices \ C.component A root).card ≤ fuel) :
    G.PrimCertificate C w root A (frontierRun G C w root hall fuel A) := by
  apply run_certificate (frontierProvider G C w root hall) hexact hroot
  · intro B hb
    exact frontierQueue_none_covers hroot hconnected B hb
  · exact hfuel

/-- A finite connected graph has a minimum spanning tree. The witness is
constructed from the existing complete Kruskal forest scan and natural-weight
minimization; callers need not supply an already-minimum tree. -/
theorem exists_mstExtending_empty (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (hexact : ExactComponentOracle G.toGraph C)
    (w : E → Nat) (hconnected : G.Spans G.edges) :
    ∃ T, IsMSTExtending G.toProblem w ∅ T := by
  classical
  have htree : ∃ T, G.IsSpanningTree T := by
    refine ⟨kruskal (acceptByComponent G.toGraph C) (G.edges.sort (· ≤ ·)) ∅, ?_⟩
    exact G.kruskal_spanning_tree_of_complete_exact_component C hexact _
      (by simp) (by intro e he; exact (G.edges.mem_sort (· ≤ ·)).1 he)
      (by intro e he; exact (G.edges.mem_sort (· ≤ ·)).2 he)
      hconnected G.isForest_empty
  have hex : ∃ k : Nat, ∃ T, G.IsSpanningTree T ∧ weight w T = k := by
    obtain ⟨T, ht⟩ := htree
    exact ⟨weight w T, T, ht, rfl⟩
  obtain ⟨T, ht, hw⟩ := Nat.find_spec hex
  refine ⟨T, ht, by simp, ?_⟩
  intro U hu _
  rw [hw]
  exact Nat.find_min' hex ⟨U, hu, rfl⟩

/-- End-to-end executable Prim MST theorem: sufficient fuel and graph/oracle
assumptions construct both terminal spanning and the initial optimum witness. -/
theorem frontierRun_minimum_spanning_tree (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (hexact : ExactComponentOracle G.toGraph C) (hroot : root ∈ G.vertices)
    (hconnected : G.Spans G.edges) (fuel : Nat)
    (hfuel : (G.vertices \ C.component ∅ root).card ≤ fuel) :
    G.IsMinimumSpanningTree w (prim (frontierRun G C w root hall fuel ∅) ∅) := by
  obtain ⟨T, ht⟩ := exists_mstExtending_empty G C hexact w hconnected
  exact G.prim_minimum_spanning_tree hexact
    (frontierRun_certificate G C w root hall hexact hroot hconnected fuel ∅ hfuel) ht

/-- The graph vertex count is always sufficient fuel. -/
theorem frontierRun_minimum_spanning_tree_of_card (G : FiniteGraph (Fin n) E)
    (C : ComponentOracle G.toGraph) (w : E → Nat) (root : Fin n)
    (hall : ∀ A f, G.toGraph.Crosses (C.component A root) f → f ∈ G.edges)
    (hexact : ExactComponentOracle G.toGraph C) (hroot : root ∈ G.vertices)
    (hconnected : G.Spans G.edges) :
    G.IsMinimumSpanningTree w
      (prim (frontierRun G C w root hall G.vertices.card ∅) ∅) := by
  exact frontierRun_minimum_spanning_tree G C w root hall hexact hroot hconnected _
    (Finset.card_le_card (Finset.sdiff_subset))


/-- Component coverage is a terminal spanning criterion for any Prim implementation. -/
theorem spans_of_component_covers {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {A : Finset E} {root : Fin n} (hcover : G.vertices ⊆ C.component A root) :
    G.Spans A := by
  intro u hu v hv
  exact Graph.connected_trans (Graph.connected_symm ((hexact A root u).1 (hcover hu)))
    ((hexact A root v).1 (hcover hv))

/-- An implementation's light-edge trace and terminal root-component coverage
suffice for MST correctness; an initial optimum is constructed internally. -/
theorem minimum_spanning_tree_of_trace_covers {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {w : E → Nat} {root : Fin n} (hroot : root ∈ G.vertices)
    (hconnected : G.Spans G.edges) {choices : List E}
    (htrace : G.PrimTrace C w root choices ∅)
    (hcover : G.vertices ⊆ C.component (prim choices ∅) root) :
    G.IsMinimumSpanningTree w (prim choices ∅) := by
  obtain ⟨T, ht⟩ := exists_mstExtending_empty G C hexact w hconnected
  exact G.prim_minimum_spanning_tree hexact
    ⟨hroot, htrace, spans_of_component_covers hexact hcover⟩ ht


/-- When all selected edges lie inside the root component, a crossing insertion
adds exactly its outside endpoint. This supports cached adjacency-once Prim. -/
theorem component_insert_crossing {G : FiniteGraph (Fin n) E}
    {C : ComponentOracle G.toGraph} (hexact : ExactComponentOracle G.toGraph C)
    {A : Finset E} {root : Fin n} {e : E}
    (hc : G.toGraph.Crosses (C.component A root) e)
    (hA : ∀ f ∈ A, G.src f ∈ C.component A root ∧ G.dst f ∈ C.component A root) :
    C.component (insert e A) root =
      insert (outsideVertex G.toGraph (C.component A root) e) (C.component A root) := by
  let S := C.component A root
  let T := insert (outsideVertex G.toGraph S e) S
  have hend : G.src e ∈ T ∧ G.dst e ∈ T := by
    by_cases hs : G.src e ∈ S
    · simp [T, outsideVertex, hs]
    · rcases hc with hc | hc
      · exact (hs hc.1).elim
      · simp [T, outsideVertex, hs, show G.dst e ∈ S from hc.1]
  apply Finset.Subset.antisymm
  · intro v hv
    change v ∈ T
    by_contra hvout
    obtain ⟨f, hf, hcross⟩ := Graph.connected_crosses_cut
      ((hexact (insert e A) root v).1 hv)
      (show root ∈ T from mem_insert_of_mem (C.mem_self A root)) hvout
    have hfend : G.src f ∈ T ∧ G.dst f ∈ T := by
      rcases mem_insert.mp hf with rfl | hf
      · exact hend
      · exact ⟨mem_insert_of_mem (hA f hf).1, mem_insert_of_mem (hA f hf).2⟩
    rcases hcross with hc | hc
    · exact hc.2 hfend.2
    · exact hc.2 hfend.1
  · apply Finset.insert_subset
    · exact crossing_outside_mem_insert hexact hc
    · exact component_mono hexact (Finset.subset_insert e A) root

end CLRS.MST.ExecutablePrim
