import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S4_Completion
import CLRSLean.Audit.Axioms
open CLRS.MST CLRS.MST.ExecutablePrim Finset

private def twoGraph : FiniteGraph (Fin 2) (Fin 1) where
  src := fun _ => 0
  dst := fun _ => 1
  vertices := univ
  edges := univ
  src_mem := by simp
  dst_mem := by simp

private def twoOracle : ComponentOracle twoGraph.toGraph where
  component A root := if (0 : Fin 1) ∈ A then univ else {root}
  mem_self := by intro A root; split <;> simp
  closed_src := by
    intro A root e he _
    have h0 : (0 : Fin 1) ∈ A := by simpa [Subsingleton.elim e (0 : Fin 1)] using he
    simp [h0]
  closed_dst := by
    intro A root e he _
    have h0 : (0 : Fin 1) ∈ A := by simpa [Subsingleton.elim e (0 : Fin 1)] using he
    simp [h0]

private theorem connected_empty {V F : Type} [DecidableEq V] [DecidableEq F]
    (G : CLRS.MST.Graph V F) (x y : V) : G.ConnectedIn ∅ x y ↔ x = y := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail hpath hadj ih => obtain ⟨e, he, _⟩ := hadj; simp at he
  · intro h; subst y; exact Graph.connected_refl _ _ _

private theorem twoExact : ExactComponentOracle twoGraph.toGraph twoOracle := by
  intro A root v
  by_cases h0 : (0 : Fin 1) ∈ A
  · simp only [twoOracle, if_pos h0, mem_univ, true_iff]
    have hc := Graph.connected_of_mem_edge (G := twoGraph.toGraph) h0
    fin_cases root <;> fin_cases v
    all_goals first | exact Graph.connected_refl _ _ _ | exact hc | exact Graph.connected_symm hc
  · have hA : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h0 (by simpa [Subsingleton.elim e (0 : Fin 1)] using he)
    subst A
    simp [twoOracle, connected_empty, eq_comm]

private theorem twoConnected : twoGraph.Spans twoGraph.edges := by
  intro u _ v _
  have hc := Graph.connected_of_mem_edge (G := twoGraph.toGraph)
    (show (0 : Fin 1) ∈ twoGraph.edges by simp [twoGraph])
  fin_cases u <;> fin_cases v
  all_goals first | exact Graph.connected_refl _ _ _ | exact hc | exact Graph.connected_symm hc

private theorem twoHall : ∀ A f, twoGraph.toGraph.Crosses (twoOracle.component A 0) f →
    f ∈ twoGraph.edges := by simp [twoGraph]

example : frontierRun twoGraph twoOracle (fun _ => 7) 0 twoHall 0 ∅ = [] := by native_decide
example : frontierRun twoGraph twoOracle (fun _ => 7) 0 twoHall 1 ∅ = [0] := by native_decide
example : frontierRun twoGraph twoOracle (fun _ => 7) 0 twoHall 10 ∅ = [0] := by native_decide
example : (twoGraph.vertices \ twoOracle.component ∅ 0).card = 1 := by native_decide
example : ¬ twoGraph.Spans (prim (frontierRun twoGraph twoOracle (fun _ => 7) 0 twoHall 0 ∅) ∅) := by
  intro h
  have hc := h 0 (by simp [twoGraph]) 1 (by simp [twoGraph])
  have heq := (connected_empty twoGraph.toGraph 0 1).1 hc
  exact (by decide : (0 : Fin 2) ≠ 1) heq
example : twoGraph.PrimCertificate twoOracle (fun _ => 7) 0 ∅
    (frontierRun twoGraph twoOracle (fun _ => 7) 0 twoHall 1 ∅) :=
  frontierRun_certificate _ _ _ _ twoHall twoExact (by simp [twoGraph])
    twoConnected _ _ (by native_decide)
example : twoGraph.IsMinimumSpanningTree (fun _ => 7)
    (prim (frontierRun twoGraph twoOracle (fun _ => 7) 0 twoHall 1 ∅) ∅) :=
  frontierRun_minimum_spanning_tree _ _ _ _ twoHall twoExact (by simp [twoGraph])
    twoConnected _ (by native_decide)

#assert_axioms crossing_uncovered_lt
#assert_axioms component_insert_crossing
#assert_axioms frontierQueue_none_covers
#assert_axioms run_certificate
#assert_axioms exists_mstExtending_empty
#assert_axioms frontierRun_minimum_spanning_tree
#assert_axioms frontierRun_minimum_spanning_tree_of_card
#assert_axioms minimum_spanning_tree_of_trace_covers

private def oneGraph : FiniteGraph (Fin 1) (Fin 0) where
  src := Fin.elim0
  dst := Fin.elim0
  vertices := univ
  edges := ∅
  src_mem := by simp
  dst_mem := by simp

private def oneOracle : ComponentOracle oneGraph.toGraph where
  component _ root := {root}
  mem_self := by simp
  closed_src := by intro _ _ e; exact Fin.elim0 e
  closed_dst := by intro _ _ e; exact Fin.elim0 e

private theorem oneExact : ExactComponentOracle oneGraph.toGraph oneOracle := by
  intro A root v
  have hv : v = root := Subsingleton.elim _ _
  subst v
  simp only [oneOracle, mem_singleton, true_iff]
  exact Graph.connected_refl _ _ _

private theorem oneConnected : oneGraph.Spans oneGraph.edges := by
  intro u _ v _
  have hv : v = u := Subsingleton.elim _ _
  subst v
  exact Graph.connected_refl _ _ _

private theorem oneHall : ∀ A f, oneGraph.toGraph.Crosses (oneOracle.component A 0) f →
    f ∈ oneGraph.edges := by intro _ e; exact Fin.elim0 e

example : (oneGraph.vertices \ oneOracle.component ∅ 0).card = 0 := by native_decide
example : frontierRun oneGraph oneOracle Fin.elim0 0 oneHall 0 ∅ = [] := by native_decide
example : oneGraph.IsMinimumSpanningTree Fin.elim0
    (prim (frontierRun oneGraph oneOracle Fin.elim0 0 oneHall 0 ∅) ∅) :=
  frontierRun_minimum_spanning_tree _ _ _ _ oneHall oneExact (by simp [oneGraph])
    oneConnected _ (by native_decide)
example : frontierRun twoGraph twoOracle (fun _ => 0) 0 twoHall 1 ∅ = [0] := by native_decide
