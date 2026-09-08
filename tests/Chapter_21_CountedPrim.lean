import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S5_CountedFrontier
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S6_ArrayPrim
open CLRS.MST CLRS.MST.ExecutablePrim Finset

#check CountedFrontier.execute_refines
#check CountedFrontier.execute_edgeVisits
#check ArrayPrim.execute_cost_bound
#check ArrayPrim.execute_cost_bound_vertices
#check ArrayPrim.execute_minimum_spanning_tree
#assert_axioms CountedFrontier.execute_refines
#assert_axioms CountedFrontier.execute_edgeVisits
#assert_axioms ArrayPrim.Adjacency.total_length
#assert_axioms ArrayPrim.advance_invariant
#assert_axioms ArrayPrim.execute_cost_bound
#assert_axioms ArrayPrim.execute_edgeVisits_le
#assert_axioms ArrayPrim.execute_extracts_le
#assert_axioms ArrayPrim.execute_correct
#assert_axioms ArrayPrim.execute_minimum_spanning_tree

private def triangle : FiniteGraph (Fin 3) (Fin 3) where
  src := ![0,0,2]
  dst := ![1,2,1]
  vertices := univ
  edges := univ
  src_mem := by simp
  dst_mem := by simp

private def triangleAdj : ArrayPrim.Adjacency triangle where
  rows := #v[[(1,0),(2,1)],[(0,0),(2,2)],[(0,1),(1,2)]]
  represents := by intro u; fin_cases u <;> native_decide

private def triangleRun := ArrayPrim.execute triangleAdj ![10,1,2] 0
example : triangleRun.edges = [1,2] := by decide
example : triangleRun.edgeVisits = 6 ∧ triangleRun.extracts = 3 := by decide
example : triangleRun.queueReads = 18 ∧ triangleRun.queueWrites = 6 ∧
    triangleRun.comparisons = 4 ∧ triangleRun.adjacencyReads = 3 ∧
    triangleRun.preparationWrites = 6 := by decide
example : ArrayPrim.cellWork triangleRun = 37 := by decide
example : ArrayPrim.cellWork triangleRun ≤ 2 * 3 * 3 + 5 * 3 + 6 * 3 :=
  ArrayPrim.execute_cost_bound triangleAdj ![10,1,2] 0
example : (ArrayPrim.execute triangleAdj (fun _ => 0) 0).edges.length = 2 := by decide

-- Parallel edges and a self-loop: the best parallel edge survives; loop incidences are scanned.
private def parallel : FiniteGraph (Fin 2) (Fin 3) where
  src := fun _ => 0
  dst := ![1,1,0]
  vertices := univ
  edges := univ
  src_mem := by simp
  dst_mem := by simp
private def parallelAdj : ArrayPrim.Adjacency parallel where
  rows := #v[[(1,0),(1,1),(0,2),(0,2)],[(0,0),(0,1)]]
  represents := by intro u; fin_cases u <;> native_decide
example : (ArrayPrim.execute parallelAdj ![9,2,0] 0).edges = [1] := by decide
example : (ArrayPrim.execute parallelAdj ![9,2,0] 0).edgeVisits = 6 := by decide

private def one : FiniteGraph (Fin 1) (Fin 0) where
  src := Fin.elim0
  dst := Fin.elim0
  vertices := univ
  edges := ∅
  src_mem := by simp
  dst_mem := by simp
private def oneAdj : ArrayPrim.Adjacency one where
  rows := #v[[]]
  represents := by intro u; fin_cases u; simp [one]
example : (ArrayPrim.execute oneAdj Fin.elim0 0).edges = [] := by decide
example : (ArrayPrim.execute oneAdj Fin.elim0 0).edgeVisits = 0 ∧
    ArrayPrim.cellWork (ArrayPrim.execute oneAdj Fin.elim0 0) = 6 := by decide
example : (ArrayPrim.initialCells (E := Fin 0) 0).2 = 0 := by decide

private def two : FiniteGraph (Fin 2) (Fin 1) where
  src := fun _ => 0
  dst := fun _ => 1
  vertices := univ
  edges := univ
  src_mem := by simp
  dst_mem := by simp
private def twoAdj : ArrayPrim.Adjacency two where
  rows := #v[[(1,0)],[(0,0)]]
  represents := by intro u; fin_cases u <;> native_decide
private def twoOracle : ComponentOracle two.toGraph where
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
private theorem twoExact : ExactComponentOracle two.toGraph twoOracle := by
  intro A root v
  by_cases h0 : (0 : Fin 1) ∈ A
  · simp only [twoOracle, if_pos h0, mem_univ, true_iff]
    have hc := Graph.connected_of_mem_edge (G := two.toGraph) h0
    fin_cases root <;> fin_cases v
    all_goals first | exact Graph.connected_refl _ _ _ | exact hc | exact Graph.connected_symm hc
  · have hA : A = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h0 (by simpa [Subsingleton.elim e (0 : Fin 1)] using he)
    subst A
    simp [twoOracle, Graph.connected_empty_iff, eq_comm]
private theorem twoConnected : two.Spans two.edges := by
  intro u _ v _
  have hc := Graph.connected_of_mem_edge (G := two.toGraph)
    (show (0 : Fin 1) ∈ two.edges by simp [two])
  fin_cases u <;> fin_cases v
  all_goals first | exact Graph.connected_refl _ _ _ | exact hc | exact Graph.connected_symm hc
private theorem twoHall : ∀ A f, two.toGraph.Crosses (twoOracle.component A 0) f →
    f ∈ two.edges := by simp [two]
example : two.IsMinimumSpanningTree (fun _ => 7)
    (prim (ArrayPrim.execute twoAdj (fun _ => 7) 0).edges ∅) :=
  ArrayPrim.execute_minimum_spanning_tree twoAdj twoOracle _ _ twoExact twoHall
    (by simp [two]) twoConnected
example : (CountedFrontier.execute two twoOracle (fun _ => 7) 0 0 ∅).edges = [] := by decide
example : (CountedFrontier.execute two twoOracle (fun _ => 7) 0 10 ∅).edges = [0] := by native_decide
example : ((CountedFrontier.execute two twoOracle (fun _ => 7) 0 10 ∅).rounds.map
    CountedFrontier.Round.edgeVisits).sum = 2 := by native_decide
