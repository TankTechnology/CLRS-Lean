import CLRSLean.FourthEdition.Chapter_35.Section_35_2_The_Traveling_Salesperson_Problem.GraphExecution
import CLRSLean.Audit.Axioms
import CLRSLean.FourthEdition.Chapter_35.Section_35_3_The_Set_Covering_Problem.ReturnedFamily
#assert_axioms CLRS.SetCover.greedySetCover_card_eq_cost
#assert_axioms CLRS.SetCover.greedySetCover_card_approx
#assert_axioms CLRS.SetCover.greedySetCover_card_ln_approx

open CLRS.SetCover Finset

example : greedySetCover (∅ : Finset (Finset Nat)) ∅ (by simp) = ∅ := by
  rw [greedySetCover.eq_1]
  simp

-- A single covering set is returned exactly once, even when it covers many elements.
example : (greedySetCover ({(univ : Finset (Fin 7))}) univ
    (by intro x _; exact ⟨univ,by simp,mem_univ x⟩)).card = 1 := by
  let hcov : ∀ x ∈ (univ : Finset (Fin 7)), ∃ S ∈ ({univ} : Finset (Finset (Fin 7))), x ∈ S :=
    by intro x _; exact ⟨univ,by simp,mem_univ x⟩
  have hsub := greedySetCover_subset ({univ} : Finset (Finset (Fin 7))) hcov
  have hcard := card_le_card hsub
  obtain ⟨S,hS,_⟩ := greedySetCover_covers ({univ} : Finset (Finset (Fin 7))) hcov 0 (mem_univ _)
  have hpos := card_pos.mpr ⟨S,hS⟩
  simp only [card_singleton] at hcard
  omega

open CLRS.TSP CLRS.TSP.GraphAdapter
#assert_axioms components_exact
#assert_axioms parent_tree
#assert_axioms parentEdge_injective
#assert_axioms parent_cost_le
#assert_axioms selected_mst
#assert_axioms mstParent_minimum
#assert_axioms graphTour_nodup
#assert_axioms graphTour_mem
#assert_axioms graphTour_length
#assert_axioms graphTour_two_approx

-- Singleton graphs have a one-vertex tour, including zero total cost.
example : (graphTour (fun _ _ : Fin 1 => 0) 0).length = 1 := graphTour_length _ _
example : (graphTour (fun _ _ : Fin 1 => 0) 0).Nodup := graphTour_nodup _ _
-- Ties do not affect coverage, uniqueness, or the constructed MST certificate.
example : (graphTour (fun _ _ : Fin 4 => 0) 0).length = 4 := graphTour_length _ _
example (v : Fin 4) : v ∈ graphTour (fun _ _ : Fin 4 => 0) 0 := graphTour_mem _ _ _
example : IsMinimumSpanningTreeOn (fun _ _ : Fin 4 => 0)
    (mstParent (fun _ _ : Fin 4 => 0) 0) 0 := mstParent_minimum _ _ (by intros; rfl)
-- The public ratio is graph-input only; no parent tree or edge MST is supplied.
example (n : Nat) (w : Graph (Fin n)) (r : Fin n)
    (hs : ∀ u v, w u v = w v u)
    (ht : ∀ a b c, w a c ≤ w a b+w b c)
    (hl : ∀ v, w v v=0) (σ : Fin n → Fin n) (hσ : Tour σ) :
    tourCostTo w r (graphTour w r) ≤ 2*TourCost w σ :=
  graphTour_two_approx w r hs ht hl hσ

private def twoTour : Fin 2 → Fin 2 := ![1,0]
private theorem twoTour_valid : Tour twoTour where
  bijective := by decide
  reachable u v := by
    fin_cases u <;> fin_cases v
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨0,rfl⟩
private def twoMetric (u v : Fin 2) : Nat := if u=v then 0 else 1

-- A positive metric and an inhabited comparator tour exercise the full composition.
example : tourCostTo twoMetric 0 (graphTour twoMetric 0) ≤ 4 := by
  have h := graphTour_two_approx twoMetric 0 (by decide) (by decide) (by decide) twoTour_valid
  simpa [TourCost,Fin.sum_univ_two,twoMetric,twoTour] using h
