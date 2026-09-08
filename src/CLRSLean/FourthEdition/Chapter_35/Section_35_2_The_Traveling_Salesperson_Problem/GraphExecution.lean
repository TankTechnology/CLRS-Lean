import CLRSLean.FourthEdition.Chapter_35.Section_35_2_The_Traveling_Salesperson_Problem.Rooting

/-!
# Metric TSP starting from a weighted complete graph

Chapter 21's verified Prim execution constructs an edge MST. Shortest-path
rooting converts its selected edges into a parent tree without increasing
weight. Conversely, each competing parent tree gives a connected edge set;
Kruskal extracts a spanning tree of no greater weight. This discharges the
minimum-parent-tree premise of the existing DFS approximation theorem.

Only the weights, root, symmetry, triangle inequality and zero-loop conditions
are inputs. Neither a final MST certificate nor a representation adapter is
supplied by the caller. Rooting and exact component queries are classical;
there is no polynomial runtime claim for this composition.
-/
noncomputable section
namespace CLRS.TSP.GraphAdapter
open Finset Classical MST MST.ExecutablePrim
variable {n : Nat}

local instance : LinearOrder (Fin n × Fin n) :=
  LinearOrder.lift' (Fintype.equivFin (Fin n × Fin n)) (Fintype.equivFin _).injective

local instance : DecidableEq (Fin n × Fin n) :=
  (inferInstance : LinearOrder (Fin n × Fin n)).toDecidableEq

/-- The complete graph represents an undirected connection by ordered endpoint labels. -/
def complete : FiniteGraph (Fin n) (Fin n × Fin n) where
  src := Prod.fst
  dst := Prod.snd
  vertices := univ
  edges := univ
  src_mem _ _ := mem_univ _
  dst_mem _ _ := mem_univ _

theorem complete_connected : (complete (n:=n)).Spans complete.edges := by
  intro u _ v _
  exact Graph.connected_of_mem_edge (e := (u,v)) (mem_univ _)

def selected (w : TSP.Graph (Fin n)) (r : Fin n) : Finset (Fin n × Fin n) :=
  prim (frontierRun (complete (n:=n)) (components (complete (n:=n)).toGraph) (fun e : Fin n × Fin n => w e.1 e.2) r
    (by intro A e h; exact (show e ∈ (complete (n:=n)).edges from mem_univ e)) n ∅) ∅

theorem selected_mst (w : TSP.Graph (Fin n)) (r : Fin n) :
    complete.IsMinimumSpanningTree (fun e : Fin n × Fin n => w e.1 e.2) (selected w r) := by
  simpa [selected,complete] using frontierRun_minimum_spanning_tree_of_card
    (complete (n:=n)) (components (complete (n:=n)).toGraph) (fun e : Fin n × Fin n => w e.1 e.2) r
    (by intro A e h; exact (show e ∈ (complete (n:=n)).edges from mem_univ e)) (components_exact _) (mem_univ r) complete_connected

theorem selectedConnected (w : TSP.Graph (Fin n)) (r : Fin n) :
    ConnectedSelection complete.toGraph (selected w r) r where
  reaches v := (selected_mst w r).1.2.1 r (mem_univ _) v (mem_univ _)

/-- The parent map is computed from the MST selected by the actual Prim recursion. -/
def mstParent (w : TSP.Graph (Fin n)) (r : Fin n) : Fin n → Fin n :=
  parent (selectedConnected w r)

theorem mstParent_tree (w : TSP.Graph (Fin n)) (r : Fin n) : TreeOn (mstParent w r) r :=
  parent_tree (selectedConnected w r)

def parentEdges (p : Fin n → Fin n) (r : Fin n) : Finset (Fin n × Fin n) :=
  (univ.erase r).image (fun v => (v,p v))

theorem parentEdges_weight (w : TSP.Graph (Fin n)) (p : Fin n → Fin n) (r : Fin n) :
    MST.weight (fun e : Fin n × Fin n => w e.1 e.2) (parentEdges p r) = treeCost w p r := by
  unfold MST.weight parentEdges treeCost
  rw [sum_image]
  intro u hu v hv he
  exact congrArg Prod.fst he

theorem parentEdges_spans {p : Fin n → Fin n} {r : Fin n} (h : TreeOn p r) :
    complete.Spans (parentEdges p r) := by
  have hedge (v : Fin n) : complete.toGraph.ConnectedIn (parentEdges p r) v (p v) := by
    by_cases hv : v=r
    · subst v
      rw [h.root_fixed]
      exact Graph.connected_refl _ _ _
    · exact Graph.connected_of_mem_edge (e:=(v,p v))
        (mem_image.mpr ⟨v,mem_erase.mpr ⟨hv,mem_univ _⟩,rfl⟩)
  have hiter (k : Nat) (v : Fin n) :
      complete.toGraph.ConnectedIn (parentEdges p r) v (p^[k] v) := by
    induction k generalizing v with
    | zero => exact Graph.connected_refl _ _ _
    | succ k ih =>
      rw [Function.iterate_succ_apply]
      exact Graph.connected_trans (hedge v) (ih (p v))
  have hroot (v : Fin n) : complete.toGraph.ConnectedIn (parentEdges p r) v r := by
    obtain ⟨k,hk⟩ := h.reaches_root v
    simpa [hk] using hiter k v
  intro u _ v _
  exact Graph.connected_trans (hroot u) (Graph.connected_symm (hroot v))

/-- The edge MST compares with any connected edge set, including one with cycles. -/
theorem selected_le_connected (w : TSP.Graph (Fin n)) (r : Fin n)
    (B : Finset (Fin n × Fin n)) (hB : complete.Spans B) :
    MST.weight (fun e : Fin n × Fin n => w e.1 e.2) (selected w r) ≤ MST.weight (fun e : Fin n × Fin n => w e.1 e.2) B := by
  let H : FiniteGraph (Fin n) (Fin n × Fin n) :=
    { complete with
      edges := B
      src_mem := by intros; exact mem_univ _
      dst_mem := by intros; exact mem_univ _ }
  let K := kruskal (acceptByComponent H.toGraph (components H.toGraph)) B.toList ∅
  have hK : H.IsSpanningTree K := H.kruskal_spanning_tree_of_complete_exact_component
    (components H.toGraph) (components_exact _) B.toList (by simp)
    (by intro e he; exact mem_toList.mp he) (by intro e he; exact mem_toList.mpr he)
    hB H.isForest_empty
  have hK' : complete.IsSpanningTree K := ⟨by intro e he; exact mem_univ e,hK.2⟩
  exact le_trans ((selected_mst w r).2 K hK') (sum_le_sum_of_subset hK.1)

/-- Concrete edge-to-parent composition discharges the old minimum-tree premise. -/
theorem mstParent_minimum (w : TSP.Graph (Fin n)) (r : Fin n)
    (hSymm : ∀ u v, w u v = w v u) : IsMinimumSpanningTreeOn w (mstParent w r) r := by
  refine ⟨mstParent_tree w r,?_⟩
  intro p r' hp
  calc
    treeCost w (mstParent w r) r ≤ MST.weight (fun e : Fin n × Fin n => w e.1 e.2) (selected w r) :=
      parent_cost_le (selectedConnected w r) w hSymm
    _ ≤ MST.weight (fun e : Fin n × Fin n => w e.1 e.2) (parentEdges p r') :=
      selected_le_connected w r _ (parentEdges_spans hp)
    _ = treeCost w p r' := parentEdges_weight w p r'

/-- The actual returned preorder, rooted from the actual Prim-selected edge set. -/
def graphTour (w : TSP.Graph (Fin n)) (r : Fin n) : List (Fin n) :=
  TreeOn.dfsTour (mstParent_tree w r)

theorem graphTour_nodup (w : TSP.Graph (Fin n)) (r : Fin n) : (graphTour w r).Nodup :=
  TreeOn.dfsTour_nodup (mstParent_tree w r)

theorem graphTour_mem (w : TSP.Graph (Fin n)) (r v : Fin n) : v ∈ graphTour w r :=
  TreeOn.dfsTour_mem (mstParent_tree w r) v

theorem graphTour_length (w : TSP.Graph (Fin n)) (r : Fin n) : (graphTour w r).length = n := by
  have heq : (graphTour w r).toFinset = univ := by
    ext v
    simp [graphTour_mem]
  have hc := congrArg Finset.card heq
  simpa [List.toFinset_card_of_nodup (graphTour_nodup w r)] using hc

theorem graphTour_two_approx (w : TSP.Graph (Fin n)) (r : Fin n)
    (hSymm : ∀ u v, w u v = w v u)
    (hTri : ∀ a b c, w a c ≤ w a b + w b c)
    (hLoop : ∀ v, w v v = 0)
    {σ : Fin n → Fin n} (hTour : Tour σ) :
    tourCostTo w r (graphTour w r) ≤ 2*TourCost w σ := by
  have ht := TreeOn.tsp_two_approx (mstParent_minimum w r hSymm) hSymm hTri hLoop hTour
  simpa [graphTour,TreeOn.dfsTour_head] using ht

end CLRS.TSP.GraphAdapter
