import CLRSLean.FourthEdition.Chapter_35.Section_35_2_The_Traveling_Salesperson_Problem
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S4_Completion

/-!
# Rooting a selected connected edge set

Shortest unweighted root-path distances select strictly decreasing parents.
Every non-root vertex is assigned a selected edge, and these assignments are
injective: opposite uses of one edge would contradict strict depth decrease.
Thus rooting costs no more than the supplied selected edge set. The choice of
shortest predecessors is classical; this module makes no running-time claim.
-/
noncomputable section
namespace CLRS.TSP.GraphAdapter
open Finset Classical
variable {V E : Type} [Fintype V] [DecidableEq V] [DecidableEq E]

/-- The exact finite component interface, constructed from graph connectivity. -/
def components (G : MST.Graph V E) : MST.ComponentOracle G where
  component A root := univ.filter (G.ConnectedIn A root)
  mem_self A v := by simp [MST.Graph.connected_refl]
  closed_src A root e he hs := by
    simp only [mem_filter,mem_univ,true_and] at *
    exact MST.Graph.connected_trans hs (MST.Graph.connected_of_mem_edge he)
  closed_dst A root e he hs := by
    simp only [mem_filter,mem_univ,true_and] at *
    exact MST.Graph.connected_trans hs (MST.Graph.connected_symm (MST.Graph.connected_of_mem_edge he))

omit [DecidableEq V] [DecidableEq E] in
theorem components_exact (G : MST.Graph V E) : MST.ExactComponentOracle G (components G) := by
  intro A root v
  simp [components]

inductive Hops (G : MST.Graph V E) (A : Finset E) (root : V) : Nat → V → Prop
  | root : Hops G A root 0 root
  | step {d u v} : Hops G A root d u → G.AdjIn A u v → Hops G A root (d+1) v

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
private theorem hops_exists {G : MST.Graph V E} {A : Finset E} {r v : V}
    (h : G.ConnectedIn A r v) : ∃ d, Hops G A r d v := by
  induction h with
  | refl => exact ⟨0,.root⟩
  | tail _ he ih => obtain ⟨d,hd⟩ := ih; exact ⟨d+1,.step hd he⟩

structure ConnectedSelection (G : MST.Graph V E) (A : Finset E) (r : V) : Prop where
  reaches : ∀ v, G.ConnectedIn A r v

variable {G : MST.Graph V E} {A : Finset E} {r : V}

def depth (h : ConnectedSelection G A r) (v : V) : Nat := Nat.find (hops_exists (h.reaches v))

theorem depth_spec (h : ConnectedSelection G A r) (v : V) : Hops G A r (depth h v) v :=
  Nat.find_spec (hops_exists (h.reaches v))

theorem depth_le (h : ConnectedSelection G A r) {d : Nat} {v : V} (hd : Hops G A r d v) :
    depth h v ≤ d := Nat.find_min' _ hd

@[simp] theorem depth_root (h : ConnectedSelection G A r) : depth h r = 0 :=
  Nat.eq_zero_of_le_zero (depth_le h Hops.root)

theorem predecessor_exists (h : ConnectedSelection G A r) {v : V} (hv : v ≠ r) :
    ∃ u e, e ∈ A ∧ ((G.src e = v ∧ G.dst e = u) ∨ (G.src e = u ∧ G.dst e = v)) ∧
      depth h u < depth h v := by
  have hp := depth_spec h v
  generalize hd : depth h v = d at hp
  cases hp with
  | root => exact (hv rfl).elim
  | @step d u v hp he =>
    obtain ⟨e,he,hor⟩ := he
    exact ⟨u,e,he,hor.symm,by have := depth_le h hp; omega⟩

def parent (h : ConnectedSelection G A r) (v : V) : V :=
  if hv : v=r then r else (predecessor_exists h hv).choose

def parentEdge (h : ConnectedSelection G A r) (v : V) (hv : v ≠ r) : E :=
  ((predecessor_exists h hv).choose_spec).choose

theorem parent_spec (h : ConnectedSelection G A r) (v : V) (hv : v ≠ r) :
    parentEdge h v hv ∈ A ∧
      ((G.src (parentEdge h v hv)=v ∧ G.dst (parentEdge h v hv)=parent h v) ∨
       (G.src (parentEdge h v hv)=parent h v ∧ G.dst (parentEdge h v hv)=v)) ∧
      depth h (parent h v) < depth h v := by
  simpa [parent,parentEdge,hv] using ((predecessor_exists h hv).choose_spec).choose_spec

@[simp] theorem parent_root (h : ConnectedSelection G A r) : parent h r = r := by simp [parent]

theorem parent_tree (h : ConnectedSelection G A r) : TreeOn (parent h) r := by
  refine ⟨parent_root h,?_⟩
  intro v
  induction hv : depth h v using Nat.strong_induction_on generalizing v with
  | h d ih =>
    by_cases hvr : v=r
    · exact ⟨0,hvr⟩
    · obtain ⟨k,hk⟩ := ih (depth h (parent h v)) (by simpa [hv] using (parent_spec h v hvr).2.2)
        (parent h v) rfl
      exact ⟨k+1,by simpa only [Function.iterate_succ_apply] using hk⟩

theorem parentEdge_injective (h : ConnectedSelection G A r) {u v : V}
    (hu : u ≠ r) (hv : v ≠ r) (he : parentEdge h u hu = parentEdge h v hv) : u=v := by
  obtain ⟨_,hue,hud⟩ := parent_spec h u hu
  obtain ⟨_,hve,hvd⟩ := parent_spec h v hv
  rw [he] at hue
  rcases hue with hu' | hu' <;> rcases hve with hv' | hv'
  · exact hu'.1.symm.trans hv'.1
  · have huv : u = parent h v := hu'.1.symm.trans hv'.1
    have hvu : v = parent h u := hv'.2.symm.trans hu'.2
    have hdu := congrArg (depth h) huv
    have hdv := congrArg (depth h) hvu
    omega
  · have huv : u = parent h v := hu'.2.symm.trans hv'.2
    have hvu : v = parent h u := hv'.1.symm.trans hu'.1
    have hdu := congrArg (depth h) huv
    have hdv := congrArg (depth h) hvu
    omega
  · exact hu'.2.symm.trans hv'.2

/-- Parent maintenance assigns distinct selected edges; nonnegative weights suffice. -/
theorem parent_cost_le (h : ConnectedSelection G A r) (w : TSP.Graph V)
    (hSymm : ∀ u v, w u v = w v u) :
    treeCost w (parent h) r ≤ MST.weight (fun e => w (G.src e) (G.dst e)) A := by
  classical
  by_cases hA : A.Nonempty
  · let f : V → E := fun v => if hv : v ≠ r then parentEdge h v hv else hA.choose
    have hf : ∀ v ∈ univ.erase r, f v ∈ A := by
      intro v hv
      simpa [f,(mem_erase.mp hv).1] using (parent_spec h v (mem_erase.mp hv).1).1
    have hinj : Set.InjOn f (univ.erase r : Finset V) := by
      intro u hu v hv he
      apply parentEdge_injective h (mem_erase.mp hu).1 (mem_erase.mp hv).1
      simpa [f,(mem_erase.mp hu).1,(mem_erase.mp hv).1] using he
    calc
      treeCost w (parent h) r = ∑ v ∈ univ.erase r, w (G.src (f v)) (G.dst (f v)) := by
        apply sum_congr rfl
        intro v hv
        have hn := (mem_erase.mp hv).1
        obtain ⟨_,hor,_⟩ := parent_spec h v hn
        rcases hor with hor | hor
        · simp [f,hn,hor.1,hor.2]
        · simp [f,hn,hor.1,hor.2,hSymm]
      _ = ∑ e ∈ (univ.erase r).image f, w (G.src e) (G.dst e) := (sum_image (f := fun e => w (G.src e) (G.dst e)) hinj).symm
      _ ≤ MST.weight (fun e => w (G.src e) (G.dst e)) A := by
        apply sum_le_sum_of_subset
        intro e he
        obtain ⟨v,hv,rfl⟩ := mem_image.mp he
        exact hf v hv
  · have hzero : univ.erase r = (∅ : Finset V) := by
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hA ⟨parentEdge h v (mem_erase.mp hv).1,(parent_spec h v (mem_erase.mp hv).1).1⟩
    simp [treeCost,hzero]

end CLRS.TSP.GraphAdapter
