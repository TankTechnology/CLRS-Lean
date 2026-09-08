import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.ArrayPrim.Queue
import CLRSLean.FourthEdition.Chapter_21.Section_21_2_Kruskal_And_Prim.S4_Completion

/-!
# Adjacency representation and cached-cut invariant

The input is a stored array of adjacency lists. Its representation contract
says that each graph edge contributes its two endpoint incidences, in any row
order. Thus the total adjacency length is derived as twice the edge count;
it is not a supplied bound on the execution's decreases.
-/
namespace CLRS.MST.ExecutablePrim.ArrayPrim
open Finset
variable {n : Nat} {E : Type} [LinearOrder E]

def incidences (G : Graph (Fin n) E) (u : Fin n) (e : E) : List (Fin n × E) :=
  (if G.src e = u then [(G.dst e,e)] else []) ++
    (if G.dst e = u then [(G.src e,e)] else [])

structure Adjacency (G : FiniteGraph (Fin n) E) where
  rows : Vector (List (Fin n × E)) n
  represents : ∀ u : Fin n, (rows[u.val]).Perm
    ((G.edges.sort (· ≤ ·)).flatMap (incidences G.toGraph u))

@[simp] theorem Adjacency.mem_iff {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (u v : Fin n) (e : E) :
    (v,e) ∈ adj.rows[u.val] ↔ e ∈ G.edges ∧
      ((G.src e = u ∧ G.dst e = v) ∨ (G.dst e = u ∧ G.src e = v)) := by
  rw [(adj.represents u).mem_iff]
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨f,hf,h⟩
    simp only [incidences, List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨(G.edges.mem_sort (· ≤ ·)).1 hf, Or.inl ⟨by assumption,rfl⟩⟩
      · simp at h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        exact ⟨(G.edges.mem_sort (· ≤ ·)).1 hf, Or.inr ⟨by assumption,rfl⟩⟩
      · simp at h
  · rintro ⟨he,h⟩
    refine ⟨e, (G.edges.mem_sort (· ≤ ·)).2 he, ?_⟩
    rcases h with ⟨hs,hd⟩ | ⟨hd,hs⟩ <;> simp [incidences, hs, hd]

theorem Adjacency.total_length {G : FiniteGraph (Fin n) E} (adj : Adjacency G) :
    ∑ u : Fin n, (adj.rows[u.val]).length = 2 * G.edges.card := by
  have general (es : List E) :
      ∑ u : Fin n, (es.flatMap (incidences G.toGraph u)).length = 2 * es.length := by
    induction es with
    | nil => simp
    | cons e es ih =>
      simp only [List.flatMap_cons, List.length_append, Finset.sum_add_distrib, ih,
        List.length_cons]
      have h : ∑ u : Fin n, (incidences G.toGraph u e).length = 2 := by
        simp only [incidences, List.length_append]
        simp_rw [apply_ite List.length]
        simp [Finset.sum_add_distrib, eq_comm]
      rw [h]
      omega
  calc
    _ = ∑ u : Fin n,
        ((G.edges.sort (· ≤ ·)).flatMap (incidences G.toGraph u)).length :=
      Finset.sum_congr rfl (fun u _ => (adj.represents u).length_eq)
    _ = _ := by simpa using general (G.edges.sort (· ≤ ·))

/-- All active cells describe the best known parent into the reached set. -/
structure Invariant {G : FiniteGraph (Fin n) E} (adj : Adjacency G) (w : E → Nat)
    (S : Finset (Fin n)) (q : Cells n E) : Prop where
  active : ∀ v, (read q v).active = true ↔ v ∉ S
  parent : ∀ v e, (read q v).active = true → (read q v).parent = some e →
    ∃ u ∈ S, (v,e) ∈ adj.rows[u.val] ∧ (read q v).key = (w e : Key)
  covers : ∀ u ∈ S, ∀ v e, (v,e) ∈ adj.rows[u.val] →
    (read q v).active = true → (read q v).key ≤ (w e : Key)
  none_key : ∀ v, (read q v).parent = none → (read q v).key = ⊤

theorem initialCells_invariant {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) : Invariant adj w ∅ (initialCells n).1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

/-- Remove one vertex and scan only its cached adjacency list. -/
def advance {G : FiniteGraph (Fin n) E} (adj : Adjacency G) (w : E → Nat)
    (q : Cells n E) (u : Fin n) : Relaxed n E :=
  relaxAll w (deactivate q u) adj.rows[u.val]

@[simp] theorem advance_active {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (q : Cells n E) (u v : Fin n) :
    (read (advance adj w q u).cells v).active =
      if u = v then false else (read q v).active := by simp [advance]

theorem advance_invariant {G : FiniteGraph (Fin n) E} (adj : Adjacency G)
    (w : E → Nat) (S : Finset (Fin n)) (q : Cells n E) (u : Fin n)
    (h : Invariant adj w S q) : Invariant adj w (insert u S) (advance adj w q u).cells := by
  have ha (v : Fin n) : (read (advance adj w q u).cells v).active = true ↔
      u ≠ v ∧ (read q v).active = true := by
    by_cases huv : u = v <;> simp [huv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    rw [ha, h.active]
    simp [eq_comm]
  · intro v e hv hp
    obtain ⟨huv,hvold⟩ := (ha v).1 hv
    rcases relaxAll_origin w (deactivate q u) adj.rows[u.val] v with hold | ⟨f,hf,hcell⟩
    · have hpold : (read q v).parent = some e := by
        change (read (relaxAll w (deactivate q u) adj.rows[u.val]).cells v).parent = _ at hp
        rw [hold, deactivate_parent] at hp
        exact hp
      obtain ⟨x,hx,he,hkey⟩ := h.parent v e hvold hpold
      refine ⟨x, mem_insert_of_mem hx, he, ?_⟩
      change (read (relaxAll w (deactivate q u) adj.rows[u.val]).cells v).key = _
      rw [hold, deactivate_key, hkey]
    · have hfe : f = e := by
        change (read (relaxAll w (deactivate q u) adj.rows[u.val]).cells v).parent = _ at hp
        rw [hcell] at hp
        exact Option.some.inj hp
      subst f
      exact ⟨u, mem_insert_self _ _, hf, congrArg Cell.key hcell⟩
  · intro x hx v e he hv
    obtain ⟨huv,hvold⟩ := (ha v).1 hv
    rcases mem_insert.mp hx with hx | hx
    · subst x
      apply relaxAll_target_le w (deactivate q u) _ v e he
      simpa [huv] using hvold
    · exact (relaxAll_key_le w (deactivate q u) _ v).trans
        (by simpa using h.covers x hx v e he hvold)
  · intro v hp
    rcases relaxAll_origin w (deactivate q u) adj.rows[u.val] v with hold | ⟨e,he,hcell⟩
    · have hpold : (read q v).parent = none := by
        change (read (relaxAll w (deactivate q u) adj.rows[u.val]).cells v).parent = _ at hp
        rw [hold, deactivate_parent] at hp
        exact hp
      change (read (relaxAll w (deactivate q u) adj.rows[u.val]).cells v).key = _
      rw [hold, deactivate_key, h.none_key v hpold]
    · change (read (relaxAll w (deactivate q u) adj.rows[u.val]).cells v).parent = _ at hp
      rw [hcell] at hp
      contradiction

/-- Selecting a finite parent yields a real crossing edge and its outside vertex. -/
theorem Invariant.selected {G : FiniteGraph (Fin n) E} {adj : Adjacency G}
    {w : E → Nat} {S : Finset (Fin n)} {q : Cells n E} (h : Invariant adj w S q)
    (indices : List (Fin n)) (hfull : ∀ v, v ∈ indices)
    {u : Fin n} {c : Cell E} {e : E}
    (hs : (scan q indices).choice = some (u,c)) (hp : c.parent = some e) :
    e ∈ G.edges ∧ G.toGraph.Crosses S e ∧ outsideVertex G.toGraph S e = u ∧
      ∀ f ∈ G.edges, G.toGraph.Crosses S f → w e ≤ w f := by
  obtain ⟨_,rfl,hu,hmin⟩ := scan_some q _ u c hs
  obtain ⟨x,hx,he,hkey⟩ := h.parent u e hu hp
  have hout := (h.active u).1 hu
  obtain ⟨heG,heEnds⟩ := adj.mem_iff x u e |>.1 he
  have hc : G.toGraph.Crosses S e := by
    rcases heEnds with ⟨hsrc,hdst⟩ | ⟨hdst,hsrc⟩
    · exact Or.inl ⟨hsrc ▸ hx, hdst ▸ hout⟩
    · exact Or.inr ⟨hdst ▸ hx, hsrc ▸ hout⟩
  refine ⟨heG, hc, ?_, ?_⟩
  · rcases heEnds with ⟨hsrc,hdst⟩ | ⟨hdst,hsrc⟩ <;>
      simp [outsideVertex, hsrc, hdst, hx, hout]
  · intro f hf hfc
    let v := outsideVertex G.toGraph S f
    have hv : v ∉ S := outsideVertex_not_mem hfc
    have hvc := (h.active v).2 hv
    have hcover : (read q v).key ≤ (w f : Key) := by
      rcases hfc with hfc | hfc
      · have hm : (v,f) ∈ adj.rows[(G.src f).val] := by
          apply (adj.mem_iff _ _ _).2
          exact ⟨hf, Or.inl ⟨rfl, by simp [v, outsideVertex, hfc.1]⟩⟩
        exact h.covers _ hfc.1 v f hm hvc
      · have hsrc : G.src f ∉ S := hfc.2
        have hm : (v,f) ∈ adj.rows[(G.dst f).val] := by
          apply (adj.mem_iff _ _ _).2
          exact ⟨hf, Or.inr ⟨rfl, by simp [v, outsideVertex, hsrc]⟩⟩
        exact h.covers _ hfc.1 v f hm hvc
    have hm := hmin v (hfull v) hvc
    rw [hkey] at hm
    exact_mod_cast hm.trans hcover

end CLRS.MST.ExecutablePrim.ArrayPrim
