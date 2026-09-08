import CLRSLean.FourthEdition.Chapter_24.Section_24_2_Edmonds_Karp.SparseExecution.Support

/-!
# Sparse critical-edge counting for any shortest-path execution

The timeline records actual selected shortest paths and their resulting flows.
Its step equation is instantiated by the counted BFS execution. No equality
with the separate classical shortest-path chooser is required.
-/
noncomputable section
namespace CLRS.Chapter26.SparseEK
open Finset Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

structure Timeline (G : FlowNetwork V) where
  flow : Nat → Flow V G
  path : (i : Nat) → Option (ShortestAugmentingPath (flow i))
  next : ∀ i, flow (i+1) = match path i with
    | none => flow i
    | some p => (flow i).augment p.path

namespace Timeline
variable (T : Timeline G)

def Critical (i : Nat) (u v : V) : Prop :=
  ∃ p, T.path i = some p ∧ p.path.isCritical u v

def Augments (i : Nat) : Prop := ∃ p, T.path i = some p

theorem next_some {i : Nat} {p : ShortestAugmentingPath (T.flow i)}
    (hp : T.path i = some p) : T.flow (i+1) = (T.flow i).augment p.path := by
  rw [T.next, hp]

theorem distance_step (i : Nat) (u : V) {d : Nat}
    (hd : IsShortestDist (T.flow (i+1)) G.s u d) :
    ∃ d', IsShortestDist (T.flow i) G.s u d' ∧ d' ≤ d := by
  rw [T.next] at hd
  cases hp : T.path i with
  | none => exact ⟨d, by simpa [hp] using hd, le_rfl⟩
  | some p => exact p.exists_shortestDist_le_augment (by simpa [hp] using hd)

theorem distance_mono {i j : Nat} (hij : i ≤ j) (u : V) {d : Nat}
    (hd : IsShortestDist (T.flow j) G.s u d) :
    ∃ d', IsShortestDist (T.flow i) G.s u d' ∧ d' ≤ d := by
  induction j, hij using Nat.le_induction generalizing d with
  | base => exact ⟨d,hd,le_rfl⟩
  | succ k hk ih =>
    obtain ⟨dk,hdK,hle⟩ := T.distance_step k u hd
    obtain ⟨di,hdi,hik⟩ := ih hdK
    exact ⟨di,hdi,hik.trans hle⟩

theorem no_reverse_step (i : Nat) (u v : V)
    (hno : ∀ p, T.path i = some p → (v,u) ∉ p.path.edges) :
    (T.flow (i+1)).residualCapacity u v ≤ (T.flow i).residualCapacity u v := by
  rw [T.next]
  cases hp : T.path i with
  | none => exact le_rfl
  | some p =>
    rw [Flow.augment_residualCapacity]
    simp only [if_neg (hno p hp), add_zero]
    split <;> linarith [p.path.bottleneck_pos]

theorem no_reverse_interval {i j : Nat} (hij : i ≤ j) (u v : V)
    (hno : ∀ k, i ≤ k → k < j → ∀ p, T.path k = some p → (v,u) ∉ p.path.edges) :
    (T.flow j).residualCapacity u v ≤ (T.flow i).residualCapacity u v := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
    exact (T.no_reverse_step k u v (hno k hk (by omega))).trans
      (ih (fun l hl hlk => hno l hl (by omega)))

/-- Recovery of a saturated arc requires a real reverse traversal in between. -/
theorem recovery {i j : Nat} (hij : i < j) {u v : V}
    (hci : T.Critical i u v) (hcj : T.Critical j u v) :
    ∃ k, i < k ∧ k < j ∧ ∃ p, T.path k = some p ∧ (v,u) ∈ p.path.edges := by
  obtain ⟨pi,hpi,hei,hzero⟩ := hci
  obtain ⟨pj,hpj,hej,_⟩ := hcj
  have hz : (T.flow (i+1)).residualCapacity u v = 0 := by
    rw [T.next_some hpi]; exact hzero
  have hpos : 0 < (T.flow j).residualCapacity u v :=
    Flow.ResidualPath.residualEdge_of_mem_edges pj.path hej
  by_contra hn
  have hno : ∀ k, i+1 ≤ k → k < j → ∀ p, T.path k = some p → (v,u) ∉ p.path.edges := by
    intro k hik hkj p hp hr
    exact hn ⟨k, by omega, hkj, p, hp, hr⟩
  have hle := T.no_reverse_interval (show i+1 ≤ j by omega) u v hno
  linarith

theorem critical_growth {i j : Nat} (hij : i < j) {u v : V}
    (hci : T.Critical i u v) (hcj : T.Critical j u v) :
    ∃ d d', IsShortestDist (T.flow i) G.s u d ∧
      IsShortestDist (T.flow j) G.s u d' ∧ d < d' := by
  obtain ⟨k,hik,hkj,p,hp,hrev⟩ := T.recovery hij hci hcj
  obtain ⟨pi,hpi,hei,_⟩ := hci
  obtain ⟨pj,hpj,hej,_⟩ := hcj
  obtain ⟨di,dk,hdi,hdk,hgrow⟩ := critical_dist_increase_rev pi p hei hrev
    (fun x d hd => T.distance_mono (by omega) x hd)
  obtain ⟨dj,hdj,_⟩ := shortest_edge_dist pj hej
  obtain ⟨dk',hdk',hle⟩ := T.distance_mono (by omega : k ≤ j) u hdj
  have heq := hdk.unique hdk'
  exact ⟨di,dj,hdi,hdj,by omega⟩

theorem critical_dist {i : Nat} {u v : V} (hc : T.Critical i u v) :
    ∃ d, IsShortestDist (T.flow i) G.s u d ∧ d < Fintype.card V := by
  obtain ⟨p,hp,he,_⟩ := hc
  obtain ⟨d,hd,_⟩ := shortest_edge_dist p he
  exact ⟨d,hd,hd.lt_card⟩

theorem critical_support {i : Nat} {u v : V} (hc : T.Critical i u v) :
    (u,v) ∈ support G := by
  obtain ⟨p,hp,he,_⟩ := hc
  exact residual_mem_support _ (Flow.ResidualPath.residualEdge_of_mem_edges p.path he)

theorem exists_critical (i : Nat) (ha : T.Augments i) : ∃ u v, T.Critical i u v := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨u,v,hc⟩ := exists_critical_edge p.path
  exact ⟨u,v,p,hp,hc⟩

theorem augmentation_count_bound (N : ℕ) :
    ((Finset.range N).filter (fun n => T.Augments n)).card ≤
      (support G).card * Fintype.card V := by
  let s : Finset ℕ :=
    (Finset.range N).filter (fun n => T.Augments n)
  let haug : ∀ x : {n : ℕ // n ∈ s}, T.Augments x.1 :=
    fun x => (Finset.mem_filter.mp x.2).2
  let pair : {n : ℕ // n ∈ s} → V × V := fun x =>
    let h := T.exists_critical x.1 (haug x)
    (Classical.choose h, Classical.choose (Classical.choose_spec h))
  let hcrit : ∀ x : {n : ℕ // n ∈ s},
      T.Critical x.1 (pair x).1 (pair x).2 :=
    fun x =>
      Classical.choose_spec
        (Classical.choose_spec (T.exists_critical x.1 (haug x)))
  let distOf : {n : ℕ // n ∈ s} → ℕ :=
    fun x => Classical.choose (T.critical_dist (hcrit x))
  let f : {n : ℕ // n ∈ s} → (V × V) × Fin (Fintype.card V) :=
    fun x => (pair x, ⟨distOf x, (Classical.choose_spec (T.critical_dist (hcrit x))).2⟩)
  have hinj : Set.InjOn f (↑(s.attach) : Set {n : ℕ // n ∈ s}) := by
    intro x hx y hy hxy
    apply Subtype.ext
    by_contra hne
    have hpair_eq : pair x = pair y := congrArg Prod.fst hxy
    have hdist_eq : distOf x = distOf y :=
      congrArg (fun z : (V × V) × Fin (Fintype.card V) => z.2.1) hxy
    have hcy : T.Critical y.1 (pair x).1 (pair x).2 := by
      simpa [hpair_eq] using hcrit y
    have hlt_or : x.1 < y.1 ∨ y.1 < x.1 := by omega
    rcases hlt_or with hxy_lt | hyx_lt
    · rcases T.critical_growth hxy_lt (hcrit x) hcy with
        ⟨du, du', hdu, hdu', hgrow⟩
      have hdx : distOf x = du :=
        (Classical.choose_spec (T.critical_dist (hcrit x))).1.unique hdu
      have hdy : distOf y = du' := by
        have hd := (Classical.choose_spec (T.critical_dist (hcrit y))).1
        exact hd.unique (by simpa [hpair_eq] using hdu')
      omega
    · rcases T.critical_growth hyx_lt hcy (hcrit x) with
        ⟨du, du', hdu, hdu', hgrow⟩
      have hdy : distOf y = du := by
        have hd := (Classical.choose_spec (T.critical_dist (hcrit y))).1
        exact hd.unique (by simpa [hpair_eq] using hdu)
      have hdx : distOf x = du' :=
        (Classical.choose_spec (T.critical_dist (hcrit x))).1.unique hdu'
      omega
  have hsub : s.attach.image f ⊆ (support G).product
      (Finset.univ : Finset (Fin (Fintype.card V))) := by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨T.critical_support (hcrit y), Finset.mem_univ _⟩
  have hcard : (s.attach.image f).card = s.attach.card :=
    Finset.card_image_of_injOn hinj
  calc
    s.card = s.attach.card := Finset.card_attach.symm
    _ = (s.attach.image f).card := hcard.symm
    _ ≤ ((support G).product (Finset.univ : Finset (Fin (Fintype.card V)))).card :=
      Finset.card_le_card hsub
    _ = (support G).card * Fintype.card V := by simp


theorem augmentation_count_sparse (N : Nat) :
    ((Finset.range N).filter (fun i => T.Augments i)).card ≤
      2 * (positiveArcs G).card * Fintype.card V :=
  (T.augmentation_count_bound N).trans (Nat.mul_le_mul_right _ (support_card_le G))

theorem all_steps_bound (N : Nat) (h : ∀ i < N, T.Augments i) :
    N ≤ (support G).card * Fintype.card V := by
  have hc := T.augmentation_count_bound N
  have heq : (Finset.range N).filter T.Augments = Finset.range N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.left, fun hi => ⟨hi,h i hi⟩⟩
  simpa [heq] using hc

end Timeline
end CLRS.Chapter26.SparseEK
