import CLRSLean.FourthEdition.Chapter_24.Section_24_5_Relabel_To_Front

/-!
An initialized relabel-to-front execution with persistent current-neighbor lists.

Initialization writes the complete flow table and height/excess/cursor tables.
The scheduler scans inactive entries and rejected neighbors, pushes using cached
excess and two indexed arc writes, and relabels with a counted minimum scan.
A reversed processed prefix supports constant-cost discharge completion; moving
it to the front uses a counted reverse-onto loop. Relabeling immediately moves
the current vertex to the front, where its discharge continues.

The ordering, quiet-prefix, and skipped-neighbor invariants are preserved by the
controller itself. Its operation trace therefore satisfies the native discharge
discipline without an input certificate. The native cubic operation bound proves
that the concrete fuelled run terminates; its returned preflow is a maximum flow.

The work theorem counts actual initialization writes, controller/cursor visits,
minimum-scan visits, and moved list cells from this run. The scalar/indexed RAM
charge assigns a fixed 32-unit allowance to each such event. Exact real arithmetic
and indexed tables are primitives in this model; this is not a persistent Lean
function-evaluator time bound, a mutable-array refinement, or a bit-complexity
claim for arbitrary real capacities.
-/

namespace CLRS.Chapter26.RelabelExecution
open Finset Classical
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : FlowNetwork V}

noncomputable def initialFunction (G : FlowNetwork V) (u v : V) : ℝ :=
  if u = G.s then G.c G.s v else if v = G.s then -G.c G.s u else 0

theorem initialFunction_skew (G : FlowNetwork V) (u v : V) :
    initialFunction G u v = -initialFunction G v u := by
  by_cases hu : u = G.s <;> by_cases hv : v = G.s <;>
    simp [initialFunction, hu, hv, G.hc_self]

theorem initialFunction_capacity (G : FlowNetwork V) (u v : V) :
    initialFunction G u v ≤ G.c u v := by
  by_cases hu : u = G.s
  · subst u; simp [initialFunction]
  · by_cases hv : v = G.s
    · subst v
      simp only [initialFunction, if_neg hu, ↓reduceIte]
      linarith [G.hc_nonneg G.s u, G.hc_nonneg u G.s]
    · simpa [initialFunction, hu, hv] using G.hc_nonneg u v

theorem initialFunction_excess (G : FlowNetwork V) (u : V) (hu : u ≠ G.s) :
    netInflow (initialFunction G) u = G.c G.s u := by
  unfold netInflow
  simp [initialFunction, hu]

/-- Indexed writes over an explicit finite enumeration. Counter increments occur
at the same recursive nodes that install the returned cells. -/
def writeCells {ι α : Type*} [DecidableEq ι] (value : ι → α) (base : ι → α) :
    List ι → (ι → α) × Nat
  | [] => (base, 0)
  | i :: is =>
      let tail := writeCells value base is
      (Function.update tail.1 i (value i), tail.2 + 1)

@[simp] theorem writeCells_count {ι α : Type*} [DecidableEq ι]
    (value base : ι → α) (is : List ι) : (writeCells value base is).2 = is.length := by
  induction is with
  | nil => rfl
  | cons i is ih => simpa [writeCells] using ih

theorem writeCells_value {ι α : Type*} [DecidableEq ι]
    (value base : ι → α) (is : List ι) (a : ι) :
    (writeCells value base is).1 a = if a ∈ is then value a else base a := by
  induction is with
  | nil => simp [writeCells]
  | cons i is ih => by_cases h : a = i <;> simp [writeCells, Function.update, h, ih]

noncomputable def tabulate {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (value : ι → α) (default : α) : (ι → α) × Nat :=
  writeCells value (fun _ => default) univ.toList

@[simp] theorem tabulate_value {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (value : ι → α) (default : α) : (tabulate value default).1 = value := by
  funext a; simp [tabulate, writeCells_value]

@[simp] theorem tabulate_count {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (value : ι → α) (default : α) : (tabulate value default).2 = Fintype.card ι := by
  simp [tabulate]

noncomputable def initialCells (G : FlowNetwork V) : (V × V → ℝ) × Nat :=
  tabulate (fun p => initialFunction G p.1 p.2) 0

@[simp] theorem initialCells_value (G : FlowNetwork V) (u v : V) :
    (initialCells G).1 (u,v) = initialFunction G u v := by simp [initialCells]

noncomputable def initialPreflow (G : FlowNetwork V) : Preflow V G where
  f := fun u v => (initialCells G).1 (u,v)
  hcapacity := by simpa using initialFunction_capacity G
  hskew_symm := by simpa using initialFunction_skew G
  hexcess_nonneg := by
    intro u hu
    simp only [initialCells_value]
    rw [initialFunction_excess G u hu]
    exact G.hc_nonneg G.s u

def initialHeight (G : FlowNetwork V) (u : V) : Nat := if u = G.s then Fintype.card V else 0

theorem initial_valid (G : FlowNetwork V) : IsValidHeight (initialPreflow G) (initialHeight G) := by
  refine ⟨by simp [initialHeight], by simp [initialHeight, Ne.symm G.hs_ne_t], ?_⟩
  intro u v hr
  by_cases hu : u = G.s
  · subst u
    have hz : (initialPreflow G).residualCapacity G.s v = 0 := by
      simp [Preflow.residualCapacity, initialPreflow, initialFunction]
    exact (show False from by change 0 < _ at hr; rw [hz] at hr; linarith).elim
  · simp [initialHeight, hu]

/-- Push changes only its two endpoint excesses. -/
theorem push_excess (φ : Preflow V G) (u v : V) (hu : u ≠ G.s)
    (hr : φ.residualEdge u v) (a : V) :
    (push φ u v hu hr).excess a = φ.excess a +
      (if a = v then min (φ.excess u) (φ.residualCapacity u v) else 0) -
      (if a = u then min (φ.excess u) (φ.residualCapacity u v) else 0) := by
  unfold push pushBy Preflow.excess netInflow
  rw [Finset.sum_add_distrib]
  have hed (δ : ℝ) : ∑ x : V, Flow.edgeDelta δ u v x a =
      (if a = v then δ else 0) - (if a = u then δ else 0) := by
    unfold Flow.edgeDelta
    rw [Finset.sum_sub_distrib]
    have hf : (∑ x : V, if x = u ∧ a = v then δ else 0) = (if a = v then δ else 0) := by
      by_cases ha : a = v
      · subst a; simp
      · simp [ha]
    have hg : (∑ x : V, if x = v ∧ a = u then δ else 0) = (if a = u then δ else 0) := by
      by_cases ha : a = u
      · subst a; simp
      · simp [ha]
    rw [hf, hg]
  rw [hed]
  ring

theorem push_valid (φ : Preflow V G) (h : V → Nat) (hv : IsValidHeight φ h)
    (u v : V) (hu : φ.isOverflowing u) (hr : φ.residualEdge u v)
    (ha : h u = h v + 1) : IsValidHeight (push φ u v hu.1 hr) h := by
  unfold push
  exact pushBy_validHeight φ h hv _ _ _ _ _ _ _ ha

theorem push_new_admissible (φ : Preflow V G) (h : V → Nat)
    (u v : V) (hu : φ.isOverflowing u) (hr : φ.residualEdge u v)
    (ha : h u = h v + 1) (a b : V)
    (hab : admissibleEdge (push φ u v hu.1 hr) h a b) : admissibleEdge φ h a b := by
  refine ⟨?_, hab.2⟩
  by_contra hn
  have hnew := pushBy_new_residualEdge φ u v (residualEdge_ne φ hr)
    (min (φ.excess u) (φ.residualCapacity u v))
    (le_min (φ.hexcess_nonneg u hu.1) (le_of_lt hr))
    (min_le_left _ _) (min_le_right _ _) hab.1 hn
  rcases hnew with ⟨rfl, rfl⟩
  have hh := hab.2
  omega

/-- A skipped neighbor stays ineligible until this source is relabeled. -/
def CursorInvariant (φ : Preflow V G) (h : V → Nat) (cursor : V → List V) : Prop :=
  ∀ u v, v ∉ cursor u → φ.residualEdge u v → h u ≤ h v

theorem cursor_push (φ : Preflow V G) (h : V → Nat) (cursor : V → List V)
    (hc : CursorInvariant φ h cursor) (u v : V) (hu : φ.isOverflowing u)
    (hr : φ.residualEdge u v) (ha : h u = h v + 1) :
    CursorInvariant (push φ u v hu.1 hr) h cursor := by
  intro a b hb hnew
  by_cases hold : φ.residualEdge a b
  · exact hc a b hb hold
  · have hrev := pushBy_new_residualEdge φ u v (residualEdge_ne φ hr)
      (min (φ.excess u) (φ.residualCapacity u v))
      (le_min (φ.hexcess_nonneg u hu.1) (le_of_lt hr))
      (min_le_left _ _) (min_le_right _ _) hnew hold
    rcases hrev with ⟨rfl, rfl⟩
    omega

theorem cursor_relabel (φ : Preflow V G) (h : V → Nat) (cursor : V → List V)
    (hc : CursorInvariant φ h cursor) (u : V) (hr : ∃ v, φ.residualEdge u v)
    (hpre : ∀ v, φ.residualEdge u v → h u ≤ h v) :
    CursorInvariant φ (relabel φ h u hr) (Function.update cursor u univ.toList) := by
  intro a b hb hab
  by_cases ha : a = u
  · subst a; simp at hb
  · have hold : b ∉ cursor a := by simpa [Function.update, ha] using hb
    have hle := hc a b hold hab
    have hup := (relabel_height_increase φ h u hr hpre).le
    rw [relabel_eq_of_ne φ h u hr ha]
    by_cases hbu : b = u
    · subst b; exact hle.trans hup
    · rwa [relabel_eq_of_ne φ h u hr hbu]


def Internal (G : FlowNetwork V) (u : V) : Prop := u ≠ G.s ∧ u ≠ G.t

def Ordered (φ : Preflow V G) (h : V → Nat) (L : List V) : Prop :=
  L.Pairwise (fun a b => ¬ admissibleEdge φ h b a)

structure Machine (G : FlowNetwork V) where
  φ : Preflow V G
  h : V → Nat
  excessCache : V → ℝ
  cache_correct : ∀ u, u ≠ G.s → excessCache u = φ.excess u
  valid : IsValidHeight φ h
  past : List V
  todo : List V
  nodup : (past.reverse ++ todo).Nodup
  complete : ∀ v, v ∈ past.reverse ++ todo ↔ Internal G v
  ordered : Ordered φ h (past.reverse ++ todo)
  quiet : ∀ v ∈ past.reverse, ¬ φ.isOverflowing v
  cursor : V → List V
  cursor_bound : ∀ v, (cursor v).length ≤ Fintype.card V
  skipped : CursorInvariant φ h cursor

def Machine.done (s : Machine G) : List V := s.past.reverse

noncomputable def selectInternal (G : FlowNetwork V) : List V → List V × Nat
  | [] => ([], 0)
  | u :: us =>
      let tail := selectInternal G us
      (if Internal G u then u :: tail.1 else tail.1, tail.2 + 1)

@[simp] theorem selectInternal_value (G : FlowNetwork V) (xs : List V) :
    (selectInternal G xs).1 = xs.filter (fun v => decide (Internal G v)) := by
  induction xs with
  | nil => rfl
  | cons u us ih => by_cases hu : Internal G u <;> simp [selectInternal, hu, ih]

@[simp] theorem selectInternal_count (G : FlowNetwork V) (xs : List V) :
    (selectInternal G xs).2 = xs.length := by
  induction xs with
  | nil => rfl
  | cons u us ih => simpa [selectInternal] using ih

noncomputable def initialMachine (G : FlowNetwork V) : Machine G where
  φ := initialPreflow G
  h := (tabulate (initialHeight G) 0).1
  excessCache := (tabulate (G.c G.s) 0).1
  cache_correct := by intro u hu; simpa [initialPreflow, Preflow.excess] using (initialFunction_excess G u hu).symm
  valid := by simpa using initial_valid G
  past := []
  todo := (selectInternal G univ.toList).1
  nodup := by simpa using (Finset.nodup_toList (univ : Finset V)).filter _
  complete := by simp
  ordered := by
    simp only [List.reverse_nil, List.nil_append, selectInternal_value]
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hadm
    have hia : (univ.toList.filter (fun v => decide (Internal G v)))[i] ≠ G.s := by
      have hm := List.getElem_mem hi
      exact (of_decide_eq_true (List.mem_filter.mp hm).2).1
    have hja : (univ.toList.filter (fun v => decide (Internal G v)))[j] ≠ G.s := by
      have hm := List.getElem_mem hj
      exact (of_decide_eq_true (List.mem_filter.mp hm).2).1
    have he := hadm.2
    simp only [tabulate_value] at he
    change (if (univ.toList.filter (fun v => decide (Internal G v)))[j] = G.s then Fintype.card V else 0) =
      (if (univ.toList.filter (fun v => decide (Internal G v)))[i] = G.s then Fintype.card V else 0) + 1 at he
    rw [if_neg hja, if_neg hia] at he
    omega
  quiet := by simp
  cursor := (tabulate (fun _ : V => (univ.toList : List V)) []).1
  cursor_bound := by simp
  skipped := by intro u v hv; simp at hv

noncomputable def credit (s : Machine G) : Nat :=
  s.todo.length + ∑ v, (s.cursor v).length

theorem credit_initial (G : FlowNetwork V) :
    credit (initialMachine G) ≤ Fintype.card V + Fintype.card V * Fintype.card V := by
  have hl := List.length_filter_le (fun v => decide (Internal G v)) (univ.toList : List V)
  simp only [Finset.length_toList, Finset.card_univ] at hl
  simpa [credit, initialMachine] using Nat.add_le_add_right hl (Fintype.card V * Fintype.card V)

theorem ordered_push (s : Machine G) (u v : V) (hu : s.φ.isOverflowing u)
    (hr : s.φ.residualEdge u v) (ha : s.h u = s.h v + 1) :
    Ordered (push s.φ u v hu.1 hr) s.h (s.done ++ s.todo) := by
  apply s.ordered.imp
  intro a b hold hn
  exact hold (push_new_admissible s.φ s.h u v hu hr ha b a hn)

theorem current_not_done (s : Machine G) {u : V} {us : List V} (ht : s.todo = u :: us) :
    u ∉ s.done := by
  have hn := s.nodup
  rw [ht, List.nodup_append] at hn
  intro hu
  exact hn.2.2 u hu u (by simp) rfl

theorem current_internal (s : Machine G) {u : V} {us : List V} (ht : s.todo = u :: us) :
    Internal G u := (s.complete u).1 (by simp [ht])

theorem push_quiet_done (s : Machine G) {u : V} {us : List V} (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) :
    ∀ a ∈ s.done, ¬ (push s.φ u v hu.1 hr).isOverflowing a := by
  intro a haD hover
  have hau : a ≠ u := by intro h; subst a; exact current_not_done s ht haD
  have hav : a ≠ v := by
    intro h; subst a
    have hord := List.pairwise_append.mp s.ordered
    exact hord.2.2 v haD u (by simp [ht]) ⟨hr, ha⟩
  have he : (push s.φ u v hu.1 hr).excess a = s.φ.excess a := by
    rw [push_excess]; simp [hau, hav]
  exact s.quiet a haD ⟨hover.1, hover.2.1, by simpa [he] using hover.2.2⟩

noncomputable def skipCurrent (s : Machine G) (u : V) (us : List V)
    (ht : s.todo = u :: us) (hq : ¬ s.φ.isOverflowing u) : Machine G :=
  { s with
    past := u :: s.past
    todo := us
    nodup := by simpa [ht, Machine.done, List.reverse_cons, List.append_assoc] using s.nodup
    complete := by intro v; simpa [ht, Machine.done, List.reverse_cons, List.append_assoc] using s.complete v
    ordered := by simpa [ht, Machine.done, List.reverse_cons, List.append_assoc] using s.ordered
    quiet := by
      intro v hv
      simp only [List.reverse_cons] at hv
      rcases List.mem_append.mp hv with hv | hv
      · exact s.quiet v hv
      · simpa using (List.mem_singleton.mp hv) ▸ hq }

theorem credit_skip (s : Machine G) (u : V) (us : List V)
    (ht : s.todo = u :: us) (hq : ¬ s.φ.isOverflowing u) :
    credit (skipCurrent s u us ht hq) + 1 = credit s := by
  simp [credit, skipCurrent, ht]
  omega

noncomputable def advanceCursor (s : Machine G) (u v : V) (vs : List V)
    (hc : s.cursor u = v :: vs) (hn : ¬ admissibleEdge s.φ s.h u v) : Machine G :=
  { s with
    cursor := Function.update s.cursor u vs
    cursor_bound := by
      intro a
      by_cases ha : a = u
      · subst a; simp only [Function.update_self]
        have hb := s.cursor_bound u; rw [hc] at hb; simpa using Nat.le_trans (Nat.le_succ _) hb
      · simpa [Function.update, ha] using s.cursor_bound a
    skipped := by
      intro a b hb hr
      by_cases ha : a = u
      · subst a
        simp only [Function.update_self] at hb
        by_cases hbv : b = v
        · subst b
          have hv := s.valid.2.2 u v hr
          have hne : s.h u ≠ s.h v + 1 := fun he => hn ⟨hr, he⟩
          omega
        · apply s.skipped u b ?_ hr
          simp [hc, hb, hbv]
      · apply s.skipped a b ?_ hr
        simpa [Function.update, ha] using hb }

theorem credit_advanceCursor (s : Machine G) (u v : V) (vs : List V)
    (hc : s.cursor u = v :: vs) (hn : ¬ admissibleEdge s.φ s.h u v) :
    credit (advanceCursor s u v vs hc hn) + 1 = credit s := by
  unfold credit
  have hfun : (fun a => ((advanceCursor s u v vs hc hn).cursor a).length) =
      Function.update (fun a => (s.cursor a).length) u vs.length := by
    funext a
    by_cases ha : a = u <;> simp [advanceCursor, Function.update, ha]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ u)]
  have hs := Finset.sum_erase_add (univ : Finset V) (fun a => (s.cursor a).length) (mem_univ u)
  rw [hc] at hs
  simp only [List.length_cons] at hs
  simp only [advanceCursor]
  rw [Finset.sdiff_singleton_eq_erase]
  omega


theorem ordered_relabel (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (hr : ∃ v, s.φ.residualEdge u v)
    (hp : ∀ v, s.φ.residualEdge u v → s.h u ≤ s.h v) :
    Ordered s.φ (relabel s.φ s.h u hr) (u :: (s.done ++ us)) := by
  have hn : (u :: (s.done ++ us)).Nodup := List.perm_middle.nodup (by simpa [ht, Machine.done] using s.nodup)
  have hnot := (List.nodup_cons.mp hn).1
  have ho : Ordered s.φ s.h (s.done ++ us) := by
    exact s.ordered.sublist (by rw [ht]; exact List.Sublist.append (List.Sublist.refl _) (List.sublist_cons_self _ _))
  apply List.Pairwise.cons
  · intro a ha hadm
    have hau : a ≠ u := by intro he; subst a; exact hnot ha
    have old := s.valid.2.2 a u hadm.1
    have inc := relabel_height_increase s.φ s.h u hr hp
    have eqn := hadm.2
    rw [relabel_eq_of_ne s.φ s.h u hr hau] at eqn
    omega
  · apply List.Pairwise.imp_of_mem _ ho
    intro a b ha hb hold hnew
    have hau : a ≠ u := by intro he; subst a; exact hnot ha
    have hbu : b ≠ u := by intro he; subst b; exact hnot hb
    apply hold
    refine ⟨hnew.1, ?_⟩
    simpa only [relabel_eq_of_ne s.φ s.h u hr hau,
      relabel_eq_of_ne s.φ s.h u hr hbu] using hnew.2

/-- A literal residual-neighbor scan: one candidate visit at every list cell. -/
noncomputable def scanMinimum (φ : Preflow V G) (h : V → Nat) (u : V) :
    List V → WithTop Nat × Nat
  | [] => (⊤, 0)
  | v :: vs =>
      let tail := scanMinimum φ h u vs
      (if φ.residualEdge u v then min (h v : WithTop Nat) tail.1 else tail.1, tail.2 + 1)

@[simp] theorem scanMinimum_visits (φ : Preflow V G) (h : V → Nat) (u : V) (vs : List V) :
    (scanMinimum φ h u vs).2 = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simpa [scanMinimum] using ih

theorem scanMinimum_value (φ : Preflow V G) (h : V → Nat) (u : V) (vs : List V) :
    (scanMinimum φ h u vs).1 = ((vs.filter fun v => decide (φ.residualEdge u v)).map h).minimum := by
  induction vs with
  | nil => simp [scanMinimum]
  | cons v vs ih => by_cases hv : φ.residualEdge u v <;> simp [scanMinimum, hv, ih, List.minimum_cons]

noncomputable def scannedRelabel (φ : Preflow V G) (h : V → Nat) (u : V) : V → Nat :=
  let least := (scanMinimum φ h u univ.toList).1.untopD 0
  Function.update h u (1 + least)

theorem scannedRelabel_eq (φ : Preflow V G) (h : V → Nat) (u : V)
    (hr : ∃ v, φ.residualEdge u v) : scannedRelabel φ h u = relabel φ h u hr := by
  let S := ((univ : Finset V).filter (fun v => φ.residualEdge u v)).image h
  have hS : S.Nonempty := by
    obtain ⟨v, hv⟩ := hr
    exact ⟨h v, mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩, rfl⟩⟩
  have heq : (scanMinimum φ h u univ.toList).1 = (S.min' hS : WithTop Nat) := by
    rw [scanMinimum_value]
    apply (List.minimum_eq_coe_iff (m := S.min' hS)).mpr
    constructor
    · obtain ⟨v, hv, he⟩ := mem_image.mp (Finset.min'_mem S hS)
      exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨by simp, by simpa using (mem_filter.mp hv).2⟩, he⟩
    · intro a ha
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
      exact Finset.min'_le S _ (mem_image.mpr ⟨v, mem_filter.mpr ⟨mem_univ _,
        by simpa using (List.mem_filter.mp hv).2⟩, rfl⟩)
  funext a
  by_cases hau : a = u
  · subst a
    simp only [scannedRelabel, heq, Function.update_self]
    calc
      _ = 1 + S.min' hS := congrArg (1 + ·) (WithTop.untopD_coe 0 (S.min' hS))
      _ = _ := by unfold relabel; simp only [↓reduceIte]; rfl
  · simp [scannedRelabel, hau, relabel_eq_of_ne φ h u hr hau]

/-- Reverse the processed prefix directly onto the remaining suffix. Each visited
cell performs one cons; no repeated append traversal is hidden in a discharge. -/
def reverseOnto {α : Type*} : List α → List α → List α × Nat
  | [], acc => (acc, 0)
  | a :: as, acc =>
      let tail := reverseOnto as (a :: acc)
      (tail.1, tail.2 + 1)

@[simp] theorem reverseOnto_value {α : Type*} (xs acc : List α) :
    (reverseOnto xs acc).1 = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp [reverseOnto]
  | cons a as ih => simp [reverseOnto, ih, List.reverse_cons, List.append_assoc]

@[simp] theorem reverseOnto_count {α : Type*} (xs acc : List α) :
    (reverseOnto xs acc).2 = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons a as ih => simp [reverseOnto, ih]

noncomputable def relabelCurrent (s : Machine G) (u : V) (us : List V)
    (ht : s.todo = u :: us) (hu : s.φ.isOverflowing u)
    (hr : ∃ v, s.φ.residualEdge u v)
    (hp : ∀ v, s.φ.residualEdge u v → s.h u ≤ s.h v) : Machine G where
  φ := s.φ
  h := scannedRelabel s.φ s.h u
  excessCache := s.excessCache
  cache_correct := s.cache_correct
  valid := by rw [scannedRelabel_eq _ _ _ hr]; exact relabel_validHeight s.φ s.h s.valid u hu.1 hu.2.1 hr hp
  past := []
  todo := u :: (reverseOnto s.past us).1
  nodup := by simpa only [List.reverse_nil, List.nil_append, reverseOnto_value, Machine.done] using List.perm_middle.nodup (by simpa [ht, Machine.done] using s.nodup)
  complete := by intro a; simpa [ht, Machine.done, List.mem_append, or_assoc, or_left_comm] using s.complete a
  ordered := by rw [scannedRelabel_eq _ _ _ hr]; simpa [Machine.done] using ordered_relabel s u us ht hr hp
  quiet := by simp
  cursor := Function.update s.cursor u univ.toList
  cursor_bound := by intro a; by_cases ha : a = u <;> simp [Function.update, ha, s.cursor_bound]
  skipped := by rw [scannedRelabel_eq _ _ _ hr]; exact cursor_relabel s.φ s.h s.cursor s.skipped u hr hp

theorem credit_relabel (s : Machine G) (u : V) (us : List V)
    (ht : s.todo = u :: us) (hu : s.φ.isOverflowing u)
    (hr : ∃ v, s.φ.residualEdge u v)
    (hp : ∀ v, s.φ.residualEdge u v → s.h u ≤ s.h v) :
    credit (relabelCurrent s u us ht hu hr hp) ≤ credit s + 2 * Fintype.card V := by
  have hl := List.Nodup.length_le_card s.nodup
  rw [ht] at hl
  have hsum := Finset.sum_erase_add (univ : Finset V) (fun a => (s.cursor a).length) (mem_univ u)
  have hfun : (fun a => ((relabelCurrent s u us ht hu hr hp).cursor a).length) =
      Function.update (fun a => (s.cursor a).length) u (Fintype.card V) := by
    funext a; by_cases ha : a = u <;> simp [relabelCurrent, Function.update, ha]
  unfold credit
  rw [hfun, Finset.sum_update_of_mem (mem_univ u), Finset.sdiff_singleton_eq_erase]
  simp only [relabelCurrent, ht, List.length_cons, reverseOnto_value, List.length_append] at *
  omega

def pushCells (f : V → V → ℝ) (u v : V) (δ : ℝ) : V → V → ℝ :=
  Function.update (Function.update f u (Function.update (f u) v (f u v + δ)))
    v (Function.update (f v) u (f v u - δ))

theorem pushCells_eq (f : V → V → ℝ) (u v : V) (huv : u ≠ v) (δ : ℝ) :
    pushCells f u v δ = fun a b => f a b + Flow.edgeDelta δ u v a b := by
  funext a b
  by_cases hau : a = u <;> by_cases hav : a = v <;>
    by_cases hbu : b = u <;> by_cases hbv : b = v <;>
    simp_all [pushCells, Function.update, Flow.edgeDelta] <;> ring

theorem preflow_ext {φ ψ : Preflow V G} (h : φ.f = ψ.f) : φ = ψ := by
  cases φ; cases ψ; cases h; rfl

noncomputable def cachedPush (s : Machine G) (u v : V) (hu : u ≠ G.s)
    (hr : s.φ.residualEdge u v) : Preflow V G := by
  let δ := min (s.excessCache u) (s.φ.residualCapacity u v)
  let φ' := pushBy s.φ u v (residualEdge_ne s.φ hr) δ
    (by dsimp [δ]; rw [s.cache_correct u hu]; exact le_min (s.φ.hexcess_nonneg u hu) hr.le)
    (by dsimp [δ]; rw [s.cache_correct u hu]; exact min_le_left _ _)
    (by dsimp [δ]; exact min_le_right _ _)
  let f' := pushCells s.φ.f u v δ
  have hf : f' = φ'.f := pushCells_eq s.φ.f u v (residualEdge_ne s.φ hr) δ
  exact { f := f'
          hcapacity := by rw [hf]; exact φ'.hcapacity
          hskew_symm := by rw [hf]; exact φ'.hskew_symm
          hexcess_nonneg := by rw [hf]; exact φ'.hexcess_nonneg }

@[simp] theorem cachedPush_eq (s : Machine G) (u v : V) (hu : u ≠ G.s)
    (hr : s.φ.residualEdge u v) : cachedPush s u v hu hr = push s.φ u v hu hr := by
  apply preflow_ext
  simp [cachedPush, push, pushBy, pushCells_eq _ _ _ (residualEdge_ne s.φ hr), s.cache_correct u hu]

noncomputable def pushedCache (s : Machine G) (u v : V) : V → ℝ :=
  let δ := min (s.excessCache u) (s.φ.residualCapacity u v)
  Function.update (Function.update s.excessCache u (s.excessCache u - δ)) v (s.excessCache v + δ)

theorem pushedCache_correct (s : Machine G) (u v : V) (hu : u ≠ G.s)
    (hr : s.φ.residualEdge u v) (a : V) (has : a ≠ G.s) :
    pushedCache s u v a = (cachedPush s u v hu hr).excess a := by
  rw [cachedPush_eq, push_excess]
  have huv := residualEdge_ne s.φ hr
  by_cases hau : a = u <;> by_cases hav : a = v <;>
    simp_all [pushedCache, Function.update, s.cache_correct]

noncomputable def pushCurrent (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) : Machine G := by
  let φ' := cachedPush s u v hu.1 hr
  have hvalid : IsValidHeight φ' s.h := by simpa [φ'] using push_valid s.φ s.h s.valid u v hu hr ha
  have hord : Ordered φ' s.h (s.done ++ s.todo) := by simpa [φ'] using ordered_push s u v hu hr ha
  have hquiet : ∀ a ∈ s.done, ¬ φ'.isOverflowing a := by simpa [φ'] using push_quiet_done s ht v hu hr ha
  have hskip : CursorInvariant φ' s.h s.cursor := by simpa [φ'] using cursor_push s.φ s.h s.cursor s.skipped u v hu hr ha
  exact if hnCache : s.excessCache u < s.φ.residualCapacity u v then
    let hn : s.φ.excess u < s.φ.residualCapacity u v := by simpa [s.cache_correct u hu.1] using hnCache
    { φ := φ', h := s.h, valid := hvalid
      excessCache := pushedCache s u v
      cache_correct := pushedCache_correct s u v hu.1 hr
      past := u :: s.past, todo := us
      nodup := by simpa [ht, Machine.done, List.reverse_cons, List.append_assoc] using s.nodup
      complete := by intro a; simpa [ht, Machine.done, List.reverse_cons, List.append_assoc] using s.complete a
      ordered := by simpa [ht, Machine.done, List.reverse_cons, List.append_assoc] using hord
      quiet := by
        intro a hm
        simp only [List.reverse_cons] at hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hquiet a hm
        · have hau : a = u := List.mem_singleton.mp hm
          subst a
          intro hover
          have hex : φ'.excess u = 0 := by
            dsimp [φ']
            rw [cachedPush_eq, push_excess]
            simp [residualEdge_ne s.φ hr, min_eq_left hn.le]
          have hx := hover.2.2
          rw [hex] at hx
          linarith
      cursor := s.cursor, cursor_bound := s.cursor_bound, skipped := hskip }
    else
    { φ := φ', h := s.h, valid := hvalid
      excessCache := pushedCache s u v
      cache_correct := pushedCache_correct s u v hu.1 hr
      past := s.past, todo := s.todo, nodup := s.nodup, complete := s.complete,
      ordered := hord, quiet := hquiet
      cursor := s.cursor, cursor_bound := s.cursor_bound, skipped := hskip }

theorem pushCurrent_φ (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) :
    (pushCurrent s u us ht v hu hr ha).φ = push s.φ u v hu.1 hr := by
  by_cases hn : s.φ.excess u < s.φ.residualCapacity u v <;> simp [pushCurrent, s.cache_correct u hu.1, hn]

theorem pushCurrent_h (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) : (pushCurrent s u us ht v hu hr ha).h = s.h := by
  by_cases hn : s.φ.excess u < s.φ.residualCapacity u v <;> simp [pushCurrent, s.cache_correct u hu.1, hn]

theorem pushCurrent_done_mono (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) :
    ∀ a ∈ s.done, a ∈ (pushCurrent s u us ht v hu hr ha).done := by
  by_cases hn : s.φ.excess u < s.φ.residualCapacity u v <;> intro a hm
  all_goals simp only [Machine.done, List.mem_reverse] at hm
  all_goals simp [pushCurrent, s.cache_correct u hu.1, hn, Machine.done, hm]

theorem pushCurrent_nonsat_done (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) (hn : s.φ.excess u < s.φ.residualCapacity u v) :
    u ∈ (pushCurrent s u us ht v hu hr ha).done := by simp [pushCurrent, s.cache_correct u hu.1, hn, Machine.done]

theorem credit_push (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) :
    credit (pushCurrent s u us ht v hu hr ha) ≤ credit s := by
  by_cases hn : s.φ.excess u < s.φ.residualCapacity u v <;> simp [pushCurrent, s.cache_correct u hu.1, hn, credit, ht]


/-- One executed basic operation, including its preceding cursor/list scans. -/
structure BasicResult (s : Machine G) where
  op : BasicOp V G
  after : Machine G
  beforeφ : op.beforeφ = s.φ
  beforeh : op.beforeh = s.h
  resultφ : op.resultφ = after.φ
  resulth : op.resulth = after.h
  scans : Nat
  moves : Nat
  minimumVisits : Nat
  minimumVisits_eq : minimumVisits = Fintype.card V * (if op.isRelabel then 1 else 0)
  scan_credit : scans + credit after ≤ credit s + 2 * Fintype.card V * (if op.isRelabel then 1 else 0)
  move_bound : moves ≤ 2 * Fintype.card V * (if op.isRelabel then 1 else 0)
  done_mono : op.isRelabel = false → ∀ a ∈ s.done, a ∈ after.done
  nonsat_done : op.isNonsaturatingPush = true → op.opVertex ∈ after.done
  source_fresh : op.opVertex ∉ s.done

noncomputable def relabelResult (s : Machine G) (u : V) (us : List V)
    (ht : s.todo = u :: us) (hu : s.φ.isOverflowing u)
    (hr : ∃ v, s.φ.residualEdge u v)
    (hp : ∀ v, s.φ.residualEdge u v → s.h u ≤ s.h v) : BasicResult s where
  op := .relabel s.φ s.h u hu hr hp
  after := relabelCurrent s u us ht hu hr hp
  beforeφ := rfl
  beforeh := rfl
  resultφ := rfl
  resulth := (scannedRelabel_eq _ _ _ hr).symm
  scans := 0
  moves := (reverseOnto s.past us).2
  minimumVisits := (scanMinimum s.φ s.h u univ.toList).2
  minimumVisits_eq := by simp [BasicOp.isRelabel]
  scan_credit := by simpa [BasicOp.isRelabel] using credit_relabel s u us ht hu hr hp
  move_bound := by
    have hl := List.Nodup.length_le_card s.nodup
    simp only [List.length_append, List.length_reverse] at hl
    simp only [BasicOp.isRelabel, ↓reduceIte, Nat.mul_one, reverseOnto_count]
    omega
  done_mono := by simp [BasicOp.isRelabel]
  nonsat_done := by simp [BasicOp.isNonsaturatingPush]
  source_fresh := current_not_done s ht

noncomputable def pushResult (s : Machine G) (u : V) (us : List V) (ht : s.todo = u :: us)
    (v : V) (hu : s.φ.isOverflowing u) (hr : s.φ.residualEdge u v)
    (ha : s.h u = s.h v + 1) : BasicResult s where
  op := .push s.φ s.h u v hu hr ha
  after := pushCurrent s u us ht v hu hr ha
  beforeφ := rfl
  beforeh := rfl
  resultφ := (pushCurrent_φ s u us ht v hu hr ha).symm
  resulth := (pushCurrent_h s u us ht v hu hr ha).symm
  scans := 0
  moves := 0
  minimumVisits := 0
  minimumVisits_eq := by simp [BasicOp.isRelabel]
  scan_credit := by simpa [BasicOp.isRelabel] using credit_push s u us ht v hu hr ha
  move_bound := by simp
  done_mono := by intro _; exact pushCurrent_done_mono s u us ht v hu hr ha
  nonsat_done := by
    intro hn
    have hn' : s.φ.excess u < s.φ.residualCapacity u v := by
      simpa [BasicOp.isNonsaturatingPush] using hn
    exact pushCurrent_nonsat_done s u us ht v hu hr ha hn'
  source_fresh := current_not_done s ht

/-- Pull a result back across one actual administrative cursor/list step. -/
noncomputable def BasicResult.prependScan {s t : Machine G}
    (hp : t.φ = s.φ) (hh : t.h = s.h)
    (hd : ∀ a ∈ s.done, a ∈ t.done) (hc : credit t + 1 = credit s)
    (r : BasicResult t) : BasicResult s where
  op := r.op
  after := r.after
  beforeφ := r.beforeφ.trans hp
  beforeh := r.beforeh.trans hh
  resultφ := r.resultφ
  resulth := r.resulth
  scans := r.scans + 1
  moves := r.moves
  minimumVisits := r.minimumVisits
  minimumVisits_eq := r.minimumVisits_eq
  scan_credit := by have h := r.scan_credit; omega
  move_bound := r.move_bound
  done_mono := by intro hn a ha; exact r.done_mono hn a (hd a ha)
  nonsat_done := r.nonsat_done
  source_fresh := by intro hs; exact r.source_fresh (hd _ hs)

structure Finished (s : Machine G) where
  quiet : ∀ u, ¬ s.φ.isOverflowing u
  scans : Nat
  scan_bound : scans ≤ credit s

noncomputable def Finished.prependScan {s t : Machine G}
    (hp : t.φ = s.φ) (hc : credit t + 1 = credit s) (r : Finished t) : Finished s where
  quiet := by rw [← hp]; exact r.quiet
  scans := r.scans + 1
  scan_bound := by have h := r.scan_bound; omega

abbrev Next (s : Machine G) := Finished s ⊕ BasicResult s

/-- Scan current neighbors and inactive list entries until a basic operation
or a completed flow is reached. Administrative steps strictly consume credit. -/
noncomputable def next (s : Machine G) : Next s :=
  match ht : s.todo with
  | [] => .inl
      { quiet := by
          intro u hu
          have hm : u ∈ s.done ++ s.todo := (s.complete u).2 ⟨hu.1, hu.2.1⟩
          have hd : u ∈ s.done := by simpa [ht] using hm
          exact s.quiet u hd hu
        scans := 0
        scan_bound := Nat.zero_le _ }
  | u :: us =>
      if huCache : 0 < s.excessCache u then
        let hu : s.φ.isOverflowing u := ⟨(current_internal s ht).1, (current_internal s ht).2, by
          simpa [s.cache_correct u (current_internal s ht).1] using huCache⟩
        match hc : s.cursor u with
        | [] =>
            let hr := exists_residualEdge_of_overflowing s.φ u hu.1 hu.2.2
            let hp : ∀ v, s.φ.residualEdge u v → s.h u ≤ s.h v :=
              fun v hv => s.skipped u v (by simp [hc]) hv
            .inr (relabelResult s u us ht hu hr hp)
        | v :: vs =>
            if ha : admissibleEdge s.φ s.h u v then
              .inr (pushResult s u us ht v hu ha.1 ha.2)
            else
              let t := advanceCursor s u v vs hc ha
              match next t with
              | .inl r => .inl (r.prependScan (s := s) (t := t) rfl (credit_advanceCursor s u v vs hc ha))
              | .inr r => .inr (r.prependScan (s := s) (t := t) rfl rfl (fun _ hx => hx)
                  (credit_advanceCursor s u v vs hc ha))
      else
        let hu : ¬ s.φ.isOverflowing u := by
          intro hover; exact huCache (by simpa [s.cache_correct u hover.1] using hover.2.2)
        let t := skipCurrent s u us ht hu
        match next t with
        | .inl r => .inl (r.prependScan (s := s) (t := t) rfl (credit_skip s u us ht hu))
        | .inr r => .inr (r.prependScan (s := s) (t := t) rfl rfl
            (by intro a ha; simpa [Machine.done, t, skipCurrent, or_comm] using List.mem_cons_of_mem u (by simpa [Machine.done] using ha))
            (credit_skip s u us ht hu))
termination_by credit s
 decreasing_by
  · have h := credit_advanceCursor s u v vs hc ha
    omega
  · have h := credit_skip s u us ht hu
    omega


inductive Trace : Machine G → Machine G → Nat → Type _
  | nil (s : Machine G) : Trace s s 0
  | cons {s t : Machine G} {n : Nat} (r : BasicResult s)
      (tail : Trace r.after t n) : Trace s t (n + 1)

namespace Trace

noncomputable def state {s t : Machine G} {n : Nat} (tr : Trace s t n) : Nat → Machine G :=
  match tr with
  | .nil s => fun _ => s
  | .cons r tail => fun i => match i with | 0 => s | k + 1 => tail.state k

@[simp] theorem state_zero {s t : Machine G} {n : Nat} (tr : Trace s t n) : tr.state 0 = s := by
  cases tr <;> rfl

@[simp] theorem state_end {s t : Machine G} {n : Nat} (tr : Trace s t n) : tr.state n = t := by
  induction tr with
  | nil => rfl
  | cons r tail ih => exact ih

noncomputable def result {s t : Machine G} {n : Nat} (tr : Trace s t n)
    (i : Nat) (hi : i < n) : BasicResult (tr.state i) :=
  match tr with
  | .nil _ => False.elim (by omega)
  | .cons r tail => match i with
      | 0 => r
      | k + 1 => tail.result k (by omega)

@[simp] theorem result_after {s t : Machine G} {n : Nat} (tr : Trace s t n)
    (i : Nat) (hi : i < n) : (tr.result i hi).after = tr.state (i + 1) := by
  induction tr generalizing i with
  | nil => omega
  | cons r tail ih =>
      cases i with
      | zero => simp [result, state]
      | succ k => exact ih k (by omega)

noncomputable def toRun {s t : Machine G} {n : Nat} (tr : Trace s t n) : Run V G n where
  φ i := (tr.state i).φ
  h i := (tr.state i).h
  hvalid i := (tr.state i).valid
  op i hi := (tr.result i hi).op
  hop_beforeφ i hi := (tr.result i hi).beforeφ
  hop_beforeh i hi := (tr.result i hi).beforeh
  hop_resultφ i hi := by rw [(tr.result i hi).resultφ, result_after]
  hop_resulth i hi := by rw [(tr.result i hi).resulth, result_after]

theorem done_mono_interval {s t : Machine G} {n : Nat} (tr : Trace s t n)
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ n)
    (hn : ∀ k (hk : k < n), i ≤ k → k < j → (tr.result k hk).op.isRelabel = false) :
    ∀ a ∈ (tr.state i).done, a ∈ (tr.state j).done := by
  induction j with
  | zero =>
      have heq : i = 0 := by omega
      subst i
      exact fun _ h => h
  | succ j ih =>
      by_cases heq : i = j + 1
      · subst i; exact fun _ h => h
      · have hjn : j < n := by omega
        have hmid := ih (by omega) (by omega) (by
          intro k hk hik hkj; exact hn k hk hik (by omega))
        intro a ha
        have h := (tr.result j hjn).done_mono (hn j hjn (by omega) (by omega)) a (hmid a ha)
        simpa using h

noncomputable def toRelabelToFrontRun {s t : Machine G} {n : Nat}
    (tr : Trace s t n) : RelabelToFrontRun V G n where
  run := tr.toRun
  discharge_discipline := by
    intro i j hi hj hij hni _ hnone heq
    have hm := (tr.result i hi).nonsat_done hni
    rw [result_after] at hm
    have hmono := tr.done_mono_interval (i := i + 1) (j := j) (by omega) (by omega)
      (by intro k hk hik hkj; exact hnone k hk (by omega) hkj)
    have hin := hmono _ hm
    have heq' : (tr.result i hi).op.opVertex = (tr.result j hj).op.opVertex := heq
    rw [heq'] at hin
    exact (tr.result j hj).source_fresh hin

theorem length_bound {s t : Machine G} {n : Nat} (tr : Trace s t n) :
    n ≤ 9 * Fintype.card V * Fintype.card V * Fintype.card V :=
  tr.toRelabelToFrontRun.step_count_bound_V3

noncomputable def scans {s t : Machine G} {n : Nat} : Trace s t n → Nat
  | .nil _ => 0
  | .cons r tail => r.scans + tail.scans

noncomputable def moves {s t : Machine G} {n : Nat} : Trace s t n → Nat
  | .nil _ => 0
  | .cons r tail => r.moves + tail.moves

noncomputable def relabels {s t : Machine G} {n : Nat} : Trace s t n → Nat
  | .nil _ => 0
  | .cons r tail => (if r.op.isRelabel then 1 else 0) + tail.relabels

theorem relabels_eq {s t : Machine G} {n : Nat} (tr : Trace s t n) :
    tr.relabels = tr.toRun.numRelabels := by
  induction tr with
  | nil => simp [relabels, Run.numRelabels]
  | cons r tail ih =>
      simp only [relabels, Run.numRelabels, Fin.sum_univ_succ, Run.opFin, toRun, result]
      congr 1

theorem scans_credit {s t : Machine G} {n : Nat} (tr : Trace s t n) :
    tr.scans + credit t ≤ credit s + 2 * Fintype.card V * tr.relabels := by
  induction tr with
  | nil => simp [scans, relabels]
  | cons r tail ih =>
      have h := r.scan_credit
      simp only [scans, relabels, Nat.mul_add]
      omega

theorem moves_bound {s t : Machine G} {n : Nat} (tr : Trace s t n) :
    tr.moves ≤ 2 * Fintype.card V * tr.relabels := by
  induction tr with
  | nil => simp [moves, relabels]
  | cons r tail ih =>
      have h := r.move_bound
      simp only [moves, relabels, Nat.mul_add]
      omega

noncomputable def minimumVisits {s t : Machine G} {n : Nat} : Trace s t n → Nat
  | .nil _ => 0
  | .cons r tail => r.minimumVisits + tail.minimumVisits

theorem minimumVisits_eq {s t : Machine G} {n : Nat} (tr : Trace s t n) :
    tr.minimumVisits = Fintype.card V * tr.relabels := by
  induction tr with
  | nil => simp [minimumVisits, relabels]
  | cons r tail ih => simp [minimumVisits, relabels, r.minimumVisits_eq, ih, Nat.mul_add]

end Trace


structure Execution (s : Machine G) (fuel : Nat) where
  last : Machine G
  steps : Nat
  trace : Trace s last steps
  terminal : Option (Finished last)
  exhausted : terminal = none → steps = fuel

noncomputable def execute (s : Machine G) : (fuel : Nat) → Execution s fuel
  | 0 => ⟨s, 0, .nil s, none, fun _ => rfl⟩
  | fuel + 1 => match next s with
      | .inl fin => ⟨s, 0, .nil s, some fin, by simp⟩
      | .inr r =>
          let tail := execute r.after fuel
          { last := tail.last
            steps := tail.steps + 1
            trace := .cons r tail.trace
            terminal := tail.terminal
            exhausted := by intro hn; rw [tail.exhausted hn] }

def budget (V : Type*) [Fintype V] := 9 * Fintype.card V * Fintype.card V * Fintype.card V + 1

theorem execute_terminal (s : Machine G) : (execute s (budget V)).terminal ≠ none := by
  intro hn
  have h := (execute s (budget V)).trace.length_bound
  rw [(execute s (budget V)).exhausted hn] at h
  simp only [budget] at h
  omega

noncomputable def completed (s : Machine G) : Finished (execute s (budget V)).last :=
  (execute s (budget V)).terminal.get (Option.isSome_iff_ne_none.mpr (execute_terminal s))

theorem completed_excess_zero (s : Machine G) (u : V) (hs : u ≠ G.s) (ht : u ≠ G.t) :
    (execute s (budget V)).last.φ.excess u = 0 := by
  have h := (completed s).quiet u
  have hnonneg := (execute s (budget V)).last.φ.hexcess_nonneg u hs
  by_contra hn
  exact h ⟨hs, ht, lt_of_le_of_ne hnonneg (Ne.symm hn)⟩

noncomputable def maximumFlow (s : Machine G) : Flow V G :=
  (execute s (budget V)).last.φ.toFlow (completed_excess_zero s)

theorem maximumFlow_isMaximal (s : Machine G) : (maximumFlow s).isMaximal :=
  maximal_of_no_overflow _ _ (execute s (budget V)).last.valid (completed_excess_zero s)

noncomputable def initializedFlow (G : FlowNetwork V) : Flow V G := maximumFlow (initialMachine G)

theorem initialized_maximum_flow (G : FlowNetwork V) : (initializedFlow G).isMaximal :=
  maximumFlow_isMaximal _

/-- Actual cursor advances/inactive-entry scans, plus terminal scans, list traversal
on move-to-front, and a full vertex scan for each relabel. Pushes contribute one
basic-operation unit. The scalar/indexed implementation expands these units below. -/
noncomputable def controllerWork (s : Machine G) : Nat :=
  let r := execute s (budget V)
  r.steps + r.trace.scans + (completed s).scans + r.trace.moves +
    r.trace.minimumVisits

theorem controllerWork_bound (s : Machine G) :
    controllerWork s ≤ 19 * Fintype.card V * Fintype.card V * Fintype.card V + credit s := by
  let r := execute s (budget V)
  have hn := r.trace.length_bound
  have hscan := r.trace.scans_credit
  have hfin := (completed s).scan_bound
  have hmove := r.trace.moves_bound
  have hrel : r.trace.relabels ≤ 2 * Fintype.card V * Fintype.card V := by
    rw [Trace.relabels_eq]; exact r.trace.toRun.relabel_count_bound
  change r.steps + r.trace.scans + (completed s).scans + r.trace.moves +
    r.trace.minimumVisits ≤ _
  rw [Trace.minimumVisits_eq]
  change (completed s).scans ≤ credit r.last at hfin
  nlinarith

theorem initialized_controllerWork_le (G : FlowNetwork V) :
    controllerWork (initialMachine G) ≤ 21 * Fintype.card V * Fintype.card V * Fintype.card V := by
  have h := controllerWork_bound (initialMachine G)
  have hc := credit_initial G
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.s⟩
  have h1 : Fintype.card V ≤ Fintype.card V * Fintype.card V := Nat.le_mul_self _
  have h2 : Fintype.card V * Fintype.card V ≤ Fintype.card V * Fintype.card V * Fintype.card V :=
    Nat.le_mul_of_pos_right _ hp
  nlinarith


/-- The initialization's actual cell writes and internal-list candidate visits. -/
noncomputable def initializationWork (G : FlowNetwork V) : Nat :=
  (initialCells G).2 + (tabulate (initialHeight G) 0).2 + (tabulate (G.c G.s) 0).2 +
    (tabulate (fun _ : V => (univ.toList : List V)) []).2 + (selectInternal G univ.toList).2

@[simp] theorem initializationWork_eq (G : FlowNetwork V) :
    initializationWork G = Fintype.card V * Fintype.card V + 4 * Fintype.card V := by
  simp [initializationWork, initialCells, Fintype.card_prod]
  omega

/-- Scalar/indexed RAM charge: a fixed allowance of 32 primitive operations per
cursor/list test, push/relabel dispatch, moved list cell, or minimum-scan cell.
Indexed table lookup/update and exact real arithmetic are unit primitives.
This is not a bound on persistent-function evaluation or machine bit complexity. -/
noncomputable def Trace.work {s t : Machine G} {n : Nat} : Trace s t n → Nat
  | .nil _ => 0
  | .cons r tail => 32 * (1 + r.scans + r.moves + r.minimumVisits) + tail.work

theorem Trace.work_eq {s t : Machine G} {n : Nat} (tr : Trace s t n) :
    tr.work = 32 * (n + tr.scans + tr.moves + tr.minimumVisits) := by
  induction tr with
  | nil => simp [work, scans, moves, minimumVisits]
  | cons r tail ih => simp only [work, scans, moves, minimumVisits, ih]; omega

/-- The returned measured construction-and-run charge. The last summand includes
the actual scans that discover termination and its final empty-list test. -/
noncomputable def initializedWork (G : FlowNetwork V) : Nat :=
  32 * initializationWork G + (execute (initialMachine G) (budget V)).trace.work +
    32 * ((completed (initialMachine G)).scans + 1)

theorem initializedWork_eq (G : FlowNetwork V) : initializedWork G =
    32 * (initializationWork G + controllerWork (initialMachine G) + 1) := by
  unfold initializedWork controllerWork
  rw [Trace.work_eq]
  dsimp only
  omega

theorem initialized_work_le_cubic (G : FlowNetwork V) :
    initializedWork G ≤ 864 * Fintype.card V * Fintype.card V * Fintype.card V := by
  rw [initializedWork_eq, initializationWork_eq]
  have h := initialized_controllerWork_le G
  have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.s⟩
  have h1 : Fintype.card V ≤ Fintype.card V * Fintype.card V := Nat.le_mul_self _
  have h2 : Fintype.card V * Fintype.card V ≤ Fintype.card V * Fintype.card V * Fintype.card V :=
    Nat.le_mul_of_pos_right _ hp
  nlinarith

/-- One concrete initialized run supplies both maximum flow and the cubic charge. -/
theorem initialized_correct_and_cost (G : FlowNetwork V) :
    (initializedFlow G).isMaximal ∧
      initializedWork G ≤ 864 * Fintype.card V * Fintype.card V * Fintype.card V :=
  ⟨initialized_maximum_flow G, initialized_work_le_cubic G⟩

end CLRS.Chapter26.RelabelExecution
