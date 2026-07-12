import Mathlib.Tactic
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import CLRSLean.Chapter_16.Section_16_4_Matroids

/-!
# A task-scheduling problem as a matroid

This section formalizes CLRS §16.5: the task-scheduling problem as a
matroid.  We consider `n` unit-time tasks, each with an integer deadline
`d_i` and a nonnegative penalty `w_i` incurred if the task finishes after
its deadline.  The goal is to find a schedule that minimizes the total
penalty of late tasks.

The key insight (CLRS Theorem 16.13) is that the family of task sets that
admit a schedule with **no late task** forms a matroid — the
*task-scheduling matroid*.  Minimizing the total penalty of late tasks is
then equivalent to finding a maximum-weight independent set in this
matroid, which is solved by the general greedy algorithm of §16.4
({name}`CLRS.Matroid16.greedyRun_optimal`).

Main results:

- `scheduleIndependent`: a set of tasks is *independent* iff `N_t(A) ≤ t`
  for all `t`, where `N_t(A)` counts the tasks in `A` whose deadline is at
  most `t` (CLRS Lemma 16.12).
- `schedulingMatroid`: the `Matroid (Fin n)` whose independent sets are
  exactly the on-time-schedulable task sets (CLRS Theorem 16.13).
- `minPenaltySchedule_correct`: applying `greedyRun` with penalty weights
  to the scheduling matroid yields a minimum-penalty independent set, so
  the optimal schedule puts exactly those tasks on time.

Notation conventions:

- `tasks : Fin n → Task`, indexed by `Fin n`, each with `.deadline` and `.penalty`.
- `Nt tasks A t` = number of tasks `i ∈ A` with `(tasks i).deadline ≤ t`.
- `A`, `C` : `Finset (Fin n)` (sets of task indices).
- The scheduling matroid's independent sets are the `scheduleIndependent` sets.
-/
namespace CLRS.SchedulingMatroid

open Set
open Matroid
open Finset

set_option linter.unusedSectionVars false

/-! ## Task model -/

/-- A unit-time task with an integer deadline and a nonnegative penalty
weight (CLRS §16.5). -/
structure Task where
  /-- The deadline of the task.  (CLRS uses 1-indexed deadlines, but 0
  is harmless — any task with deadline 0 is a matroid loop.) -/
  deadline : ℕ
  /-- The penalty incurred if the task finishes after its deadline. -/
  penalty : ℕ

/-! ## The `N_t` function and independence (Lemma 16.12) -/

/-- `Nt tasks A t` is the number of tasks `i ∈ A` whose deadline is ≤ `t`
(CLRS equation (16.16)). -/
def Nt {n : ℕ} (tasks : Fin n → Task) (A : Finset (Fin n)) (t : ℕ) : ℕ :=
  (A.filter fun i => (tasks i).deadline ≤ t).card

lemma Nt_mono {n : ℕ} (tasks : Fin n → Task) (A : Finset (Fin n)) {t₁ t₂ : ℕ}
    (h : t₁ ≤ t₂) : Nt tasks A t₁ ≤ Nt tasks A t₂ := by
  unfold Nt
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  omega

lemma Nt_le_card {n : ℕ} (tasks : Fin n → Task) (A : Finset (Fin n)) (t : ℕ) :
    Nt tasks A t ≤ A.card := by
  unfold Nt
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma Nt_empty {n : ℕ} (tasks : Fin n → Task) (t : ℕ) : Nt tasks ∅ t = 0 := by
  simp [Nt]

/-- `Nt` after inserting a new element `e ∉ A`.  (If `e ∉ A`, inserting `e`
adds 1 to the count precisely when `deadline(e) ≤ t`.) -/
lemma Nt_insert {n : ℕ} (tasks : Fin n → Task) (A : Finset (Fin n)) (e : Fin n) (heA : e ∉ A)
    (t : ℕ) : Nt tasks (insert e A) t = Nt tasks A t + (if (tasks e).deadline ≤ t then 1 else 0) := by
  unfold Nt
  rw [Finset.filter_insert]
  by_cases h : (tasks e).deadline ≤ t
  · simp [h, heA]
  · simp [h]

lemma Nt_subset {n : ℕ} (tasks : Fin n → Task) {A B : Finset (Fin n)} (hAB : A ⊆ B) (t : ℕ) :
    Nt tasks A t ≤ Nt tasks B t := by
  unfold Nt
  apply Finset.card_le_card
  exact Finset.filter_subset_filter (fun i => (tasks i).deadline ≤ t) hAB

/-- If all tasks in `X` have deadline ≤ `t`, then `Nt` counts all of them. -/
lemma Nt_eq_card_of_deadline_le {n : ℕ} (tasks : Fin n → Task) {X : Finset (Fin n)} {t : ℕ}
    (h : ∀ i ∈ X, (tasks i).deadline ≤ t) : Nt tasks X t = X.card := by
  unfold Nt
  have : (X.filter fun i => (tasks i).deadline ≤ t) = X := by
    ext i; simp; intro hi; exact h i hi
  rw [this]

/-- For disjoint `X` and `Y`, `Nt` is additive. -/
lemma Nt_disjoint_union {n : ℕ} (tasks : Fin n → Task) {X Y : Finset (Fin n)}
    (hdisj : Disjoint X Y) (t : ℕ) : Nt tasks (X ∪ Y) t = Nt tasks X t + Nt tasks Y t := by
  classical
    unfold Nt
    have hfilter_disj : Disjoint (X.filter fun i => (tasks i).deadline ≤ t)
        (Y.filter fun i => (tasks i).deadline ≤ t) :=
      Finset.disjoint_filter_filter hdisj
    rw [Finset.filter_union, Finset.card_union_of_disjoint hfilter_disj]

/-- Decompose `Nt` over a set `C` by intersecting with `A`. -/
lemma Nt_decompose_eq {n : ℕ} (tasks : Fin n → Task) (A C : Finset (Fin n)) (t : ℕ) :
    Nt tasks C t = Nt tasks (A ∩ C) t + Nt tasks (C \ A) t := by
  have h_disjoint : Disjoint (A ∩ C) (C \ A) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hne
    have hne_nonempty : ((A ∩ C) ∩ (C \ A)).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨i, hi⟩ := hne_nonempty
    rcases Finset.mem_inter.mp hi with ⟨hiAC, hiCA⟩
    rcases Finset.mem_inter.mp hiAC with ⟨hiA, hiC⟩
    rcases Finset.mem_sdiff.mp hiCA with ⟨hiC', hiA'⟩
    exact hiA' hiA
  have h_union : (A ∩ C) ∪ (C \ A) = C := by
    ext i; constructor
    · intro hi
      rw [Finset.mem_union] at hi
      rcases hi with (hiAC | hiCA)
      · exact (Finset.mem_inter.mp hiAC).2
      · exact (Finset.mem_sdiff.mp hiCA).1
    · intro hiC
      by_cases hiA : i ∈ A
      · apply Finset.mem_union.mpr; left; exact Finset.mem_inter.mpr ⟨hiA, hiC⟩
      · apply Finset.mem_union.mpr; right; exact Finset.mem_sdiff.mpr ⟨hiC, hiA⟩
  calc
    Nt tasks C t = Nt tasks ((A ∩ C) ∪ (C \ A)) t := by rw [h_union]
    _ = Nt tasks (A ∩ C) t + Nt tasks (C \ A) t := Nt_disjoint_union tasks h_disjoint t

/-- Symmetric version: `Nt A t = Nt (A ∩ C) t + Nt (A \ C) t`. -/
lemma Nt_decompose_symm {n : ℕ} (tasks : Fin n → Task) (A C : Finset (Fin n)) (t : ℕ) :
    Nt tasks A t = Nt tasks (A ∩ C) t + Nt tasks (A \ C) t := by
  have h_disjoint : Disjoint (A ∩ C) (A \ C) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    by_contra hne
    have hne_nonempty : ((A ∩ C) ∩ (A \ C)).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨i, hi⟩ := hne_nonempty
    rcases Finset.mem_inter.mp hi with ⟨hiAC, hiAC'⟩
    rcases Finset.mem_inter.mp hiAC with ⟨hiA, hiC⟩
    rcases Finset.mem_sdiff.mp hiAC' with ⟨hiA', hiC'⟩
    exact hiC' hiC
  have h_union : (A ∩ C) ∪ (A \ C) = A := by
    ext i; constructor
    · intro hi
      rw [Finset.mem_union] at hi
      rcases hi with (hiAC | hiAC')
      · exact (Finset.mem_inter.mp hiAC).1
      · exact (Finset.mem_sdiff.mp hiAC').1
    · intro hiA
      by_cases hiC : i ∈ C
      · apply Finset.mem_union.mpr; left; exact Finset.mem_inter.mpr ⟨hiA, hiC⟩
      · apply Finset.mem_union.mpr; right; exact Finset.mem_sdiff.mpr ⟨hiA, hiC⟩
  calc
    Nt tasks A t = Nt tasks ((A ∩ C) ∪ (A \ C)) t := by rw [h_union]
    _ = Nt tasks (A ∩ C) t + Nt tasks (A \ C) t := Nt_disjoint_union tasks h_disjoint t

/-- If `A.card < C.card`, then `|A \ C| < |C \ A|`. -/
lemma card_sdiff_lt_card_sdiff_of_card_lt {α : Type*} [DecidableEq α] {A C : Finset α}
    (h : A.card < C.card) : (A \ C).card < (C \ A).card := by
  have hA : A.card = (A \ C).card + (A ∩ C).card := by
    simpa using (Finset.card_sdiff_add_card_inter A C).symm
  have hC : C.card = (C \ A).card + (A ∩ C).card := by
    simpa [Finset.inter_comm] using (Finset.card_sdiff_add_card_inter C A).symm
  omega

/--
**CLRS Lemma 16.12 (independence equivalence).**  A set `A` of tasks admits a
schedule with no late task iff `N_t(A) ≤ t` for all `t`.  We take the latter
as the definition of *independence*.

(CLRS also gives a third equivalent condition: `A` can be ordered by deadline
so that each task finishes by its deadline — the earliest-deadline-first
schedule.)
-/
def scheduleIndependent {n : ℕ} (tasks : Fin n → Task) (A : Finset (Fin n)) : Prop :=
  ∀ t : ℕ, Nt tasks A t ≤ t

lemma scheduleIndependent_empty {n : ℕ} (tasks : Fin n → Task) :
    scheduleIndependent tasks ∅ := by
  intro t; simp [Nt]

lemma scheduleIndependent_subset {n : ℕ} (tasks : Fin n → Task) {A B : Finset (Fin n)}
    (hB : scheduleIndependent tasks B) (hAB : A ⊆ B) : scheduleIndependent tasks A := by
  intro t
  have hNt : Nt tasks A t ≤ Nt tasks B t := Nt_subset tasks hAB t
  have hbound : Nt tasks B t ≤ t := hB t
  omega

/--
**Exchange property for `scheduleIndependent`.**  If `A` and `C` are independent
with `|A| < |C|`, then there exists a task `e ∈ C \ A` such that `A ∪ {e}` is also
independent.  The correct `e` to choose is one whose deadline is **maximal** among
`C \ A`, and the proof works uniformly regardless of whether that deadline exceeds
`|A|` (CLRS Theorem 16.13, exchange axiom).

The proof decomposes the count `Nt` across the disjoint union structure of `A`
and `C`: for `t ≥ deadline(e)`, the additional tasks in `C \ A` outnumber the absent
tasks `A \ C` because `|C| > |A|`.
-/
lemma scheduleIndependent_augmentation {n : ℕ} (tasks : Fin n → Task) {A C : Finset (Fin n)}
    (hA : scheduleIndependent tasks A) (hC : scheduleIndependent tasks C)
    (hcard : A.card < C.card) : ∃ e ∈ C, e ∉ A ∧ scheduleIndependent tasks (insert e A) := by
  have h_nonempty : (C \ A).Nonempty := by
    obtain ⟨e, heC, heA⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨e, Finset.mem_sdiff.mpr ⟨heC, heA⟩⟩
  -- Pick a task in C\A with maximum deadline
  obtain ⟨e, he_sdiff, he_max⟩ :=
    Finset.exists_max_image (C \ A) (fun i => (tasks i).deadline) h_nonempty
  have heC : e ∈ C := (Finset.mem_sdiff.1 he_sdiff).1
  have heA : e ∉ A := (Finset.mem_sdiff.1 he_sdiff).2
  let d := (tasks e).deadline
  have h_all_deadline_le_d : ∀ i ∈ C \ A, (tasks i).deadline ≤ d := he_max
  have h_card_diff : (A \ C).card < (C \ A).card :=
    card_sdiff_lt_card_sdiff_of_card_lt hcard
  refine ⟨e, heC, heA, ?_⟩
  intro t
  by_cases ht : t < d
  · -- t < deadline(e): e is not counted
    rw [Nt_insert tasks A e heA t, if_neg (by omega)]
    exact hA t
  · -- t ≥ deadline(e): e adds 1 to the count
    rw [Nt_insert tasks A e heA t, if_pos (by omega)]
    have hNt_A_C_ineq : Nt tasks A t + 1 ≤ Nt tasks C t := by
      -- Decompose Nt(C) and Nt(A) using the disjoint union structure
      rw [Nt_decompose_eq tasks A C t, Nt_decompose_symm tasks A C t]
      -- For t ≥ d, all tasks in C\A count (they all have deadline ≤ d ≤ t)
      have hNt_sdiff_eq_card : Nt tasks (C \ A) t = (C \ A).card :=
        Nt_eq_card_of_deadline_le tasks (by
          intro i hi
          have hdeadline := h_all_deadline_le_d i hi
          omega)
      -- Subset count bound for A\C
      have hNt_sdiff_le_card : Nt tasks (A \ C) t ≤ (A \ C).card :=
        Nt_le_card tasks (A \ C) t
      -- Chain the inequalities
      calc
        Nt tasks (A ∩ C) t + Nt tasks (A \ C) t + 1
            ≤ Nt tasks (A ∩ C) t + (A \ C).card + 1 := by omega
        _ ≤ Nt tasks (A ∩ C) t + (C \ A).card := by omega
        _ = Nt tasks (A ∩ C) t + Nt tasks (C \ A) t := by rw [hNt_sdiff_eq_card]
    have hC_indep : Nt tasks C t ≤ t := hC t
    omega

/--
The **scheduling matroid** (CLRS Theorem 16.13).  The family of independent
sets defined by `scheduleIndependent` satisfies the matroid axioms.
-/
noncomputable def schedulingMatroid {n : ℕ} (tasks : Fin n → Task) : Matroid (Fin n) :=
  (IndepMatroid.ofFinset (E := Set.univ) (fun A : Finset (Fin n) => scheduleIndependent tasks A)
    (scheduleIndependent_empty tasks)
    (fun I J hJ hIJ => scheduleIndependent_subset tasks hJ hIJ)
    (fun I J hI hJ hcard => scheduleIndependent_augmentation tasks hI hJ hcard)
    (fun I hI => by simp)).matroid

/-- The ground set of the scheduling matroid is all tasks (`Set.univ`). -/
@[simp]
lemma schedulingMatroid_E {n : ℕ} (tasks : Fin n → Task) :
    (schedulingMatroid tasks).E = Set.univ := by
  simp [schedulingMatroid, IndepMatroid.ofFinset_E]

/-- A Finset is independent in the scheduling matroid iff it is scheduleIndependent. -/
@[simp]
lemma schedulingMatroid_indep_finset_iff {n : ℕ} (tasks : Fin n → Task) (A : Finset (Fin n)) :
    (schedulingMatroid tasks).Indep (A : Set (Fin n)) ↔ scheduleIndependent tasks A := by
  simp [schedulingMatroid, IndepMatroid.ofFinset_indep]

/-! ## Optimal schedule via greedy (Theorem 16.13 + §16.4 greedy optimality) -/

-- The `Indep` predicate of the scheduling matroid is decidable classically.
noncomputable instance {n : ℕ} (tasks : Fin n → Task) :
    DecidablePred ((schedulingMatroid tasks).Indep) := by
  classical
    exact inferInstance

/--
**Minimum-penalty schedule (CLRS Theorem 16.13, optimality).**  Let
`schedMatroid` be the scheduling matroid on `tasks`, and let the weight of
each task be its penalty.  Then `greedyRun` returns a maximum-penalty
independent set of on-time tasks; the optimal schedule puts those tasks on
time and incurs the total penalty of the complementary late tasks.
-/
theorem minPenaltySchedule_correct {n : ℕ} (tasks : Fin n → Task)
    (A : Finset (Fin n)) (hA : (schedulingMatroid tasks).Indep (A : Set (Fin n))) :
    Matroid16.gweight (fun i => (tasks i).penalty) A ≤
    Matroid16.gweight (fun i => (tasks i).penalty)
      (Matroid16.greedyRun (schedulingMatroid tasks) (fun i => (tasks i).penalty)) := by
  exact Matroid16.greedyRun_optimal (schedulingMatroid tasks)
    (fun i => (tasks i).penalty) A hA

end CLRS.SchedulingMatroid
