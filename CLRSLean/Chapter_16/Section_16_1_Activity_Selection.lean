import Mathlib

/-!
# CLRS Section 16.1 - Activity selection

This file gives a first Lean model for the activity-selection problem from
CLRS Section 16.1.  Activities are closed-open intervals over natural-number
time points, represented only by their {lit}`start` and {lit}`finish` fields.  A selected
list is feasible when every earlier activity in the list finishes before every
later one starts.

Main results:

- Theorem {lit}`earliest_finish_minFinish`: the executable selector
  {lit}`earliest_finish` returns an activity whose finish time is minimum in the
  input list.
- Theorem {lit}`greedy_choice_minFinish_preserves_optimal_tail_feasibility`: if the
  greedy activity is compatible with an optimal tail solution, prepending it is
  feasible.
- Theorem {lit}`greedy_choice_optimal_from_certificate`: a certificate-based
  optimality theorem for the greedy-choice step.  The exchange argument is
  provided as a hypothesis, keeping the theorem honest while still matching the
  CLRS proof structure.

Current gaps:

- This file does not yet prove the full automated CLRS recursion from a sorted
  activity list.  The remaining work is to derive the exchange certificate from
  a sorted-by-finish interface and connect it to {lit}`greedySelect`.
-/

open List

namespace CLRS
namespace ActivitySelection

/-! ## Activities and feasibility -/

/--
An activity is an interval with a natural-number start time and finish time.
The model intentionally does not require {lit}`start ≤ finish`; that assumption can
be added by clients that want to rule out degenerate input data.
-/
structure Activity where
  start : Nat
  finish : Nat
  deriving Repr, DecidableEq

/--
Two activities are compatible when one finishes before the other starts.  This
is the symmetric textbook notion used for unordered sets of selected
activities.
-/
def Compatible (a b : Activity) : Prop :=
  a.finish ≤ b.start ∨ b.finish ≤ a.start

/--
{lit}`Before a b` is the oriented compatibility relation used by a selected
list: activity {lit}`a` is scheduled before activity {lit}`b`.
-/
def Before (a b : Activity) : Prop :=
  a.finish ≤ b.start

/--
A selected list is feasible when it is in chronological order and every head
activity finishes before every activity in the tail starts.
-/
def Feasible : List Activity → Prop
  | [] => True
  | a :: rest => Feasible rest ∧ ∀ b ∈ rest, Before a b

/--
Every activity after {lit}`a` in a feasible {lit}`a :: rest` selection is
compatible with {lit}`a`.
-/
theorem compatible_of_before {a b : Activity} (h : Before a b) :
    Compatible a b := by
  exact Or.inl h

/--
The tail of a feasible selected list is feasible.
-/
theorem feasible_tail {a : Activity} {rest : List Activity}
    (h : Feasible (a :: rest)) :
    Feasible rest := by
  exact h.1

/--
Consing an activity onto a feasible tail preserves feasibility when the new
activity finishes before every activity in the tail starts.
-/
theorem feasible_cons {a : Activity} {rest : List Activity}
    (hrest : Feasible rest)
    (ha : ∀ b ∈ rest, Before a b) :
    Feasible (a :: rest) := by
  exact ⟨hrest, ha⟩

/-! ## Earliest finishing activity -/

/--
{lit}`MinFinish a xs` says that {lit}`a` is an element of {lit}`xs` with
minimum finish time among all activities in {lit}`xs`.
-/
def MinFinish (a : Activity) (xs : List Activity) : Prop :=
  a ∈ xs ∧ ∀ b ∈ xs, a.finish ≤ b.finish

/--
Select an activity with earliest finish time from a finite list, returning
{lit}`none` on the empty list.
-/
def earliest_finish : List Activity → Option Activity
  | [] => none
  | a :: rest =>
      match earliest_finish rest with
      | none => some a
      | some b => if a.finish ≤ b.finish then some a else some b

/--
The earliest-finish selector returns {lit}`none` exactly for the empty list.
-/
theorem earliest_finish_eq_none_iff (xs : List Activity) :
    earliest_finish xs = none ↔ xs = [] := by
  induction xs with
  | nil =>
      simp [earliest_finish]
  | cons a rest ih =>
      rw [earliest_finish]
      cases hrest : earliest_finish rest with
      | none =>
          simp
      | some b =>
          by_cases hab : a.finish ≤ b.finish <;> simp [hab]

/--
The executable selector {name}`earliest_finish` returns a minimum-finish
activity.
-/
theorem earliest_finish_minFinish {xs : List Activity} {a : Activity}
    (h : earliest_finish xs = some a) :
    MinFinish a xs := by
  induction xs generalizing a with
  | nil =>
      simp [earliest_finish] at h
  | cons head rest ih =>
      rw [earliest_finish] at h
      cases hrest : earliest_finish rest with
      | none =>
          have hrest_empty : rest = [] :=
            (earliest_finish_eq_none_iff rest).mp hrest
          subst rest
          simp [earliest_finish] at h
          subst a
          simp [MinFinish]
      | some best =>
          have hbest : MinFinish best rest := ih hrest
          by_cases hhead : head.finish ≤ best.finish
          · simp [hrest, hhead] at h
            subst a
            constructor
            · simp
            · intro b hb
              simp at hb
              rcases hb with rfl | hb
              · rfl
              · exact Nat.le_trans hhead (hbest.2 b hb)
          · simp [hrest, hhead] at h
            subst a
            have hbest_head : best.finish ≤ head.finish :=
              Nat.le_of_lt (Nat.lt_of_not_ge hhead)
            constructor
            · simp [hbest.1]
            · intro b hb
              simp at hb
              rcases hb with rfl | hb
              · exact hbest_head
              · exact hbest.2 b hb

/-! ## Subproblems and greedy selection -/

/--
The activities still available after choosing {lit}`a`: those whose start time
is at least {lit}`a.finish`.
-/
def activitiesAfter (a : Activity) (xs : List Activity) : List Activity :=
  xs.filter fun b => decide (a.finish ≤ b.start)

/--
Membership in {name}`activitiesAfter` is exactly membership in the source list plus
oriented compatibility with the chosen activity.
-/
theorem mem_activitiesAfter {a b : Activity} {xs : List Activity} :
    b ∈ activitiesAfter a xs ↔ b ∈ xs ∧ Before a b := by
  simp [activitiesAfter, Before]

/--
The CLRS recursive greedy algorithm, parameterized by the list order supplied by
the caller.  On a list sorted by finish time, the head is an earliest-finishing
available activity.
-/
def greedySelect : List Activity → List Activity
  | [] => []
  | a :: rest => a :: greedySelect (activitiesAfter a rest)
termination_by xs => xs.length
decreasing_by
  simp_wf
  dsimp [activitiesAfter]
  have hle :
      (List.filter (fun b => decide (a.finish ≤ b.start)) rest).length ≤ rest.length :=
    List.length_filter_le (fun b => decide (a.finish ≤ b.start)) rest
  omega

/-! ## Maximum-cardinality certificates -/

/--
{lit}`MaxCardinality available selected` says that {lit}`selected` is a
feasible sublist of {lit}`available` and no feasible sublist of
{lit}`available` has larger cardinality.
-/
structure MaxCardinality (available selected : List Activity) : Prop where
  sublist : selected.Sublist available
  feasible : Feasible selected
  maximum :
    ∀ other, other.Sublist available → Feasible other →
      other.length ≤ selected.length

/--
A one-step greedy-choice certificate.  The field {lit}`exchange` is the CLRS
exchange argument: every feasible competitor can be converted, without losing
cardinality, into one that starts with the chosen greedy activity and then uses
only the {lit}`after` subproblem.
-/
structure GreedyChoiceCertificate
    (available after selected : List Activity) (a : Activity) : Prop where
  chosen_sublist : (a :: selected).Sublist available
  selected_after : ∀ b ∈ selected, Before a b
  exchange :
    ∀ other, other.Sublist available → Feasible other →
      ∃ tail, tail.Sublist after ∧ Feasible tail ∧
        other.length ≤ (a :: tail).length

/--
**Greedy-choice feasibility.**  If {lit}`a` has minimum finish time among the
available activities and an optimal tail solution is compatible with {lit}`a`,
then prepending {lit}`a` preserves feasibility.

The minimum-finish hypothesis records the CLRS greedy choice; feasibility itself
uses only the compatibility of the chosen tail.
-/
theorem greedy_choice_minFinish_preserves_optimal_tail_feasibility
    {available after selected : List Activity} {a : Activity}
    (hmin : MinFinish a available)
    (hopt : MaxCardinality after selected)
    (hafter : ∀ b ∈ selected, Before a b) :
    Feasible (a :: selected) := by
  rcases hmin with ⟨_, _⟩
  exact feasible_cons hopt.feasible hafter

/--
If the tail is maximum-cardinality for the post-greedy subproblem, then every
chosen-tail competitor has size at most the greedy choice plus that tail.
-/
theorem chosen_tail_bound_of_tail_optimal
    {after selected tail : List Activity} {a : Activity}
    (hopt : MaxCardinality after selected)
    (htail : tail.Sublist after)
    (hfeasible : Feasible tail) :
    (a :: tail).length ≤ (a :: selected).length := by
  have htail_len : tail.length ≤ selected.length :=
    hopt.maximum tail htail hfeasible
  simpa using Nat.succ_le_succ htail_len

/--
**Certificate-based greedy-choice optimality.**  This is the Lean-friendly
version of the CLRS exchange step.  Given:

* an optimal solution {lit}`selected` for the {lit}`after` subproblem, and
* a certificate that every feasible competitor for {lit}`available` can be exchanged
  for one beginning with {lit}`a`,

the solution {lit}`a :: selected` is maximum-cardinality for {lit}`available`.
-/
theorem greedy_choice_optimal_from_certificate
    {available after selected : List Activity} {a : Activity}
    (hopt : MaxCardinality after selected)
    (hcert : GreedyChoiceCertificate available after selected a) :
    MaxCardinality available (a :: selected) := by
  refine ⟨hcert.chosen_sublist, ?_, ?_⟩
  · exact feasible_cons hopt.feasible hcert.selected_after
  · intro other hsub hfeasible
    rcases hcert.exchange other hsub hfeasible with
      ⟨tail, htail_sub, htail_feasible, hle_exchange⟩
    have htail_bound :
        (a :: tail).length ≤ (a :: selected).length :=
      chosen_tail_bound_of_tail_optimal hopt htail_sub htail_feasible
    exact Nat.le_trans hle_exchange htail_bound

end ActivitySelection
end CLRS
