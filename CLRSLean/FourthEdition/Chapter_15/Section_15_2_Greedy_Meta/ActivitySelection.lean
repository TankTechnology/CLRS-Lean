import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection
import CLRSLean.FourthEdition.Chapter_15.Section_15_2_Greedy_Meta

/-!
# Activity selection as a {lit}`GreedyProblem`

This companion connects the concrete §15.1 exchange proof to the abstract
§15.2 framework.  Problem instances carry the finish-sortedness invariant, so
the generic solver's axioms are proved rather than assumed by callers.
-/

namespace CLRS.GreedyMeta

open CLRS.ActivitySelection

/-- A finish-time-sorted activity-selection subproblem. -/
abbrev SortedActivityProblem :=
  {xs : List Activity // FinishSorted xs}

def activityGreedyElt : SortedActivityProblem → Option Activity
  | ⟨[], _⟩ => none
  | ⟨a :: _, _⟩ => some a

def activitySubproblem : SortedActivityProblem → SortedActivityProblem
  | ⟨[], _⟩ => ⟨[], by simp [FinishSorted]⟩
  | ⟨a :: rest, hsorted⟩ =>
      ⟨activitiesAfter a rest,
        finishSorted_activitiesAfter (List.pairwise_cons.mp hsorted).2⟩

def activityCombine : Option Activity → List Activity → List Activity
  | none, selected => selected
  | some a, selected => a :: selected

def activityOptimal (p : SortedActivityProblem) (selected : List Activity) : Prop :=
  MaxCardinality p.1 selected

def activitySize (p : SortedActivityProblem) : Nat :=
  p.1.length

/--
The §15.1 activity-selection problem satisfies the separated greedy-choice and
optimal-substructure interface from §15.2.
-/
noncomputable def activityGreedyProblem :
    GreedyProblem (Option Activity) (List Activity) SortedActivityProblem where
  optimal := activityOptimal
  greedyElt := activityGreedyElt
  sub := activitySubproblem
  combine := activityCombine
  base := []
  size := activitySize
  greedy_choice := by
    rintro ⟨xs, hsorted⟩ hpos
    cases xs with
    | nil => simp [activitySize] at hpos
    | cons a rest =>
        refine ⟨greedySelect (activitiesAfter a rest), ?_⟩
        exact greedySelect_cons_maxCardinality hsorted
  optimal_substructure := by
    rintro ⟨xs, hsorted⟩ tail hpos hwhole
    cases xs with
    | nil => simp [activitySize] at hpos
    | cons a rest =>
        change MaxCardinality (activitiesAfter a rest) tail
        change MaxCardinality (a :: rest) (a :: tail) at hwhole
        have htailSub : tail.Sublist (activitiesAfter a rest) :=
          feasible_competitor_tail_sublist_after
            (finishSorted_head_minFinish hsorted) hwhole.sublist hwhole.feasible.2
        refine ⟨htailSub, hwhole.feasible.1, ?_⟩
        intro other hotherSub hotherFeasible
        have hotherBefore : ∀ b ∈ other, Before a b := by
          intro b hb
          exact (mem_activitiesAfter.mp (hotherSub.subset hb)).2
        have hbound := hwhole.maximum (a :: other)
          (List.Sublist.cons_cons a
            (hotherSub.trans (activitiesAfter_sublist a rest)))
          (feasible_cons hotherFeasible hotherBefore)
        simpa using hbound
  replace_optimal_tail := by
    rintro ⟨xs, hsorted⟩ oldTail newTail hpos hold hnew hwhole
    cases xs with
    | nil => simp [activitySize] at hpos
    | cons a rest =>
        change MaxCardinality (activitiesAfter a rest) newTail at hnew
        change MaxCardinality (a :: rest) (a :: newTail)
        exact greedy_choice_optimal_from_certificate hnew
          (finishSorted_greedyChoiceCertificate hsorted hnew.sublist)
  sub_lt := by
    rintro ⟨xs, _hsorted⟩ hpos
    cases xs with
    | nil => simp [activitySize] at hpos
    | cons a rest =>
        have hle := (activitiesAfter_sublist a rest).length_le
        change (activitiesAfter a rest).length < (a :: rest).length
        simpa using Nat.lt_succ_of_le hle
  base_opt := by
    rintro ⟨xs, hsorted⟩ hzero
    cases xs with
    | nil =>
        exact ⟨by simp, by simp [Feasible], by
          intro other hsub _
          simpa using hsub.length_le⟩
    | cons a rest => simp [activitySize] at hzero

/-- Generic §15.2 optimality specialized to activity selection. -/
theorem activityGsolve_maxCardinality (p : SortedActivityProblem) :
    MaxCardinality p.1 (gsolve activityGreedyProblem p) :=
  gsolve_optimal activityGreedyProblem p

/-- The generic solver computes the same recursive selector formalized in §15.1. -/
theorem activityGsolve_eq_greedySelect (p : SortedActivityProblem) :
    gsolve activityGreedyProblem p = greedySelect p.1 := by
  induction hsize : activitySize p using Nat.strong_induction_on generalizing p with
  | h n ih =>
      rcases p with ⟨xs, hsorted⟩
      cases xs with
      | nil =>
          rw [gsolve_base activityGreedyProblem (by rfl)]
          simp [activityGreedyProblem, greedySelect]
      | cons a rest =>
          have hpos : activityGreedyProblem.size ⟨a :: rest, hsorted⟩ > 0 := by
            simp [activityGreedyProblem, activitySize]
          rw [gsolve_eq activityGreedyProblem hpos, greedySelect_cons_eq]
          change a :: gsolve activityGreedyProblem
              (activitySubproblem ⟨a :: rest, hsorted⟩) =
            a :: greedySelect (activitiesAfter a rest)
          apply congrArg (a :: ·)
          have hlt := activityGreedyProblem.sub_lt ⟨a :: rest, hsorted⟩ hpos
          have hltN : activitySize (activitySubproblem ⟨a :: rest, hsorted⟩) < n := by
            rw [← hsize]
            exact hlt
          simpa [activitySubproblem] using
            ih (activitySize (activitySubproblem ⟨a :: rest, hsorted⟩)) hltN
              (activitySubproblem ⟨a :: rest, hsorted⟩) rfl

/-- The concrete §15.1 optimum theorem is recovered from the §15.2 instance. -/
theorem greedySelect_maxCardinality_via_meta {xs : List Activity}
    (hsorted : FinishSorted xs) :
    MaxCardinality xs (greedySelect xs) := by
  let p : SortedActivityProblem := ⟨xs, hsorted⟩
  rw [← activityGsolve_eq_greedySelect p]
  exact activityGsolve_maxCardinality p

/-- The abstract instance exposes the two textbook properties separately. -/
theorem activityGreedyChoiceProperty :
    GreedyChoiceProperty SortedActivityProblem (Option Activity) (List Activity)
      activityOptimal (fun p => activitySize p > 0)
      activityGreedyElt activityCombine :=
  activityGreedyProblem.greedyChoiceProperty

theorem activityOptimalSubstructure :
    OptimalSubstructure SortedActivityProblem (Option Activity) (List Activity)
      activityOptimal (fun p => activitySize p > 0)
      activityGreedyElt activitySubproblem activityCombine :=
  activityGreedyProblem.hasOptimalSubstructure

end CLRS.GreedyMeta
