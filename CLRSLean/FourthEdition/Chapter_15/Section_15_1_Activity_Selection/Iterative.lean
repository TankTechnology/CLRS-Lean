import CLRSLean.FourthEdition.Chapter_15.Section_15_1_Activity_Selection.TextbookModel

/-!
# CLRS GREEDY-ACTIVITY-SELECTOR

This module gives the one-pass version of the activity-selection algorithm.
{lit}`greedyScan lastFinish xs` carries the finish time of the most recently chosen
activity and inspects every remaining activity exactly once.
-/

namespace CLRS.ActivitySelection

/-- Scan the finish-sorted candidates once, retaining compatible activities. -/
def greedyScan (lastFinish : Nat) : List Activity → List Activity
  | [] => []
  | a :: rest =>
      if lastFinish ≤ a.start then
        a :: greedyScan a.finish rest
      else
        greedyScan lastFinish rest

/-- The iterative textbook selector: choose the first activity, then scan. -/
def greedySelectIterative : List Activity → List Activity
  | [] => []
  | a :: rest => a :: greedyScan a.finish rest

private theorem filter_after_filter_eq
    (threshold : Nat) (a : Activity) (rest : List Activity)
    (hthreshold : threshold ≤ a.start) (hvalid : TextbookValid a) :
    activitiesAfter a
        (rest.filter fun b => decide (threshold ≤ b.start)) =
      rest.filter fun b => decide (a.finish ≤ b.start) := by
  rw [activitiesAfter, List.filter_filter]
  congr 1
  funext b
  by_cases hab : a.finish ≤ b.start
  · have hthresholdFinish : threshold ≤ a.finish :=
      Nat.le_trans hthreshold (Nat.le_of_lt hvalid)
    have hthresholdB : threshold ≤ b.start :=
      Nat.le_trans hthresholdFinish hab
    simp [hab, hthresholdB]
  · simp [hab]

private theorem greedyScan_eq_filtered_recursive
    (threshold : Nat) (xs : List Activity)
    (hsorted : FinishSorted xs) (hvalid : TextbookInput xs) :
    greedyScan threshold xs =
      greedySelect (xs.filter fun a => decide (threshold ≤ a.start)) := by
  induction xs generalizing threshold with
  | nil => simp [greedyScan, greedySelect]
  | cons a rest ih =>
      have hsortedParts := List.pairwise_cons.mp hsorted
      have hvalidParts := textbookInput_cons.mp hvalid
      by_cases hselect : threshold ≤ a.start
      · rw [greedyScan]
        simp only [hselect, if_pos]
        rw [show (a :: rest).filter (fun b => decide (threshold ≤ b.start)) =
            a :: rest.filter (fun b => decide (threshold ≤ b.start)) by
          simp [hselect]]
        rw [greedySelect_cons_eq]
        rw [filter_after_filter_eq threshold a rest hselect hvalidParts.1]
        exact congrArg (a :: ·)
          (ih a.finish hsortedParts.2 hvalidParts.2)
      · rw [greedyScan]
        simp only [hselect]
        rw [show (a :: rest).filter (fun b => decide (threshold ≤ b.start)) =
            rest.filter (fun b => decide (threshold ≤ b.start)) by
          simp [hselect]]
        exact ih threshold hsortedParts.2 hvalidParts.2

/--
The one-pass and recursive textbook selectors return the same activities on
finish-sorted, textbook-valid inputs.
-/
theorem greedySelectIterative_eq_greedySelect {xs : List Activity}
    (hsorted : FinishSorted xs) (hvalid : TextbookInput xs) :
    greedySelectIterative xs = greedySelect xs := by
  cases xs with
  | nil => simp [greedySelectIterative, greedySelect]
  | cons a rest =>
      have hsortedParts := List.pairwise_cons.mp hsorted
      have hvalidParts := textbookInput_cons.mp hvalid
      rw [greedySelectIterative, greedySelect_cons_eq]
      apply congrArg (a :: ·)
      simpa [activitiesAfter] using
        (greedyScan_eq_filtered_recursive a.finish rest
          hsortedParts.2 hvalidParts.2)

/-- The iterative selector inherits the complete maximum-cardinality theorem. -/
theorem greedySelectIterative_maxCardinality {xs : List Activity}
    (hsorted : FinishSorted xs) (hvalid : TextbookInput xs) :
    MaxCardinality xs (greedySelectIterative xs) := by
  rw [greedySelectIterative_eq_greedySelect hsorted hvalid]
  exact greedySelect_maxCardinality hsorted

/-! ## Exact scan cost -/

/-- Result and number of inspected candidates for {name}`greedyScan`. -/
def greedyScanCost (lastFinish : Nat) : List Activity → List Activity × Nat
  | [] => ([], 0)
  | a :: rest =>
      let tail := greedyScanCost (if lastFinish ≤ a.start then a.finish else lastFinish) rest
      (if lastFinish ≤ a.start then a :: tail.1 else tail.1, tail.2 + 1)

theorem greedyScanCost_result (lastFinish : Nat) (xs : List Activity) :
    (greedyScanCost lastFinish xs).1 = greedyScan lastFinish xs := by
  induction xs generalizing lastFinish with
  | nil => rfl
  | cons a rest ih =>
      simp only [greedyScanCost, greedyScan]
      by_cases h : lastFinish ≤ a.start
      · simp [h, ih]
      · simp [h, ih]

theorem greedyScanCost_steps (lastFinish : Nat) (xs : List Activity) :
    (greedyScanCost lastFinish xs).2 = xs.length := by
  induction xs generalizing lastFinish with
  | nil => rfl
  | cons a rest ih =>
      simp only [greedyScanCost]
      by_cases h : lastFinish ≤ a.start <;> simp [h, ih]

/-- Result and exact inspection count for the complete iterative selector. -/
def greedySelectIterativeCost : List Activity → List Activity × Nat
  | [] => ([], 0)
  | a :: rest =>
      let tail := greedyScanCost a.finish rest
      (a :: tail.1, tail.2 + 1)

theorem greedySelectIterativeCost_result (xs : List Activity) :
    (greedySelectIterativeCost xs).1 = greedySelectIterative xs := by
  cases xs with
  | nil => rfl
  | cons a rest =>
      simp [greedySelectIterativeCost, greedySelectIterative,
        greedyScanCost_result]

/--
The iterative algorithm inspects exactly {lit}`xs.length` activities.  This exact
cost identity is the formal Θ(n) statement for the unit-cost scan model.
-/
theorem greedySelectIterativeCost_steps (xs : List Activity) :
    (greedySelectIterativeCost xs).2 = xs.length := by
  cases xs with
  | nil => rfl
  | cons a rest =>
      simp [greedySelectIterativeCost, greedyScanCost_steps]

end CLRS.ActivitySelection
