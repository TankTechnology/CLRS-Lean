import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Gadget.Basic

/-!
# Vertex numbering for the CLRS VERTEX-COVER to HAM-CYCLE reduction

Each source edge occurrence owns a consecutive block of twelve gadget
vertices.  Selector vertices follow all gadget blocks.  Edge *occurrences*,
rather than distinct edge values, are used deliberately because the shared
graph grammar permits duplicate edge records.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- One source-edge occurrence incident on a source vertex.  `rightSide`
records which six-vertex side of that occurrence belongs to the vertex. -/
structure IncidentOccurrence where
  occurrence : Nat
  rightSide : Bool
  deriving DecidableEq, Repr

/-- Global vertex number of a local vertex in an edge gadget. -/
def globalWidgetVertex (occurrence localVertex : Nat) : Nat :=
  widgetVertexCount * occurrence + localVertex

/-- First global selector number. -/
def selectorBase (edgeCount : Nat) : Nat :=
  widgetVertexCount * edgeCount

/-- Global number of a selector vertex. -/
def selectorVertex (edgeCount selector : Nat) : Nat :=
  selectorBase edgeCount + selector

/-- Global vertex on the side represented by an incident occurrence. -/
def incidentVertex (ref : IncidentOccurrence) (position : Nat) : Nat :=
  globalWidgetVertex ref.occurrence (widgetVertex ref.rightSide position)

/-- Scan edge records while retaining their occurrence indices. -/
def incidentOccurrencesFrom (u start : Nat) :
    List (Nat × Nat) → List IncidentOccurrence
  | [] => []
  | e :: edges =>
      let rest := incidentOccurrencesFrom u (start + 1) edges
      if e.1 = u then
        { occurrence := start, rightSide := false } :: rest
      else if e.2 = u then
        { occurrence := start, rightSide := true } :: rest
      else
        rest

/-- All edge occurrences incident on a source vertex, in source-list order. -/
def incidentOccurrences (I : CliqueInstance) (u : Nat) :
    List IncidentOccurrence :=
  incidentOccurrencesFrom u 0 I.edges

theorem occurrence_lt_of_mem_incidentOccurrencesFrom
    {u start : Nat} {edges : List (Nat × Nat)} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrencesFrom u start edges) :
    ref.occurrence < start + edges.length := by
  induction edges generalizing start with
  | nil => simp [incidentOccurrencesFrom] at href
  | cons e edges ih =>
      simp only [incidentOccurrencesFrom] at href
      split at href <;> rename_i hleft
      · simp only [List.mem_cons] at href
        rcases href with heq | href
        · simpa [heq]
        · have := ih href
          simp only [List.length_cons]
          omega
      · split at href <;> rename_i hright
        · simp only [List.mem_cons] at href
          rcases href with heq | href
          · simpa [heq]
          · have := ih href
            simp only [List.length_cons]
            omega
        · have := ih href
          simp only [List.length_cons]
          omega

theorem start_le_occurrence_of_mem_incidentOccurrencesFrom
    {u start : Nat} {edges : List (Nat × Nat)} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrencesFrom u start edges) :
    start ≤ ref.occurrence := by
  induction edges generalizing start with
  | nil => simp [incidentOccurrencesFrom] at href
  | cons e edges ih =>
      simp only [incidentOccurrencesFrom] at href
      split at href
      · simp only [List.mem_cons] at href
        rcases href with heq | href
        · simpa [heq]
        · exact Nat.le_trans (Nat.le_add_right start 1) (ih href)
      · split at href
        · simp only [List.mem_cons] at href
          rcases href with heq | href
          · simpa [heq]
          · exact Nat.le_trans (Nat.le_add_right start 1) (ih href)
        · exact Nat.le_trans (Nat.le_add_right start 1) (ih href)

/-- Incident occurrences retain strict source-list order. -/
theorem incidentOccurrencesFrom_pairwise
    (u start : Nat) (edges : List (Nat × Nat)) :
    (incidentOccurrencesFrom u start edges).Pairwise
      (fun first second => first.occurrence < second.occurrence) := by
  induction edges generalizing start with
  | nil => simp [incidentOccurrencesFrom]
  | cons e edges ih =>
      simp only [incidentOccurrencesFrom]
      split
      · simp only [List.pairwise_cons]
        constructor
        · intro ref href
          have hstart := start_le_occurrence_of_mem_incidentOccurrencesFrom href
          omega
        · exact ih (start + 1)
      · split
        · simp only [List.pairwise_cons]
          constructor
          · intro ref href
            have hstart := start_le_occurrence_of_mem_incidentOccurrencesFrom href
            omega
          · exact ih (start + 1)
        · exact ih (start + 1)

theorem occurrence_lt_of_mem_incidentOccurrences
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u) :
    ref.occurrence < I.edges.length := by
  simpa [incidentOccurrences] using
    occurrence_lt_of_mem_incidentOccurrencesFrom href

theorem incidentOccurrences_pairwise (I : CliqueInstance) (u : Nat) :
    (incidentOccurrences I u).Pairwise
      (fun first second => first.occurrence < second.occurrence) := by
  exact incidentOccurrencesFrom_pairwise u 0 I.edges

theorem widgetVertex_lt (rightSide : Bool) {position : Nat}
    (hposition : position < 6) :
    widgetVertex rightSide position < widgetVertexCount := by
  cases rightSide <;> simp [widgetVertex, widgetVertexCount] <;> omega

theorem globalWidgetVertex_lt_selectorBase
    {occurrence localVertex edgeCount : Nat}
    (hoccurrence : occurrence < edgeCount)
    (hlocal : localVertex < widgetVertexCount) :
    globalWidgetVertex occurrence localVertex < selectorBase edgeCount := by
  change localVertex < 12 at hlocal
  change 12 * occurrence + localVertex < 12 * edgeCount
  omega

theorem incidentVertex_lt_selectorBase
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u)
    {position : Nat} (hposition : position < 6) :
    incidentVertex ref position < selectorBase I.edges.length := by
  apply globalWidgetVertex_lt_selectorBase
  · exact occurrence_lt_of_mem_incidentOccurrences href
  · exact widgetVertex_lt ref.rightSide hposition

theorem incidentVertex_lt_of_occurrence_lt
    {first second : IncidentOccurrence}
    (hoccurrence : first.occurrence < second.occurrence)
    {firstPosition secondPosition : Nat}
    (hfirstPosition : firstPosition < 6)
    (hsecondPosition : secondPosition < 6) :
    incidentVertex first firstPosition <
      incidentVertex second secondPosition := by
  cases first with
  | mk firstOccurrence firstSide =>
      cases second with
      | mk secondOccurrence secondSide =>
          change firstOccurrence < secondOccurrence at hoccurrence
          cases firstSide <;> cases secondSide <;>
            simp [incidentVertex, globalWidgetVertex, widgetVertex,
              widgetVertexCount] <;> omega

theorem selectorVertex_lt
    {edgeCount selector selectorCount : Nat}
    (hselector : selector < selectorCount) :
    selectorVertex edgeCount selector <
      selectorBase edgeCount + selectorCount := by
  simp only [selectorVertex]
  omega

end CLRS.Chapter34.HamiltonianCycleReduction
