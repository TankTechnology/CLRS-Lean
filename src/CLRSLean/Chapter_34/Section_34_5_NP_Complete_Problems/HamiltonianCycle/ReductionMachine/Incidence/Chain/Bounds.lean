import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Chain.Run
import Mathlib.Tactic

/-!
# HAM-CYCLE incidence-chain formatter: uniform runtime bounds
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain

open PolyBuilder
open HamiltonianCycleReduction

/-- Encoded length of one incidence reference. -/
def referenceLength (ref : IncidentOccurrence) : Nat :=
  (Scanner.encodeIncidentOccurrence ref).length

@[simp] theorem referenceLength_eq (ref : IncidentOccurrence) :
    referenceLength ref =
      ref.occurrence + Scanner.sideValue ref.rightSide + 2 := by
  rcases ref with ⟨occurrence, side⟩
  simp [referenceLength, Scanner.encodeIncidentOccurrence,
    encodeUnaryFrame_length]
  omega

private theorem referenceSteps_le (ref : IncidentOccurrence) :
    referenceSteps ref ≤ 3 * referenceLength ref := by
  rcases ref with ⟨occurrence, side⟩
  cases side <;>
    simp [referenceSteps, sideSteps, referenceLength_eq,
      Scanner.sideValue] <;> omega

private theorem emitSteps_le
    (previous current : IncidentOccurrence) :
    emitSteps previous current ≤
      20 * (referenceLength previous + referenceLength current) := by
  rcases previous with ⟨previousOccurrence, previousSide⟩
  rcases current with ⟨currentOccurrence, currentSide⟩
  cases previousSide <;> cases currentSide <;>
    simp [emitSteps, incidentOffset, referenceLength_eq,
      Scanner.sideValue] <;> omega

private theorem remainingSteps_le (previous : IncidentOccurrence)
    (refs : List IncidentOccurrence) :
    remainingSteps previous refs ≤
      25 * referenceLength previous +
        50 * (refs.map referenceLength).sum := by
  induction refs generalizing previous with
  | nil =>
      rcases previous with ⟨occurrence, side⟩
      cases side with
      | false =>
          simp [remainingSteps, referenceLength_eq, Scanner.sideValue]
      | true =>
          simp [remainingSteps, referenceLength_eq, Scanner.sideValue]
          omega
  | cons current refs ih =>
      have hreference := referenceSteps_le current
      have hemit := emitSteps_le previous current
      have hrest := ih current
      simp only [remainingSteps, List.map_cons, List.sum_cons]
      omega

private theorem referencePayload_length (refs : List IncidentOccurrence) :
    (refs.flatMap Scanner.encodeIncidentOccurrence).length =
      (refs.map referenceLength).sum := by
  induction refs with
  | nil => rfl
  | cons ref refs ih =>
      simp [referenceLength, ih]

private theorem rowSteps_le (refs : List IncidentOccurrence) :
    rowSteps refs ≤
      50 * ((refs.flatMap Scanner.encodeIncidentOccurrence).length + 1) := by
  cases refs with
  | nil => simp [rowSteps]
  | cons first rest =>
      have hfirst := referenceSteps_le first
      have hrest := remainingSteps_le first rest
      rw [referencePayload_length]
      simp only [rowSteps, List.map_cons, List.sum_cons]
      omega

/-- Formatting cost is linear in the marked-row stream length. -/
theorem rowsSteps_le (rows : List (List IncidentOccurrence)) :
    rowsSteps rows ≤ 50 * (encodeReferenceRows rows).length := by
  induction rows with
  | nil => simp [rowsSteps, encodeReferenceRows]
  | cons refs rows ih =>
      have hrefs := rowSteps_le refs
      have hlength : (encodeReferenceRows (refs :: rows)).length =
          (refs.flatMap Scanner.encodeIncidentOccurrence).length + 1 +
            (encodeReferenceRows rows).length := by
        simp [encodeReferenceRows]
        omega
      rw [hlength]
      simp only [rowsSteps]
      omega

/-- The exact formatter execution fits one fixed linear polynomial in its
scanner-stream input length. -/
theorem formatterSteps_le (I : VertexCoverInstance) :
    formatterSteps I ≤ 52 * (Scanner.stream I).length.succ := by
  have hrows := rowsSteps_le (incidenceReferenceRows I)
  rw [encodeReferenceRows_incidence I] at hrows
  unfold formatterSteps
  omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Chain
