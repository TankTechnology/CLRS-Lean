import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.ReductionMachine.Incidence.Endpoints.Run
import Mathlib.Tactic

/-!
# HAM-CYCLE selector endpoints: extractor runtime bounds
-/

noncomputable section

namespace CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints

open PolyBuilder
open HamiltonianCycleReduction

def referenceLength (ref : IncidentOccurrence) : Nat :=
  (Scanner.encodeIncidentOccurrence ref).length

@[simp] theorem referenceLength_eq (ref : IncidentOccurrence) :
    referenceLength ref =
      ref.occurrence + Scanner.sideValue ref.rightSide + 2 := by
  rcases ref with ⟨occurrence, side⟩
  simp [referenceLength, Scanner.encodeIncidentOccurrence,
    encodeUnaryFrame_length]
  omega

private theorem firstReferenceSteps_le (ref : IncidentOccurrence) :
    firstReferenceSteps ref ≤ 4 * referenceLength ref := by
  rcases ref with ⟨occurrence, side⟩
  cases side <;>
    simp [firstReferenceSteps, sideSteps, referenceLength_eq,
      Scanner.sideValue] <;> omega

private theorem nextReferenceSteps_le
    (previous current : IncidentOccurrence) :
    nextReferenceSteps previous current ≤
      3 * (referenceLength previous + referenceLength current) := by
  rcases previous with ⟨previousOccurrence, previousSide⟩
  rcases current with ⟨currentOccurrence, currentSide⟩
  cases previousSide <;> cases currentSide <;>
    simp [nextReferenceSteps, sideSteps, referenceLength_eq,
      Scanner.sideValue] <;> omega

private theorem emitSteps_le (first last : IncidentOccurrence) :
    emitSteps first last ≤
      20 * (referenceLength first + referenceLength last) := by
  rcases first with ⟨firstOccurrence, firstSide⟩
  rcases last with ⟨lastOccurrence, lastSide⟩
  cases firstSide <;> cases lastSide <;>
    simp [emitSteps, referenceLength_eq, Scanner.sideValue] <;> omega

private theorem remainingSteps_le (first last : IncidentOccurrence)
    (refs : List IncidentOccurrence) :
    remainingSteps first last refs ≤
      20 * referenceLength first + 20 * referenceLength last +
        25 * (refs.map referenceLength).sum + 1 := by
  induction refs generalizing last with
  | nil =>
      have hemit := emitSteps_le first last
      simp only [remainingSteps, List.map_nil, List.sum_nil, Nat.mul_zero]
      simpa [Nat.mul_add] using Nat.add_le_add_right hemit 1
  | cons current refs ih =>
      have hnext := nextReferenceSteps_le last current
      have hrest := ih current
      simp only [remainingSteps, List.map_cons, List.sum_cons]
      omega

private theorem referencePayload_length (refs : List IncidentOccurrence) :
    (refs.flatMap Scanner.encodeIncidentOccurrence).length =
      (refs.map referenceLength).sum := by
  induction refs with
  | nil => rfl
  | cons ref refs ih => simp [referenceLength, ih]

private theorem rowSteps_le (refs : List IncidentOccurrence) :
    rowSteps refs ≤
      50 * ((refs.flatMap Scanner.encodeIncidentOccurrence).length + 1) := by
  cases refs with
  | nil => simp [rowSteps]
  | cons first rest =>
      have hfirst := firstReferenceSteps_le first
      have hrest := remainingSteps_le first first rest
      rw [referencePayload_length]
      simp only [rowSteps, List.map_cons, List.sum_cons]
      omega

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

theorem extractorSteps_le (I : VertexCoverInstance) :
    extractorSteps I ≤ 52 * (Scanner.stream I).length.succ := by
  have hrows := rowsSteps_le (incidenceReferenceRows I)
  rw [encodeReferenceRows_incidence I] at hrows
  unfold extractorSteps
  omega

end CLRS.Chapter34.Turing.HamiltonianCycle.ReductionMachine.Incidence.Endpoints
