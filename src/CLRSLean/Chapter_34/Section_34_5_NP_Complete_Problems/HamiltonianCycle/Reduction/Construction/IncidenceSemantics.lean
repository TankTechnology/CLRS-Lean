import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Construction.WellFormed
import Mathlib.Data.List.Enum

/-!
# Semantic interface for source-edge incidence lists

The executable scanner in `Numbering.lean` is connected here to indexed source
edges.  Later cycle construction and soundness proofs can therefore reason
about a gadget side as an endpoint of the corresponding source edge, without
unfolding the recursive scan.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- Interpret one indexed source edge as an incident gadget side for `u`. -/
def incidentOccurrenceFor (u : Nat)
    (indexedEdge : (Nat × Nat) × Nat) : Option IncidentOccurrence :=
  if indexedEdge.1.1 = u then
    some { occurrence := indexedEdge.2, rightSide := false }
  else if indexedEdge.1.2 = u then
    some { occurrence := indexedEdge.2, rightSide := true }
  else
    none

theorem incidentOccurrencesFrom_eq_filterMap_zipIdx
    (u start : Nat) (edges : List (Nat × Nat)) :
    incidentOccurrencesFrom u start edges =
      (edges.zipIdx start).filterMap (incidentOccurrenceFor u) := by
  induction edges generalizing start with
  | nil => simp [incidentOccurrencesFrom]
  | cons edge edges ih =>
      simp only [incidentOccurrencesFrom, List.zipIdx_cons, List.filterMap_cons]
      rw [ih]
      by_cases hleft : edge.1 = u
      · simp [incidentOccurrenceFor, hleft]
      · by_cases hright : edge.2 = u
        · simp [incidentOccurrenceFor, hleft, hright]
        · simp [incidentOccurrenceFor, hleft, hright]

theorem mem_incidentOccurrences_iff
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence} :
    ref ∈ incidentOccurrences I u ↔
      ∃ i, ∃ hi : i < I.edges.length,
        incidentOccurrenceFor u (I.edges[i], i) = some ref := by
  rw [incidentOccurrences,
    incidentOccurrencesFrom_eq_filterMap_zipIdx]
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨indexedEdge, hindexedEdge, href⟩
    have hexists : ∃ i, ∃ hi : i < I.edges.length,
        indexedEdge = (I.edges[i], i) := by
      rw [← List.exists_mem_zipIdx']
      exact ⟨indexedEdge, hindexedEdge, rfl⟩
    rcases hexists with ⟨i, hi, rfl⟩
    exact ⟨i, hi, href⟩
  · rintro ⟨i, hi, href⟩
    refine ⟨(I.edges[i], i), ?_, href⟩
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simpa using hi
    · simp

theorem leftIncidentOccurrence_mem
    {I : CliqueInstance} {u i : Nat} (hi : i < I.edges.length)
    (hu : I.edges[i].1 = u) :
    ({ occurrence := i, rightSide := false } : IncidentOccurrence) ∈
      incidentOccurrences I u := by
  rw [mem_incidentOccurrences_iff]
  exact ⟨i, hi, by simp [incidentOccurrenceFor, hu]⟩

theorem rightIncidentOccurrence_mem
    {I : CliqueInstance} {u i : Nat} (hi : i < I.edges.length)
    (hleft : I.edges[i].1 ≠ u) (hu : I.edges[i].2 = u) :
    ({ occurrence := i, rightSide := true } : IncidentOccurrence) ∈
      incidentOccurrences I u := by
  rw [mem_incidentOccurrences_iff]
  exact ⟨i, hi, by simp [incidentOccurrenceFor, hleft, hu]⟩

theorem endpoints_of_mem_incidentOccurrences
    {I : CliqueInstance} {u : Nat} {ref : IncidentOccurrence}
    (href : ref ∈ incidentOccurrences I u) :
    ∃ hi : ref.occurrence < I.edges.length,
      (ref.rightSide = false ∧ I.edges[ref.occurrence].1 = u) ∨
      (ref.rightSide = true ∧ I.edges[ref.occurrence].1 ≠ u ∧
        I.edges[ref.occurrence].2 = u) := by
  rw [mem_incidentOccurrences_iff] at href
  rcases href with ⟨i, hi, href⟩
  simp only [incidentOccurrenceFor] at href
  split at href <;> rename_i hleft
  · simp only [Option.some.injEq, IncidentOccurrence.mk.injEq] at href
    rcases href with ⟨rfl, rfl⟩
    exact ⟨hi, Or.inl ⟨rfl, hleft⟩⟩
  · split at href <;> rename_i hright
    · simp only [Option.some.injEq, IncidentOccurrence.mk.injEq] at href
      rcases href with ⟨rfl, rfl⟩
      exact ⟨hi, Or.inr ⟨rfl, hleft, hright⟩⟩
    · contradiction

end CLRS.Chapter34.HamiltonianCycleReduction
