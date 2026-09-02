import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.Reduction.Completeness.LocalCoverage

/-!
# Reindexing the incidences selected by a source cover

The executable certificate groups gadget traversals by selected source vertex.
For coverage it is more convenient to group the same incidences by source-edge
occurrence.  This file proves that the two incidence enumerations are
permutations.  Keeping this bridge above the vertex-path layer avoids mixing
the finite reindexing argument with arithmetic about global gadget numbers.
-/

namespace CLRS.Chapter34.HamiltonianCycleReduction

/-- All incidences owned by non-isolated vertices of the proposed cover. -/
def selectedCoverOccurrences
    (I : CliqueInstance) (cover : Finset Nat) : List IncidentOccurrence :=
  (activeCoverVertices I cover).flatMap (incidentOccurrences I)

/-- The selected endpoint incidences of one indexed source edge. -/
def coveredOccurrenceRefs
    (I : CliqueInstance) (cover : Finset Nat) (occurrence : Nat) :
    List IncidentOccurrence :=
  (if (I.edges[occurrence]?.getD (0, 0)).1 ∈ cover then
      [leftOccurrence occurrence]
    else []) ++
  (if (I.edges[occurrence]?.getD (0, 0)).2 ∈ cover then
      [rightOccurrence occurrence]
    else [])

/-- The edge-occurrence ordering of all endpoint incidences selected by the
cover. -/
def coveredOccurrences
    (I : CliqueInstance) (cover : Finset Nat) : List IncidentOccurrence :=
  (List.range I.edges.length).flatMap (coveredOccurrenceRefs I cover)

theorem incidentOccurrences_nodup (I : CliqueInstance) (u : Nat) :
    (incidentOccurrences I u).Nodup := by
  apply (incidentOccurrences_pairwise I u).imp
  intro first second hlt heq
  subst second
  exact (Nat.lt_irrefl first.occurrence hlt).elim

/-- An incidence reference belongs to the scanner output of at most one source
vertex.  The Boolean side tag is important here: it records which endpoint
owns the reference. -/
theorem sourceVertex_eq_of_mem_incidentOccurrences
    {I : CliqueInstance} {u v : Nat} {ref : IncidentOccurrence}
    (hu : ref ∈ incidentOccurrences I u)
    (hv : ref ∈ incidentOccurrences I v) :
    u = v := by
  rcases endpoints_of_mem_incidentOccurrences hu with
    ⟨_, huLeft | huRight⟩
  · rcases endpoints_of_mem_incidentOccurrences hv with
      ⟨_, hvLeft | hvRight⟩
    · exact huLeft.2.symm.trans hvLeft.2
    · simp [huLeft.1] at hvRight
  · rcases endpoints_of_mem_incidentOccurrences hv with
      ⟨_, hvLeft | hvRight⟩
    · simp [huRight.1] at hvLeft
    · exact huRight.2.2.symm.trans hvRight.2.2

theorem selectedCoverOccurrences_nodup
    (I : CliqueInstance) (cover : Finset Nat) :
    (selectedCoverOccurrences I cover).Nodup := by
  rw [selectedCoverOccurrences, List.nodup_flatMap]
  constructor
  · intro u _
    exact incidentOccurrences_nodup I u
  · apply (activeCoverVertices_nodup I cover).imp
    intro u v huv
    change List.Disjoint (incidentOccurrences I u) (incidentOccurrences I v)
    rw [List.disjoint_left]
    intro ref hrefU hrefV
    exact huv (sourceVertex_eq_of_mem_incidentOccurrences hrefU hrefV)

theorem mem_coveredOccurrenceRefs_iff
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    {ref : IncidentOccurrence} :
    ref ∈ coveredOccurrenceRefs I cover occurrence ↔
      (ref = leftOccurrence occurrence ∧ I.edges[occurrence].1 ∈ cover) ∨
      (ref = rightOccurrence occurrence ∧ I.edges[occurrence].2 ∈ cover) := by
  simp [coveredOccurrenceRefs, List.getElem?_eq_getElem hoccurrence,
    leftOccurrence, rightOccurrence, and_comm]

theorem occurrence_eq_of_mem_coveredOccurrenceRefs
    {I : CliqueInstance} {cover : Finset Nat} {occurrence : Nat}
    (hoccurrence : occurrence < I.edges.length)
    {ref : IncidentOccurrence}
    (href : ref ∈ coveredOccurrenceRefs I cover occurrence) :
    ref.occurrence = occurrence := by
  rcases (mem_coveredOccurrenceRefs_iff hoccurrence).mp href with
    ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl

theorem coveredOccurrenceRefs_nodup
    (I : CliqueInstance) (cover : Finset Nat) (occurrence : Nat) :
    (coveredOccurrenceRefs I cover occurrence).Nodup := by
  by_cases hleft : (I.edges[occurrence]?.getD (0, 0)).1 ∈ cover <;>
    by_cases hright : (I.edges[occurrence]?.getD (0, 0)).2 ∈ cover <;>
      simp [coveredOccurrenceRefs, hleft, hright,
        leftOccurrence, rightOccurrence]

theorem coveredOccurrences_nodup
    (I : CliqueInstance) (cover : Finset Nat) :
    (coveredOccurrences I cover).Nodup := by
  rw [coveredOccurrences, List.nodup_flatMap]
  constructor
  · intro occurrence _
    exact coveredOccurrenceRefs_nodup I cover occurrence
  · apply List.Pairwise.imp_of_mem _ List.nodup_range
    intro first second hfirstMem hsecondMem hne
    change List.Disjoint (coveredOccurrenceRefs I cover first)
      (coveredOccurrenceRefs I cover second)
    rw [List.disjoint_left]
    intro ref hrefFirst hrefSecond
    have hfirst : first < I.edges.length := by
      simpa using hfirstMem
    have hsecond : second < I.edges.length := by
      simpa using hsecondMem
    exact hne ((occurrence_eq_of_mem_coveredOccurrenceRefs hfirst hrefFirst).symm.trans
      (occurrence_eq_of_mem_coveredOccurrenceRefs hsecond hrefSecond))

theorem mem_coveredOccurrences_iff
    {I : CliqueInstance} {cover : Finset Nat} {ref : IncidentOccurrence} :
    ref ∈ coveredOccurrences I cover ↔
      ref.occurrence < I.edges.length ∧
        ((ref.rightSide = false ∧ (sourceEdgeForOccurrence I ref).1 ∈ cover) ∨
          (ref.rightSide = true ∧ (sourceEdgeForOccurrence I ref).2 ∈ cover)) := by
  simp only [coveredOccurrences, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨occurrence, hoccurrence, href⟩
    rcases (mem_coveredOccurrenceRefs_iff hoccurrence).mp href with
      ⟨rfl, hcover⟩ | ⟨rfl, hcover⟩
    · simpa [sourceEdgeForOccurrence_leftOccurrence hoccurrence] using
        ⟨hoccurrence, Or.inl ⟨rfl, hcover⟩⟩
    · simpa [sourceEdgeForOccurrence_rightOccurrence hoccurrence] using
        ⟨hoccurrence, Or.inr ⟨rfl, hcover⟩⟩
  · rintro ⟨hoccurrence, hside⟩
    refine ⟨ref.occurrence, hoccurrence, ?_⟩
    apply (mem_coveredOccurrenceRefs_iff hoccurrence).2
    rcases hside with ⟨hfalse, hcover⟩ | ⟨htrue, hcover⟩
    · left
      rcases ref with ⟨occurrence, side⟩
      simp only at hfalse
      subst side
      simp [sourceEdgeForOccurrence,
        List.getElem?_eq_getElem hoccurrence] at hcover
      exact ⟨rfl, hcover⟩
    · right
      rcases ref with ⟨occurrence, side⟩
      simp only at htrue
      subst side
      simp [sourceEdgeForOccurrence,
        List.getElem?_eq_getElem hoccurrence] at hcover
      exact ⟨rfl, hcover⟩

theorem mem_selectedCoverOccurrences_iff
    {I : CliqueInstance} {cover : Finset Nat} (hwellFormed : I.WellFormed)
    {ref : IncidentOccurrence} :
    ref ∈ selectedCoverOccurrences I cover ↔
      ref.occurrence < I.edges.length ∧
        ((ref.rightSide = false ∧ (sourceEdgeForOccurrence I ref).1 ∈ cover) ∨
          (ref.rightSide = true ∧ (sourceEdgeForOccurrence I ref).2 ∈ cover)) := by
  simp only [selectedCoverOccurrences, List.mem_flatMap]
  constructor
  · rintro ⟨u, huActive, href⟩
    have huCover := (mem_activeCoverVertices_iff.mp huActive).1
    rcases endpoints_of_mem_incidentOccurrences href with
      ⟨hoccurrence, hleft | hright⟩
    · rw [sourceEdgeForOccurrence_eq_getElem hoccurrence]
      exact ⟨hoccurrence, Or.inl ⟨hleft.1, hleft.2.symm ▸ huCover⟩⟩
    · rw [sourceEdgeForOccurrence_eq_getElem hoccurrence]
      exact ⟨hoccurrence, Or.inr ⟨hright.1, hright.2.2.symm ▸ huCover⟩⟩
  · rintro ⟨hoccurrence, hside⟩
    have hedgeMem : I.edges[ref.occurrence] ∈ I.edges :=
      List.getElem_mem hoccurrence
    have hedgeWellFormed := hwellFormed.2 _ hedgeMem
    rcases hside with ⟨hfalse, hcover⟩ | ⟨htrue, hcover⟩
    · rw [sourceEdgeForOccurrence_eq_getElem hoccurrence] at hcover
      have href : ref ∈ incidentOccurrences I I.edges[ref.occurrence].1 := by
        rcases ref with ⟨occurrence, side⟩
        simp only at hfalse
        subst side
        exact leftIncidentOccurrence_mem hoccurrence rfl
      refine ⟨I.edges[ref.occurrence].1, ?_, href⟩
      rw [mem_activeCoverVertices_iff]
      exact ⟨hcover, List.ne_nil_of_mem href⟩
    · rw [sourceEdgeForOccurrence_eq_getElem hoccurrence] at hcover
      have href : ref ∈ incidentOccurrences I I.edges[ref.occurrence].2 := by
        rcases ref with ⟨occurrence, side⟩
        simp only at htrue
        subst side
        apply rightIncidentOccurrence_mem hoccurrence
        · exact Nat.ne_of_lt hedgeWellFormed.1
        · rfl
      refine ⟨I.edges[ref.occurrence].2, ?_, href⟩
      rw [mem_activeCoverVertices_iff]
      exact ⟨hcover, List.ne_nil_of_mem href⟩

/-- Reindexing theorem: grouping selected incidences by cover vertex or by
source edge changes only their order. -/
theorem selectedCoverOccurrences_perm_coveredOccurrences
    {I : CliqueInstance} {cover : Finset Nat} (hwellFormed : I.WellFormed) :
    List.Perm (selectedCoverOccurrences I cover) (coveredOccurrences I cover) := by
  apply (List.perm_ext_iff_of_nodup
    (selectedCoverOccurrences_nodup I cover)
    (coveredOccurrences_nodup I cover)).2
  intro ref
  rw [mem_selectedCoverOccurrences_iff hwellFormed,
    mem_coveredOccurrences_iff]

end CLRS.Chapter34.HamiltonianCycleReduction
