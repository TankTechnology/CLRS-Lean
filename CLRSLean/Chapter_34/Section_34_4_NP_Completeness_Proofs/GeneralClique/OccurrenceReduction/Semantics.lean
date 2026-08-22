import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Instance

/-!
# Semantics of the indexed occurrence reduction

This module bridges the existing textbook occurrence proof to the numeric
vertices of a genuine graph-plus-{lit}`k` CLIQUE instance.  Both directions
use exact row-major lookup witnesses, so repeated literal values are never
silently identified as positions.
-/

namespace CLRS
namespace Chapter34

/-! ## Row-major lookup facts -/

theorem indexedClauseOccurrencesFrom_fields_of_mem
    {clauseIndex positionIndex : Nat} {clause : Clause}
    {occurrence : IndexedOccurrence}
    (hmem : occurrence ∈
      indexedClauseOccurrencesFrom clauseIndex positionIndex clause) :
    occurrence.clauseIndex = clauseIndex ∧ occurrence.literal ∈ clause := by
  induction clause generalizing positionIndex with
  | nil => simp [indexedClauseOccurrencesFrom] at hmem
  | cons literal clause ih =>
      simp only [indexedClauseOccurrencesFrom, List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨rfl, by simp⟩
      · rcases ih hmem with ⟨hclause, hliteral⟩
        exact ⟨hclause, by simp [hliteral]⟩

theorem exists_mem_indexedClauseOccurrencesFrom_of_mem
    {clauseIndex positionIndex : Nat} {clause : Clause} {literal : Literal}
    (hmem : literal ∈ clause) :
    ∃ occurrence ∈ indexedClauseOccurrencesFrom clauseIndex positionIndex clause,
      occurrence.clauseIndex = clauseIndex ∧ occurrence.literal = literal := by
  induction clause generalizing positionIndex with
  | nil => simp at hmem
  | cons head clause ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨{ clauseIndex, positionIndex, literal },
          by simp [indexedClauseOccurrencesFrom]⟩
      · rcases ih (positionIndex := positionIndex + 1) hmem with
          ⟨occurrence, hoccurrence, hclause, hliteral⟩
        exact ⟨occurrence, by simp [indexedClauseOccurrencesFrom, hoccurrence],
          hclause, hliteral⟩

theorem indexedOccurrencesFrom_fields_of_mem
    {start : Nat} {formula : CNF} {occurrence : IndexedOccurrence}
    (hmem : occurrence ∈ indexedOccurrencesFrom start formula) :
    ∃ clauseIndex,
      clauseIndex < formula.length ∧
        occurrence.clauseIndex = start + clauseIndex ∧
        occurrence.literal ∈ clauseAt formula clauseIndex := by
  induction formula generalizing start with
  | nil => simp [indexedOccurrencesFrom] at hmem
  | cons clause formula ih =>
      simp only [indexedOccurrencesFrom, List.mem_append] at hmem
      rcases hmem with hhead | htail
      · rcases indexedClauseOccurrencesFrom_fields_of_mem hhead with
          ⟨hclause, hliteral⟩
        refine ⟨0, by simp, ?_, ?_⟩
        · simpa using hclause
        · simpa [clauseAt] using hliteral
      · rcases ih htail with ⟨clauseIndex, hindex, hclause, hliteral⟩
        refine ⟨clauseIndex + 1, by simp [hindex], ?_, ?_⟩
        · omega
        · simpa [clauseAt] using hliteral

theorem exists_mem_indexedOccurrencesFrom_of_mem_clauseAt
    {start : Nat} {formula : CNF} {clauseIndex : Nat} {literal : Literal}
    (hindex : clauseIndex < formula.length)
    (hmem : literal ∈ clauseAt formula clauseIndex) :
    ∃ occurrence ∈ indexedOccurrencesFrom start formula,
      occurrence.clauseIndex = start + clauseIndex ∧
        occurrence.literal = literal := by
  induction formula generalizing start clauseIndex with
  | nil => simp at hindex
  | cons clause formula ih =>
      cases clauseIndex with
      | zero =>
          have hhead : literal ∈ clause := by
            simpa [clauseAt] using hmem
          rcases exists_mem_indexedClauseOccurrencesFrom_of_mem
              (clauseIndex := start) (positionIndex := 0) hhead with
            ⟨occurrence, hoccurrence, hclause, hliteral⟩
          refine ⟨occurrence, ?_, ?_, hliteral⟩
          · simp [indexedOccurrencesFrom, indexedClauseOccurrences,
              hoccurrence]
          · simpa using hclause
      | succ clauseIndex =>
          have hindex' : clauseIndex < formula.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hindex
          have htail : literal ∈ clauseAt formula clauseIndex := by
            simpa [clauseAt] using hmem
          rcases ih (start := start + 1) hindex' htail with
            ⟨occurrence, hoccurrence, hclause, hliteral⟩
          refine ⟨occurrence, by simp [indexedOccurrencesFrom, hoccurrence], ?_,
            hliteral⟩
          omega

/-- A successful numeric lookup denotes a valid old-style occurrence. -/
theorem indexedOccurrenceAt?_fields {formula : CNF} {vertex : Nat}
    {occurrence : IndexedOccurrence}
    (hlookup : indexedOccurrenceAt? formula vertex = some occurrence) :
    occurrence.clauseIndex < formula.length ∧
      occurrence.literal ∈ clauseAt formula occurrence.clauseIndex := by
  have hmem : occurrence ∈ indexedOccurrences formula :=
    List.mem_iff_getElem?.mpr ⟨vertex, hlookup⟩
  rcases indexedOccurrencesFrom_fields_of_mem hmem with
    ⟨clauseIndex, hindex, hclause, hliteral⟩
  have hclause' : occurrence.clauseIndex = clauseIndex := by
    simpa [indexedOccurrences] using hclause
  subst clauseIndex
  exact ⟨hindex, hliteral⟩

/-- Every valid old-style occurrence has at least one numeric position. -/
theorem exists_indexedOccurrenceAt?_of_validOccurrence {formula : CNF}
    {occurrence : Occurrence}
    (hvalid : occurrence.2 ∈ clauseAt formula occurrence.1) :
    ∃ vertex indexed,
      indexedOccurrenceAt? formula vertex = some indexed ∧
        indexed.clauseIndex = occurrence.1 ∧
        indexed.literal = occurrence.2 := by
  have hindex := occurrence_clauseIndex_lt hvalid
  rcases exists_mem_indexedOccurrencesFrom_of_mem_clauseAt
      (start := 0) hindex hvalid with
    ⟨indexed, hmem, hclause, hliteral⟩
  rcases List.mem_iff_getElem?.mp hmem with ⟨vertex, hlookup⟩
  exact ⟨vertex, indexed, hlookup, by simpa using hclause, hliteral⟩

/-! ## Witness maps -/

/-- Forget the position index of a numeric occurrence. -/
def IndexedOccurrence.toOccurrence (occurrence : IndexedOccurrence) : Occurrence :=
  (occurrence.clauseIndex, occurrence.literal)

/-- The old-style occurrence denoted by a numeric vertex, with an irrelevant
default outside the vertex range. -/
def occurrenceAtVertex (formula : CNF) (vertex : Nat) : Occurrence :=
  match indexedOccurrenceAt? formula vertex with
  | some occurrence => occurrence.toOccurrence
  | none => (0, Literal.pos 0)

theorem occurrenceAtVertex_eq_of_lookup {formula : CNF} {vertex : Nat}
    {occurrence : IndexedOccurrence}
    (hlookup : indexedOccurrenceAt? formula vertex = some occurrence) :
    occurrenceAtVertex formula vertex = occurrence.toOccurrence := by
  simp [occurrenceAtVertex, hlookup]

noncomputable def vertexOfOccurrence (formula : CNF)
    (occurrence : Occurrence) : Nat :=
  if hvalid : occurrence.2 ∈ clauseAt formula occurrence.1 then
    Classical.choose (exists_indexedOccurrenceAt?_of_validOccurrence hvalid)
  else 0

theorem vertexOfOccurrence_spec {formula : CNF} {occurrence : Occurrence}
    (hvalid : occurrence.2 ∈ clauseAt formula occurrence.1) :
    ∃ indexed,
      indexedOccurrenceAt? formula (vertexOfOccurrence formula occurrence) =
          some indexed ∧
        indexed.clauseIndex = occurrence.1 ∧
        indexed.literal = occurrence.2 := by
  rw [vertexOfOccurrence, dif_pos hvalid]
  exact Classical.choose_spec
    (exists_indexedOccurrenceAt?_of_validOccurrence hvalid)

theorem vertexOfOccurrence_injectiveOn {formula : CNF}
    {vertices : Finset Occurrence}
    (hvalid : ∀ occurrence ∈ vertices,
      occurrence.2 ∈ clauseAt formula occurrence.1) :
    Set.InjOn (vertexOfOccurrence formula) (↑vertices : Set Occurrence) := by
  intro left hleft right hright heq
  rcases vertexOfOccurrence_spec (hvalid left hleft) with
    ⟨leftIndexed, hleftLookup, hleftClause, hleftLiteral⟩
  rcases vertexOfOccurrence_spec (hvalid right hright) with
    ⟨rightIndexed, hrightLookup, hrightClause, hrightLiteral⟩
  rw [heq, hrightLookup] at hleftLookup
  have hindexed : leftIndexed = rightIndexed :=
    Option.some.inj hleftLookup.symm
  apply Prod.ext
  · simpa [hleftClause, hrightClause] using
      congrArg IndexedOccurrence.clauseIndex hindexed
  · simpa [hleftLiteral, hrightLiteral] using
      congrArg IndexedOccurrence.literal hindexed

/-! ## Equivalence of the two clique presentations -/

theorem hasCliqueOn_implies_occurrenceCliqueInstance {formula : CNF}
    (hclique : HasCliqueOn formula formula.length) :
    (occurrenceCliqueInstance formula).HasClique := by
  rcases hclique with ⟨vertices, hcard, hvalid, hadj⟩
  let numericVertices := vertices.image (vertexOfOccurrence formula)
  refine ⟨numericVertices, ?_, ?_, ?_⟩
  · dsimp [numericVertices]
    rw [Finset.card_image_of_injOn
      (vertexOfOccurrence_injectiveOn hvalid), hcard]
    rfl
  · intro vertex hvertex
    rcases Finset.mem_image.mp hvertex with
      ⟨occurrence, hoccurrence, rfl⟩
    rcases vertexOfOccurrence_spec (hvalid occurrence hoccurrence) with
      ⟨indexed, hlookup, _, _⟩
    exact List.getElem?_eq_some_iff.mp hlookup |>.1
  · intro left hleft right hright hne
    rcases Finset.mem_image.mp hleft with
      ⟨leftOccurrence, hleftOccurrence, hleftEq⟩
    rcases Finset.mem_image.mp hright with
      ⟨rightOccurrence, hrightOccurrence, hrightEq⟩
    have holdNe : leftOccurrence ≠ rightOccurrence := by
      intro heq
      apply hne
      subst rightOccurrence
      exact hleftEq.symm.trans hrightEq
    have holdAdj := hadj hleftOccurrence hrightOccurrence holdNe
    rcases vertexOfOccurrence_spec
        (hvalid leftOccurrence hleftOccurrence) with
      ⟨leftIndexed, hleftLookup, hleftClause, hleftLiteral⟩
    rcases vertexOfOccurrence_spec
        (hvalid rightOccurrence hrightOccurrence) with
      ⟨rightIndexed, hrightLookup, hrightClause, hrightLiteral⟩
    rw [← hleftEq, ← hrightEq]
    apply occurrenceCliqueInstance_adj_iff.mpr
    refine ⟨leftIndexed, rightIndexed, hleftLookup, hrightLookup, ?_⟩
    exact ⟨by simpa [hleftClause, hrightClause] using holdAdj.1,
      by simpa [hleftLiteral, hrightLiteral] using holdAdj.2⟩

theorem occurrenceAtVertex_injectiveOn {formula : CNF}
    {vertices : Finset Nat}
    (hadj : ∀ u ∈ vertices, ∀ v ∈ vertices, u ≠ v →
      (occurrenceCliqueInstance formula).Adj u v) :
    Set.InjOn (occurrenceAtVertex formula) (↑vertices : Set Nat) := by
  intro left hleft right hright heq
  by_contra hne
  rcases occurrenceCliqueInstance_adj_iff.mp
      (hadj left hleft right hright hne) with
    ⟨leftIndexed, rightIndexed, hleftLookup, hrightLookup, hcompatible⟩
  rw [occurrenceAtVertex_eq_of_lookup hleftLookup,
    occurrenceAtVertex_eq_of_lookup hrightLookup] at heq
  exact hcompatible.1 (congrArg Prod.fst heq)

theorem occurrenceCliqueInstance_implies_hasCliqueOn {formula : CNF}
    (hclique : (occurrenceCliqueInstance formula).HasClique) :
    HasCliqueOn formula formula.length := by
  rcases hclique with ⟨vertices, hcard, hbound, hadj⟩
  let occurrenceVertices := vertices.image (occurrenceAtVertex formula)
  refine ⟨occurrenceVertices, ?_, ?_, ?_⟩
  · dsimp [occurrenceVertices]
    rw [Finset.card_image_of_injOn
      (occurrenceAtVertex_injectiveOn hadj), hcard]
    rfl
  · intro occurrence hoccurrence
    rcases Finset.mem_image.mp hoccurrence with ⟨vertex, hvertex, rfl⟩
    have hvertexBound := hbound vertex hvertex
    have hlookup : indexedOccurrenceAt? formula vertex = some
        ((indexedOccurrences formula)[vertex]'hvertexBound) := by
      exact List.getElem?_eq_getElem hvertexBound
    rw [occurrenceAtVertex_eq_of_lookup hlookup]
    exact (indexedOccurrenceAt?_fields hlookup).2
  · intro left hleft right hright hne
    rcases Finset.mem_image.mp hleft with
      ⟨leftVertex, hleftVertex, hleftEq⟩
    rcases Finset.mem_image.mp hright with
      ⟨rightVertex, hrightVertex, hrightEq⟩
    have hvertexNe : leftVertex ≠ rightVertex := by
      intro heq
      apply hne
      subst rightVertex
      exact hleftEq.symm.trans hrightEq
    rcases occurrenceCliqueInstance_adj_iff.mp
        (hadj leftVertex hleftVertex rightVertex hrightVertex hvertexNe) with
      ⟨leftIndexed, rightIndexed, hleftLookup, hrightLookup, hcompatible⟩
    rw [occurrenceAtVertex_eq_of_lookup hleftLookup] at hleftEq
    rw [occurrenceAtVertex_eq_of_lookup hrightLookup] at hrightEq
    subst left
    subst right
    exact hcompatible

/-- The old occurrence-set presentation and the honest numeric graph instance
have exactly the same cliques of the textbook target size. -/
theorem hasCliqueOn_iff_occurrenceCliqueInstance (formula : CNF) :
    HasCliqueOn formula formula.length ↔
      (occurrenceCliqueInstance formula).HasClique :=
  ⟨hasCliqueOn_implies_occurrenceCliqueInstance,
    occurrenceCliqueInstance_implies_hasCliqueOn⟩

/-- Textbook 3-CNF-SAT to CLIQUE semantic correctness on the honest numeric
graph representation.  The equivalence itself holds for every CNF; the
at-most-three hypothesis is needed only by the reduction's source language. -/
theorem cnfSatisfiable_iff_occurrenceCliqueInstance (formula : CNF) :
    CnfSatisfiable formula ↔
      (occurrenceCliqueInstance formula).HasClique := by
  rw [cnfSatisfiable_iff_hasClique]
  exact hasCliqueOn_iff_occurrenceCliqueInstance formula

/-- A satisfiable formula has no empty clause, so its occurrence instance is
also structurally well formed. -/
theorem occurrenceCliqueInstance_wellFormed_of_cnfSatisfiable {formula : CNF}
    (hsatisfiable : CnfSatisfiable formula) :
    (occurrenceCliqueInstance formula).WellFormed := by
  rcases hsatisfiable with ⟨assignment, hassignment⟩
  apply occurrenceCliqueInstance_wellFormed
  intro clause hclause hempty
  subst clause
  have := hassignment [] hclause
  simp [evalClause] at this

end Chapter34
end CLRS
