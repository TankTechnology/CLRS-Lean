import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CNFToClique
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.Instance

/-!
# The indexed occurrence graph as a general CLIQUE instance

Literal occurrences, rather than literal values, are the vertices of the
textbook reduction.  Clause and position indices therefore remain explicit;
in particular, repeated equal literals still produce distinct vertices.
-/

namespace CLRS
namespace Chapter34

/-- One literal position in a CNF formula. -/
structure IndexedOccurrence where
  clauseIndex : Nat
  positionIndex : Nat
  literal : Literal
  deriving DecidableEq, Repr

/-- Attach fixed clause and starting position indices to a clause suffix. -/
def indexedClauseOccurrencesFrom (clauseIndex : Nat) :
    Nat → Clause → List IndexedOccurrence
  | _, [] => []
  | positionIndex, literal :: clause =>
      { clauseIndex, positionIndex, literal } ::
        indexedClauseOccurrencesFrom clauseIndex (positionIndex + 1) clause

/-- Attach a fixed clause index and increasing zero-based positions to a clause. -/
def indexedClauseOccurrences (clauseIndex : Nat) (clause : Clause) :
    List IndexedOccurrence :=
  indexedClauseOccurrencesFrom clauseIndex 0 clause

/-- Row-major occurrence enumeration, starting at the supplied clause index. -/
def indexedOccurrencesFrom : Nat → CNF → List IndexedOccurrence
  | _, [] => []
  | clauseIndex, clause :: formula =>
      indexedClauseOccurrences clauseIndex clause ++
        indexedOccurrencesFrom (clauseIndex + 1) formula

/-- All literal positions of a CNF formula in row-major order. -/
def indexedOccurrences (formula : CNF) : List IndexedOccurrence :=
  indexedOccurrencesFrom 0 formula

/-- Look up the occurrence represented by a numeric graph vertex. -/
def indexedOccurrenceAt? (formula : CNF) (vertex : Nat) :
    Option IndexedOccurrence :=
  (indexedOccurrences formula)[vertex]?

/-- Every normalized pair of vertices below the supplied bound. -/
def normalizedPairs : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => normalizedPairs n ++ (List.range n).map fun u => (u, n)

/-- Two indexed occurrences form an occurrence-graph edge exactly when they
come from different clauses and are not complementary. -/
def IndexedOccurrence.Compatible (left right : IndexedOccurrence) : Prop :=
  left.clauseIndex ≠ right.clauseIndex ∧
    left.literal ≠ complement right.literal

instance (left right : IndexedOccurrence) :
    Decidable (left.Compatible right) := by
  unfold IndexedOccurrence.Compatible
  infer_instance

/-- The normalized numeric edge list of the occurrence graph. -/
def occurrenceCliqueEdges (formula : CNF) : List (Nat × Nat) :=
  (normalizedPairs (indexedOccurrences formula).length).filter fun edge =>
    match indexedOccurrenceAt? formula edge.1,
        indexedOccurrenceAt? formula edge.2 with
    | some left, some right => decide (left.Compatible right)
    | _, _ => false

/-- The textbook occurrence graph, represented as an honest numeric
graph-plus-{lit}`k` CLIQUE instance. -/
def occurrenceCliqueInstance (formula : CNF) : CliqueInstance where
  vertexCount := (indexedOccurrences formula).length
  targetSize := formula.length
  edges := occurrenceCliqueEdges formula

/-! ## Enumeration and pair-list invariants -/

@[simp]
theorem indexedClauseOccurrences_length (clauseIndex : Nat) (clause : Clause) :
    (indexedClauseOccurrences clauseIndex clause).length = clause.length := by
  unfold indexedClauseOccurrences
  generalize 0 = positionIndex
  induction clause generalizing positionIndex with
  | nil => simp [indexedClauseOccurrencesFrom]
  | cons literal clause ih =>
      simp [indexedClauseOccurrencesFrom, ih]

theorem normalizedPairs_mem_iff {n u v : Nat} :
    (u, v) ∈ normalizedPairs n ↔ u < v ∧ v < n := by
  induction n with
  | zero => simp [normalizedPairs]
  | succ n ih =>
      simp only [normalizedPairs, List.mem_append, ih, List.mem_map,
        List.mem_range]
      constructor
      · rintro (⟨huv, hvn⟩ | ⟨w, hwn, hpair⟩)
        · exact ⟨huv, Nat.lt_succ_of_lt hvn⟩
        · cases hpair
          exact ⟨hwn, by omega⟩
      · rintro ⟨huv, hvn⟩
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hvn) with hvn' | rfl
        · exact Or.inl ⟨huv, hvn'⟩
        · exact Or.inr ⟨u, huv, rfl⟩

theorem normalizedPairs_nodup (n : Nat) : (normalizedPairs n).Nodup := by
  induction n with
  | zero => simp [normalizedPairs]
  | succ n ih =>
      rw [normalizedPairs]
      apply List.Nodup.append ih
      · exact List.nodup_range.map fun _ _ h => congrArg Prod.fst h
      · intro pair hpair hnew
        have hold := (normalizedPairs_mem_iff.mp hpair).2
        rcases List.mem_map.mp hnew with ⟨u, _, rfl⟩
        exact (Nat.ne_of_lt hold) rfl

@[simp]
theorem indexedOccurrence_compatible_self (occurrence : IndexedOccurrence) :
    ¬ occurrence.Compatible occurrence := by
  simp [IndexedOccurrence.Compatible]

theorem complement_complement (literal : Literal) :
    complement (complement literal) = literal := by
  cases literal <;> rfl

theorem indexedOccurrence_compatible_comm (left right : IndexedOccurrence) :
    left.Compatible right ↔ right.Compatible left := by
  constructor <;> rintro ⟨hclause, hliteral⟩
  · refine ⟨Ne.symm hclause, ?_⟩
    intro h
    apply hliteral
    rw [← complement_complement left.literal, h]
  · refine ⟨Ne.symm hclause, ?_⟩
    intro h
    apply hliteral
    rw [← complement_complement right.literal, h]

/-! ## Edge and well-formedness theorems -/

theorem mem_occurrenceCliqueEdges_iff {formula : CNF} {u v : Nat} :
    (u, v) ∈ occurrenceCliqueEdges formula ↔
      u < v ∧
        ∃ left right,
          indexedOccurrenceAt? formula u = some left ∧
          indexedOccurrenceAt? formula v = some right ∧
          left.Compatible right := by
  simp only [occurrenceCliqueEdges, List.mem_filter, normalizedPairs_mem_iff]
  constructor
  · rintro ⟨⟨huv, _⟩, hcompatible⟩
    cases hleft : indexedOccurrenceAt? formula u with
    | none => simp [hleft] at hcompatible
    | some left =>
        cases hright : indexedOccurrenceAt? formula v with
        | none => simp [hleft, hright] at hcompatible
        | some right =>
            simp only [hleft, hright] at hcompatible
            exact ⟨huv, left, right, rfl, rfl,
              of_decide_eq_true hcompatible⟩
  · rintro ⟨huv, left, right, hleft, hright, hcompatible⟩
    have hrightBound : v < (indexedOccurrences formula).length :=
      List.getElem?_eq_some_iff.mp hright |>.1
    refine ⟨⟨huv, hrightBound⟩, ?_⟩
    simp [hleft, hright, hcompatible]

theorem occurrenceCliqueEdges_nodup (formula : CNF) :
    (occurrenceCliqueEdges formula).Nodup := by
  exact List.Nodup.filter _ (normalizedPairs_nodup _)

theorem occurrenceCliqueEdges_in_range {formula : CNF} {edge : Nat × Nat}
    (hedge : edge ∈ occurrenceCliqueEdges formula) :
    edge.1 < edge.2 ∧ edge.2 < (indexedOccurrences formula).length := by
  exact normalizedPairs_mem_iff.mp (List.mem_of_mem_filter hedge)

theorem formula_length_le_indexedOccurrences_length
    {formula : CNF} (hnonempty : ∀ clause ∈ formula, clause ≠ []) :
    formula.length ≤ (indexedOccurrences formula).length := by
  change formula.length ≤ (indexedOccurrencesFrom 0 formula).length
  generalize 0 = start
  induction formula generalizing start with
  | nil => simp [indexedOccurrencesFrom]
  | cons clause formula ih =>
      have hclausePos : 0 < clause.length :=
        List.length_pos_iff.mpr (hnonempty clause (by simp))
      have htail : formula.length ≤
          (indexedOccurrencesFrom (start + 1) formula).length := by
        apply ih
        intro c hc
        exact hnonempty c (by simp [hc])
      simp only [indexedOccurrencesFrom, List.length_append,
        indexedClauseOccurrences_length, List.length_cons]
      omega

/-- The occurrence instance is structurally well formed whenever every clause
has a literal.  This is the exact required hypothesis: the project's
at-most-three-literal convention intentionally permits empty clauses. -/
theorem occurrenceCliqueInstance_wellFormed {formula : CNF}
    (hnonempty : ∀ clause ∈ formula, clause ≠ []) :
    (occurrenceCliqueInstance formula).WellFormed := by
  refine ⟨formula_length_le_indexedOccurrences_length hnonempty,
    occurrenceCliqueEdges_nodup formula, ?_⟩
  intro edge hedge
  exact occurrenceCliqueEdges_in_range hedge

/-- Below the diagonal, occurrence-graph adjacency is exactly compatibility
of the two indexed literal positions. -/
theorem occurrenceCliqueInstance_adj_iff_of_lt {formula : CNF} {u v : Nat}
    (huv : u < v) :
    (occurrenceCliqueInstance formula).Adj u v ↔
      ∃ left right,
        indexedOccurrenceAt? formula u = some left ∧
        indexedOccurrenceAt? formula v = some right ∧
        left.Compatible right := by
  rw [CliqueInstance.adj_iff_of_lt _ huv]
  exact mem_occurrenceCliqueEdges_iff.trans (and_iff_right huv)

/-- Adjacency has the same indexed-occurrence meaning in either vertex order. -/
theorem occurrenceCliqueInstance_adj_iff {formula : CNF} {u v : Nat} :
    (occurrenceCliqueInstance formula).Adj u v ↔
      ∃ left right,
        indexedOccurrenceAt? formula u = some left ∧
        indexedOccurrenceAt? formula v = some right ∧
        left.Compatible right := by
  rcases Nat.lt_trichotomy u v with huv | rfl | hvu
  · exact occurrenceCliqueInstance_adj_iff_of_lt huv
  · constructor
    · exact False.elim ∘ CliqueInstance.not_adj_self _ _
    · rintro ⟨left, right, hleft, hright, hcompatible⟩
      have : left = right := Option.some.inj (hleft.symm.trans hright)
      subst right
      exact False.elim ((indexedOccurrence_compatible_self left) hcompatible)
  · rw [CliqueInstance.adj_comm]
    rw [occurrenceCliqueInstance_adj_iff_of_lt hvu]
    constructor
    · rintro ⟨right, left, hright, hleft, hcompatible⟩
      exact ⟨left, right, hleft, hright,
        (indexedOccurrence_compatible_comm right left).mp hcompatible⟩
    · rintro ⟨left, right, hleft, hright, hcompatible⟩
      exact ⟨right, left, hright, hleft,
        (indexedOccurrence_compatible_comm left right).mp hcompatible⟩

end Chapter34
end CLRS
