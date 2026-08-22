import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsTermination
import Mathlib.Tactic

/-!
# Indexed occurrence rows: agreement with semantic enumeration

The machine-facing recursive row stream is identified with the public
row-major `indexedOccurrences` list paired with its zero-based vertex indices.
-/

noncomputable section

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Encode a semantic occurrence list using consecutive vertex indices. -/
def encodeIndexedOccurrenceListRowsFrom (vertex : Nat)
    (occurrences : List IndexedOccurrence) : List UnaryFrameSym :=
  (occurrences.zipIdx vertex).flatMap fun entry =>
    encodeUnaryFrame (indexedOccurrenceRowValues entry.2 entry.1) ++
      [UnaryFrameSym.frameEnd]

private theorem encodeIndexedOccurrenceListRowsFrom_append
    (vertex : Nat) (left right : List IndexedOccurrence) :
    encodeIndexedOccurrenceListRowsFrom vertex (left ++ right) =
      encodeIndexedOccurrenceListRowsFrom vertex left ++
        encodeIndexedOccurrenceListRowsFrom (vertex + left.length) right := by
  simp [encodeIndexedOccurrenceListRowsFrom, List.zipIdx_append,
    List.flatMap_append]

private theorem encodeIndexedClauseRowsFrom_eq_listFrom
    (vertex clauseIndex positionIndex : Nat) (clause : Clause) :
    encodeIndexedClauseRowsFrom vertex clauseIndex clause =
      encodeIndexedOccurrenceListRowsFrom vertex
        (indexedClauseOccurrencesFrom clauseIndex positionIndex clause) := by
  induction clause generalizing vertex positionIndex with
  | nil =>
      rfl
  | cons literal clause ih =>
      rw [encodeIndexedClauseRowsFrom, indexedClauseOccurrencesFrom]
      rw [ih (vertex + 1) (positionIndex + 1)]
      simp [encodeIndexedOccurrenceListRowsFrom,
        indexedOccurrenceRowValues, List.append_assoc]

private theorem encodeIndexedOccurrenceRowsFrom_eq_listFrom
    (vertex clauseIndex : Nat) (formula : CNF) :
    encodeIndexedOccurrenceRowsFrom vertex clauseIndex formula =
      encodeIndexedOccurrenceListRowsFrom vertex
        (indexedOccurrencesFrom clauseIndex formula) := by
  induction formula generalizing vertex clauseIndex with
  | nil => rfl
  | cons clause formula ih =>
      rw [encodeIndexedOccurrenceRowsFrom, indexedOccurrencesFrom,
        encodeIndexedOccurrenceListRowsFrom_append]
      unfold indexedClauseOccurrences
      rw [← encodeIndexedClauseRowsFrom_eq_listFrom vertex clauseIndex 0 clause]
      have hlength :
          (indexedClauseOccurrencesFrom clauseIndex 0 clause).length =
            clause.length := by
        simpa [indexedClauseOccurrences] using
          indexedClauseOccurrences_length clauseIndex clause
      rw [hlength]
      rw [ih]

/-- Public machine rows are exactly the rows of the semantic indexed
occurrence enumeration paired with vertices `0, ..., n-1`. -/
theorem encodeIndexedOccurrenceRows_eq_indexedOccurrences (formula : CNF) :
    encodeIndexedOccurrenceRows formula =
      (indexedOccurrences formula).zipIdx.flatMap fun entry =>
        encodeUnaryFrame (indexedOccurrenceRowValues entry.2 entry.1) ++
          [UnaryFrameSym.frameEnd] := by
  exact encodeIndexedOccurrenceRowsFrom_eq_listFrom 0 0 formula

end TMClique
end Turing
end Chapter34
end CLRS
