import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.OccurrenceRowsSimulation
import Mathlib.Tactic

/-!
# Indexed occurrence rows: clause simulation

The exact one-literal run is lifted to an arbitrary clause while preserving
the outer input suffix and both persistent counters.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Canonical graph-symbol descriptor of one literal occurrence. -/
def occurrenceLiteralDescriptor : Literal → List GraphSym
  | .pos index => .vertexMark :: .posMark :: .varMark ::
      List.replicate (index + 1) .endMark
  | .neg index => .vertexMark :: .negMark :: .varMark ::
      List.replicate (index + 1) .endMark

/-- Concatenated descriptors of one clause, excluding its clause marker. -/
def occurrenceClauseDescriptor (clause : Clause) : List GraphSym :=
  clause.flatMap occurrenceLiteralDescriptor

/-- A legal outer suffix cannot begin inside a unary variable run. -/
def ValidOccurrenceSuffix (symbols : List GraphSym) : Prop :=
  symbols.head? ≠ some .endMark

@[simp] theorem validOccurrenceSuffix_nil : ValidOccurrenceSuffix [] := by
  simp [ValidOccurrenceSuffix]

@[simp] theorem validOccurrenceSuffix_vertex (tail : List GraphSym) :
    ValidOccurrenceSuffix (.vertexMark :: tail) := by
  simp [ValidOccurrenceSuffix]

@[simp] theorem validOccurrenceSuffix_clause (tail : List GraphSym) :
    ValidOccurrenceSuffix (.clauseMark :: tail) := by
  simp [ValidOccurrenceSuffix]

private theorem occurrenceRows_relabel_replicate_end (count : Nat) :
    relabel (List.replicate count CNFSym.endMark) =
      List.replicate count GraphSym.endMark := by
  induction count with
  | zero => rfl
  | succ count ih => simp [List.replicate_succ, relabel, ih]

/-- Relabeling one encoded literal produces exactly its occurrence
descriptor. -/
theorem occurrenceLiteralDescriptor_eq_relabel_encLit (literal : Literal) :
    occurrenceLiteralDescriptor literal = relabel (encLit literal) := by
  cases literal <;>
    simp [occurrenceLiteralDescriptor, encLit, litSym, relabel,
      litIndex, occurrenceRows_relabel_replicate_end]

theorem occurrenceRows_relabel_append (left right : List CNFSym) :
    relabel (left ++ right) = relabel left ++ relabel right := by
  induction left with
  | nil => rfl
  | cons symbol left ih =>
      cases symbol <;> simp [relabel, ih]

/-- The descriptor list of a clause is the relabeling of its flattened
literal encodings. -/
theorem occurrenceClauseDescriptor_eq_relabel (clause : Clause) :
    occurrenceClauseDescriptor clause = relabel (clause.flatMap encLit) := by
  induction clause with
  | nil => rfl
  | cons literal clause ih =>
      simp only [occurrenceClauseDescriptor, List.flatMap_cons]
      rw [occurrenceRows_relabel_append, ← occurrenceLiteralDescriptor_eq_relabel_encLit,
        ← ih]
      rfl

/-- Whether the local literal parser must preserve a following boundary. -/
def occurrenceRowsHasBoundary (tail : List GraphSym) : Bool :=
  !tail.isEmpty

/-- Buffer value after consuming one complete literal. -/
def occurrenceRowsTailBuffer (tail : List GraphSym) : Option GraphSym :=
  tail.head?

/-- Unified exact literal run for every valid suffix. -/
def occurrenceRows_literalRun (vertex clause : Nat) (literal : Literal)
    (buffer : Option GraphSym) (test : Bool)
    (tail : List GraphSym) (htail : ValidOccurrenceSuffix tail)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg (.scan true) buffer test
        (occurrenceLiteralDescriptor literal ++ tail)
        output [] vertex clause 0)
      (some (occurrenceRowsCfg (.scan true)
        (occurrenceRowsTailBuffer tail) false tail
        ((encodeUnaryFrame
          (indexedOccurrenceRowValues vertex
            { clauseIndex := clause, positionIndex := 0, literal }) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output) []
        (vertex + 1) clause 0))
      (occurrenceRowsLiteralSteps vertex clause literal
        (occurrenceRowsHasBoundary tail)) := by
  cases tail with
  | nil =>
      cases literal with
      | pos index =>
          simpa [occurrenceLiteralDescriptor, occurrenceRowsTailBuffer,
            occurrenceRowsHasBoundary] using
            occurrenceRows_literalRun_empty vertex clause (.pos index)
              buffer test output
      | neg index =>
          simpa [occurrenceLiteralDescriptor, occurrenceRowsTailBuffer,
            occurrenceRowsHasBoundary] using
            occurrenceRows_literalRun_empty vertex clause (.neg index)
              buffer test output
  | cons boundary tail =>
      have hboundary : boundary ≠ GraphSym.endMark := by
        simpa [ValidOccurrenceSuffix] using htail
      cases literal with
      | pos index =>
          simpa [occurrenceLiteralDescriptor, occurrenceRowsTailBuffer,
            occurrenceRowsHasBoundary, List.append_assoc] using
            occurrenceRows_literalRun_boundary vertex clause (.pos index)
              boundary hboundary buffer test tail output
      | neg index =>
          simpa [occurrenceLiteralDescriptor, occurrenceRowsTailBuffer,
            occurrenceRowsHasBoundary, List.append_assoc] using
            occurrenceRows_literalRun_boundary vertex clause (.neg index)
              boundary hboundary buffer test tail output

/-- Exact accumulated cost for a clause in front of an outer suffix. -/
def occurrenceRowsClauseSteps : Nat → Nat → Clause → List GraphSym → Nat
  | _, _, [], _ => 0
  | vertex, clauseIndex, literal :: clause, suffix =>
      let tail := occurrenceClauseDescriptor clause ++ suffix
      occurrenceRowsLiteralSteps vertex clauseIndex literal
          (occurrenceRowsHasBoundary tail) +
        occurrenceRowsClauseSteps (vertex + 1) clauseIndex clause suffix

def occurrenceRowsClauseEndBuffer (clause : Clause)
    (suffix : List GraphSym) (buffer : Option GraphSym) : Option GraphSym :=
  if clause.isEmpty then buffer else occurrenceRowsTailBuffer suffix

def occurrenceRowsClauseEndTest (clause : Clause)
    (test : Bool) : Bool :=
  if clause.isEmpty then test else false

/-- Every occurrence of one clause becomes one marked four-field row. -/
def occurrenceRows_clauseRun (vertex clauseIndex : Nat) (clause : Clause)
    (buffer : Option GraphSym) (test : Bool)
    (suffix : List GraphSym) (hsuffix : ValidOccurrenceSuffix suffix)
    (output : List UnaryFrameSym) :
    EvalsToInTime (step occurrenceRowsRevProgram)
      (occurrenceRowsCfg (.scan true) buffer test
        (occurrenceClauseDescriptor clause ++ suffix)
        output [] vertex clauseIndex 0)
      (some (occurrenceRowsCfg (.scan true)
        (occurrenceRowsClauseEndBuffer clause suffix buffer)
        (occurrenceRowsClauseEndTest clause test) suffix
        ((encodeIndexedClauseRowsFrom vertex clauseIndex clause).reverse ++
          output) [] (vertex + clause.length) clauseIndex 0))
      (occurrenceRowsClauseSteps vertex clauseIndex clause suffix) := by
  induction clause generalizing vertex buffer test output with
  | nil =>
      exact ⟨⟨0, by simp [occurrenceClauseDescriptor,
        encodeIndexedClauseRowsFrom, occurrenceRowsClauseSteps,
        occurrenceRowsClauseEndBuffer, occurrenceRowsClauseEndTest]⟩,
        le_rfl⟩
  | cons literal clause ih =>
      let tail := occurrenceClauseDescriptor clause ++ suffix
      have htail : ValidOccurrenceSuffix tail := by
        cases clause with
        | nil => simpa [tail, occurrenceClauseDescriptor] using hsuffix
        | cons next rest =>
            cases next <;>
              simp [tail, occurrenceClauseDescriptor,
                occurrenceLiteralDescriptor, ValidOccurrenceSuffix]
      let first := occurrenceRows_literalRun vertex clauseIndex literal
        buffer test tail htail output
      let remaining := ih (vertex + 1)
        (occurrenceRowsTailBuffer tail) false
        ((encodeUnaryFrame
          (indexedOccurrenceRowValues vertex
            { clauseIndex, positionIndex := 0, literal }) ++
          [UnaryFrameSym.frameEnd]).reverse ++ output)
      let full := EvalsToInTime.trans (step occurrenceRowsRevProgram)
        (occurrenceRowsLiteralSteps vertex clauseIndex literal
          (occurrenceRowsHasBoundary tail))
        (occurrenceRowsClauseSteps (vertex + 1) clauseIndex clause suffix)
        _ _ _ first remaining
      cases clause <;>
        simpa [tail, occurrenceClauseDescriptor,
          encodeIndexedClauseRowsFrom, occurrenceRowsClauseSteps,
          occurrenceRowsClauseEndBuffer, occurrenceRowsClauseEndTest,
          List.reverse_append, List.append_assoc,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
