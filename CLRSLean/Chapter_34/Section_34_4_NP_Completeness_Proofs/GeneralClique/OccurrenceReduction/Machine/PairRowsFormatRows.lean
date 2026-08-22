import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.PairRowsFormatSimulation
import Mathlib.Tactic

/-!
# Formatting triangular pair rows: row simulation

This layer lifts the exact one-field simulation to one complete row and then
to the entire canonical triangular family.  Buffer details that no later
phase observes are hidden from the all-rows interface.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Exact accumulated cost of formatting a list of lower endpoints. -/
def pairRowsFormatValuesSteps (values : List Nat) (upper : Nat) : Nat :=
  (values.map fun lower => pairRowsFormatFieldSteps lower upper).sum

private def pairRowsFormatEndBuffer (values : List Nat)
    (buffer : Option UnaryFrameSym) : Option UnaryFrameSym :=
  if values.isEmpty then buffer else some .separator

private def pairRowsFormatEndTest (values : List Nat) (test : Bool) : Bool :=
  if values.isEmpty then test else false

/-- Every unary field in one row is formatted, in order, into a reverse-output
edge record. -/
def pairRowsFormat_valuesRun (values : List Nat) (upper : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step pairRowsFormatRevProgram)
      (pairRowsFormatCfg .scan buffer test
        (encodeUnaryFrame values ++ tail) output upper 0)
      (some (pairRowsFormatCfg .scan
        (pairRowsFormatEndBuffer values buffer)
        (pairRowsFormatEndTest values test) tail
        ((values.flatMap fun lower => encodeCliqueEdge (lower, upper)).reverse ++
          output) upper 0))
      (pairRowsFormatValuesSteps values upper) := by
  induction values generalizing buffer test output with
  | nil =>
      exact ⟨⟨0, by simp [encodeUnaryFrame, pairRowsFormatEndBuffer,
        pairRowsFormatEndTest]⟩, le_rfl⟩
  | cons lower values ih =>
      let first := pairRowsFormat_fieldRun lower upper buffer test
        (encodeUnaryFrame values ++ tail) output
      let remaining := ih (some .separator) false
        ((encodeCliqueEdge (lower, upper)).reverse ++ output)
      let full := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        (pairRowsFormatFieldSteps lower upper)
        (pairRowsFormatValuesSteps values upper) _ _ _ first remaining
      simpa [encodeUnaryFrame, pairRowsFormatValuesSteps,
        pairRowsFormatEndBuffer, pairRowsFormatEndTest,
        List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- Exact cost of one row, including its row-end marker and counter advance. -/
def pairRowsFormatRowSteps (upper : Nat) : Nat :=
  pairRowsFormatValuesSteps (List.range upper) upper + 2

/-- One complete triangular row is formatted and advances the upper-endpoint
counter exactly once. -/
def pairRowsFormat_rowRun (upper : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    EvalsToInTime (step pairRowsFormatRevProgram)
      (pairRowsFormatCfg .scan buffer test
        (encodeUnaryFrame (List.range upper) ++ .frameEnd :: tail)
        output upper 0)
      (some (pairRowsFormatCfg .scan (some .frameEnd)
        (pairRowsFormatEndTest (List.range upper) test) tail
        (((List.range upper).flatMap fun lower =>
          encodeCliqueEdge (lower, upper)).reverse ++ output)
        (upper + 1) 0))
      (pairRowsFormatRowSteps upper) := by
  let fields := pairRowsFormat_valuesRun (List.range upper) upper
    buffer test (.frameEnd :: tail) output
  let afterFields := pairRowsFormatCfg .scan
    (pairRowsFormatEndBuffer (List.range upper) buffer)
    (pairRowsFormatEndTest (List.range upper) test)
    (.frameEnd :: tail)
    (((List.range upper).flatMap fun lower =>
      encodeCliqueEdge (lower, upper)).reverse ++ output) upper 0
  let afterRow := pairRowsFormatCfg .scan (some .frameEnd)
    (pairRowsFormatEndTest (List.range upper) test) tail
    (((List.range upper).flatMap fun lower =>
      encodeCliqueEdge (lower, upper)).reverse ++ output) (upper + 1) 0
  have advance : EvalsToInTime (step pairRowsFormatRevProgram)
      afterFields (some afterRow) 2 := ⟨⟨2, rfl⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step pairRowsFormatRevProgram)
    (pairRowsFormatValuesSteps (List.range upper) upper) 2
    _ _ _ fields advance
  simpa [afterFields, afterRow, pairRowsFormatRowSteps,
    pairRowsFormatEndBuffer, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using full

/-- Candidate edges in a consecutive interval of rows. -/
def pairRowsFormatEdgesFrom : Nat → Nat → List CliqueSym
  | _, 0 => []
  | upper, count + 1 =>
      (List.range upper).flatMap (fun lower =>
        encodeCliqueEdge (lower, upper)) ++
      pairRowsFormatEdgesFrom (upper + 1) count

/-- Exact accumulated cost of a consecutive interval of rows. -/
def pairRowsFormatRowsSteps : Nat → Nat → Nat
  | _, 0 => 0
  | upper, count + 1 =>
      pairRowsFormatRowSteps upper +
        pairRowsFormatRowsSteps (upper + 1) count

/-- Format all remaining canonical rows.  The final buffer and test-bit values
are deliberately hidden because cleanup does not inspect them. -/
def pairRowsFormat_rowsRun (upper count : Nat)
    (buffer : Option UnaryFrameSym) (test : Bool)
    (tail : List UnaryFrameSym) (output : List CliqueSym) :
    Σ finalBuffer, Σ finalTest,
      EvalsToInTime (step pairRowsFormatRevProgram)
        (pairRowsFormatCfg .scan buffer test
          (unaryFrameAffinePrefixRowsStreamFrom upper
            (encodeUnaryFrame (List.range upper)) count ++ tail)
          output upper 0)
        (some (pairRowsFormatCfg .scan finalBuffer finalTest tail
          ((pairRowsFormatEdgesFrom upper count).reverse ++ output)
          (upper + count) 0))
        (pairRowsFormatRowsSteps upper count) := by
  induction count generalizing upper buffer test output with
  | zero =>
      refine ⟨buffer, test, ?_⟩
      exact ⟨⟨0, by simp [unaryFrameAffinePrefixRowsStreamFrom,
        pairRowsFormatEdgesFrom]⟩, le_rfl⟩
  | succ count ih =>
      let restInput := unaryFrameAffinePrefixRowsStreamFrom (upper + 1)
        (encodeUnaryFrame (List.range (upper + 1))) count
      let first := pairRowsFormat_rowRun upper buffer test
        (restInput ++ tail) output
      rcases ih (upper + 1) (some .frameEnd)
          (pairRowsFormatEndTest (List.range upper) test)
          (((List.range upper).flatMap fun lower =>
            encodeCliqueEdge (lower, upper)).reverse ++ output) with
        ⟨finalBuffer, finalTest, remaining⟩
      refine ⟨finalBuffer, finalTest, ?_⟩
      let full := EvalsToInTime.trans (step pairRowsFormatRevProgram)
        (pairRowsFormatRowSteps upper)
        (pairRowsFormatRowsSteps (upper + 1) count)
        _ _ _ first remaining
      simpa [unaryFrameAffinePrefixRowsStreamFrom, restInput,
        encodeUnaryFrame, List.range_succ, pairRowsFormatEdgesFrom,
        pairRowsFormatRowsSteps, List.reverse_append, List.append_assoc,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

/-- The recursive edge stream covers exactly a consecutive interval of upper
endpoints. -/
theorem pairRowsFormatEdgesFrom_eq_range' (upper count : Nat) :
    pairRowsFormatEdgesFrom upper count =
      (List.range' upper count).flatMap fun current =>
        (List.range current).flatMap fun lower =>
          encodeCliqueEdge (lower, current) := by
  induction count generalizing upper with
  | zero => rfl
  | succ count ih =>
      simp [pairRowsFormatEdgesFrom, List.range'_succ, ih]

/-- The recursive edge stream from row zero is the public complete-pair
stream. -/
theorem pairRowsFormatEdgesFrom_zero (count : Nat) :
    pairRowsFormatEdgesFrom 0 count = completePairEdgeStream count := by
  rw [pairRowsFormatEdgesFrom_eq_range']
  unfold completePairEdgeStream
  rw [List.range_eq_range']

end TMClique
end Turing
end Chapter34
end CLRS
