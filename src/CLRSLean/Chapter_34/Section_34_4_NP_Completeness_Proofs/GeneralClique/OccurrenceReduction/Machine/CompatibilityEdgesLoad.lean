import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralClique.OccurrenceReduction.Machine.CompatibilityEdgesCore
import Mathlib.Tactic

/-!
# Occurrence compatibility edges: row loading

This file proves that the first controller phase reverses the order of a
delimiter-safe row family while retaining the forward symbol order inside
each row.  The theorem is generic in the already occupied output and work
stack, which is the invariant needed by the outer compatibility loop.
-/

noncomputable section

open StateTransition

namespace CLRS
namespace Chapter34
namespace Turing
namespace TMClique

open PolyBuilder

/-- Physical row attached to one row-major indexed occurrence. -/
def encodeIndexedOccurrenceEntry
    (entry : IndexedOccurrence × Nat) : List UnaryFrameSym :=
  encodeUnaryFrame (indexedOccurrenceRowValues entry.2 entry.1) ++ [.frameEnd]

/-- Physical family attached to an explicit indexed-occurrence enumeration. -/
def encodeIndexedOccurrenceEntries
    (entries : List (IndexedOccurrence × Nat)) : List UnaryFrameSym :=
  entries.flatMap encodeIndexedOccurrenceEntry

/-- Canonical occurrence rows are the explicit zipped-entry family. -/
theorem encodeIndexedOccurrenceEntries_zipIdx (formula : CNF) :
    encodeIndexedOccurrenceEntries (indexedOccurrences formula).zipIdx =
      encodeIndexedOccurrenceRows formula := by
  rw [encodeIndexedOccurrenceRows_eq_indexedOccurrences]
  rfl

private theorem encodeUnaryFrame_frameEnd_free (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values, symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  induction values with
  | nil => simp [encodeUnaryFrame] at hsymbol
  | cons value values ih =>
      simp only [encodeUnaryFrame, List.flatMap_cons, List.mem_append] at hsymbol
      rcases hsymbol with hsymbol | hsymbol
      · simp [encodeUnaryFrameBlock] at hsymbol
        rcases hsymbol with ⟨_, rfl⟩ | rfl <;> decide
      · exact ih hsymbol

private def compatibilityEdgesLoadLastBuffer
    (initial : Option UnaryFrameSym) (symbols : List UnaryFrameSym) :
    Option UnaryFrameSym :=
  symbols.foldl (fun _ symbol => some symbol) initial

private def compatibilityEdgesFlushLastBuffer
    (_initial : Option UnaryFrameSym) (_symbols : List UnaryFrameSym) :
    Option UnaryFrameSym :=
  none

private theorem compatibilityEdges_loadSymbols_eval
    (symbols tail work₁ work₂ : List UnaryFrameSym)
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCount : Nat)
    (hfree : ∀ symbol ∈ symbols,
      symbol ≠ UnaryFrameSym.frameEnd) :
    (flip Option.bind (step compatibilityEdgesProgram))^[2 * symbols.length]
      (some (compatibilityEdgesCfg .load buffer₁ buffer₂ test
        (symbols ++ tail) output work₁ work₂ upper clause variableCount)) =
      some (compatibilityEdgesCfg .load
        (compatibilityEdgesLoadLastBuffer buffer₁ symbols) buffer₂ test
        tail output work₁ (symbols.reverse ++ work₂)
        upper clause variableCount) := by
  induction symbols generalizing buffer₁ work₂ with
  | nil => rfl
  | cons symbol symbols ih =>
      have hsymbol : symbol ≠ UnaryFrameSym.frameEnd :=
        hfree symbol (by simp)
      have htail : ∀ value ∈ symbols,
          value ≠ UnaryFrameSym.frameEnd := by
        intro value hvalue
        exact hfree value (by simp [hvalue])
      rw [show 2 * (symbol :: symbols).length =
          2 * symbols.length + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step compatibilityEdgesProgram
          (compatibilityEdgesCfg .load buffer₁ buffer₂ test
            (symbol :: symbols ++ tail) output work₁ work₂
            upper clause variableCount) =
          some (compatibilityEdgesCfg (.loadPush symbol) (some symbol)
            buffer₂ test (symbols ++ tail) output work₁ work₂
            upper clause variableCount) by
        simp [step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp]]
      simp only [Option.bind_some]
      rw [show step compatibilityEdgesProgram
          (compatibilityEdgesCfg (.loadPush symbol) (some symbol)
            buffer₂ test (symbols ++ tail) output work₁ work₂
            upper clause variableCount) =
          some (compatibilityEdgesCfg .load (some symbol) buffer₂ test
            (symbols ++ tail) output work₁ (symbol :: work₂)
            upper clause variableCount) by
        simp [step, compatibilityEdgesProgram, compatibilityEdgesCfg,
          stepOp, hsymbol]]
      have hrun := ih (buffer₁ := some symbol) (work₂ := symbol :: work₂) htail
      simpa [compatibilityEdgesLoadLastBuffer, List.reverse_cons,
        List.append_assoc] using hrun

private theorem compatibilityEdges_flush_eval
    (symbols input work₁ : List UnaryFrameSym)
    (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCount : Nat) :
    (flip Option.bind (step compatibilityEdgesProgram))^[symbols.length + 1]
      (some (compatibilityEdgesCfg .flushRow buffer₁ buffer₂ test
        input output work₁ symbols upper clause variableCount)) =
      some (compatibilityEdgesCfg .load buffer₁
        (compatibilityEdgesFlushLastBuffer buffer₂ symbols) test
        input output (symbols.reverse ++ work₁) []
        upper clause variableCount) := by
  induction symbols generalizing buffer₂ work₁ with
  | nil =>
      simp only [List.length_nil, zero_add, Function.iterate_one, flip,
        Option.bind_some, List.reverse_nil, List.nil_append,
        compatibilityEdgesFlushLastBuffer]
      simp [step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]
  | cons symbol symbols ih =>
      rw [show (symbol :: symbols).length + 1 =
          (symbols.length + 1) + 1 by simp,
        Function.iterate_succ_apply]
      simp only [flip, Option.bind_some]
      rw [show step compatibilityEdgesProgram
          (compatibilityEdgesCfg .flushRow buffer₁ buffer₂ test
            input output work₁ (symbol :: symbols)
            upper clause variableCount) =
          some (compatibilityEdgesCfg .flushRow buffer₁ (some symbol) test
            input output (symbol :: work₁) symbols
            upper clause variableCount) by
        simp [step, compatibilityEdgesProgram, compatibilityEdgesCfg, stepOp]]
      simpa [compatibilityEdgesFlushLastBuffer, List.reverse_cons,
        List.append_assoc] using
        (ih (buffer₂ := some symbol) (work₁ := symbol :: work₁))

/-- Exact cost of loading one complete physical row. -/
def compatibilityEdgesLoadRowSteps
    (entry : IndexedOccurrence × Nat) : Nat :=
  3 * (encodeIndexedOccurrenceEntry entry).length + 1

/-- One entry is placed in forward order above the previous row stack. -/
def compatibilityEdges_loadRowRun
    (entry : IndexedOccurrence × Nat)
    (tail work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCount : Nat) :
    Σ finalBuffer₂,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .load buffer₁ buffer₂ test
          (encodeIndexedOccurrenceEntry entry ++ tail)
          output work₁ [] upper clause variableCount)
        (some (compatibilityEdgesCfg .load (some .frameEnd) finalBuffer₂ test
          tail output (encodeIndexedOccurrenceEntry entry ++ work₁) []
          upper clause variableCount))
        (compatibilityEdgesLoadRowSteps entry) := by
  let content := encodeUnaryFrame (indexedOccurrenceRowValues entry.2 entry.1)
  have hfree := encodeUnaryFrame_frameEnd_free
    (indexedOccurrenceRowValues entry.2 entry.1)
  have hcontent := compatibilityEdges_loadSymbols_eval content
    (.frameEnd :: tail) work₁ [] output buffer₁ buffer₂ test
    upper clause variableCount hfree
  have hboundary :
      (flip Option.bind (step compatibilityEdgesProgram))^[2]
        (some (compatibilityEdgesCfg .load
          (compatibilityEdgesLoadLastBuffer buffer₁ content) buffer₂ test
          (.frameEnd :: tail) output work₁ content.reverse
          upper clause variableCount)) =
        some (compatibilityEdgesCfg .flushRow (some .frameEnd) buffer₂ test
          tail output work₁ (.frameEnd :: content.reverse)
          upper clause variableCount) := by
    rfl
  let finalBuffer₂ := compatibilityEdgesFlushLastBuffer buffer₂
    (.frameEnd :: content.reverse)
  have hflush := compatibilityEdges_flush_eval
    (.frameEnd :: content.reverse) tail work₁ output
    (some .frameEnd) buffer₂ test upper clause variableCount
  refine ⟨finalBuffer₂, ?_⟩
  let first : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .load buffer₁ buffer₂ test
        (content ++ .frameEnd :: tail) output work₁ []
        upper clause variableCount)
      (some (compatibilityEdgesCfg .flushRow (some .frameEnd) buffer₂ test
        tail output work₁ (.frameEnd :: content.reverse)
        upper clause variableCount))
      (2 * content.length + 2) :=
    ⟨⟨_, by
      calc
        (flip Option.bind (step compatibilityEdgesProgram))^[
            2 * content.length + 2]
            (some (compatibilityEdgesCfg .load buffer₁ buffer₂ test
              (content ++ .frameEnd :: tail) output work₁ []
              upper clause variableCount)) =
          (flip Option.bind (step compatibilityEdgesProgram))^[2]
            ((flip Option.bind (step compatibilityEdgesProgram))^[
              2 * content.length]
              (some (compatibilityEdgesCfg .load buffer₁ buffer₂ test
                (content ++ .frameEnd :: tail) output work₁ []
                upper clause variableCount))) := by
                  rw [show 2 * content.length + 2 =
                    2 + 2 * content.length by omega,
                    Function.iterate_add_apply]
        _ = (flip Option.bind (step compatibilityEdgesProgram))^[2]
            (some (compatibilityEdgesCfg .load
              (compatibilityEdgesLoadLastBuffer buffer₁ content) buffer₂ test
              (.frameEnd :: tail) output work₁ content.reverse
              upper clause variableCount)) := by
                simpa using congrArg
                  ((flip Option.bind (step compatibilityEdgesProgram))^[2])
                  hcontent
        _ = _ := hboundary⟩, le_rfl⟩
  let flushed : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .flushRow (some .frameEnd) buffer₂ test
        tail output work₁ (.frameEnd :: content.reverse)
        upper clause variableCount)
      (some (compatibilityEdgesCfg .load (some .frameEnd) finalBuffer₂ test
        tail output (content ++ [.frameEnd] ++ work₁) []
        upper clause variableCount))
      (content.length + 2) := by
    exact ⟨⟨content.length + 2, by
      simpa [List.reverse_cons, List.reverse_reverse,
        List.append_assoc] using hflush⟩, le_rfl⟩
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (2 * content.length + 2) (content.length + 2) _ _ _ first flushed
  have hsteps : (content.length + 2) + (2 * content.length + 2) =
      compatibilityEdgesLoadRowSteps entry := by
    simp only [compatibilityEdgesLoadRowSteps, encodeIndexedOccurrenceEntry,
      List.length_append, List.length_cons, List.length_nil]
    change (content.length + 2) + (2 * content.length + 2) =
      3 * (content.length + 1) + 1
    omega
  rw [← hsteps]
  simpa [content, encodeIndexedOccurrenceEntry, List.append_assoc] using full

/-- Exact accumulated cost of loading an explicit occurrence family. -/
def compatibilityEdgesLoadRowsSteps
    (entries : List (IndexedOccurrence × Nat)) : Nat :=
  (entries.map compatibilityEdgesLoadRowSteps).sum

/-- Every complete row is loaded, with row order reversed and field order
preserved. -/
def compatibilityEdges_loadRowsRun
    (entries : List (IndexedOccurrence × Nat))
    (tail work₁ : List UnaryFrameSym) (output : List CliqueSym)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (upper clause variableCount : Nat) :
    Σ finalBuffer₁, Σ finalBuffer₂,
      EvalsToInTime (step compatibilityEdgesProgram)
        (compatibilityEdgesCfg .load buffer₁ buffer₂ test
          (encodeIndexedOccurrenceEntries entries ++ tail)
          output work₁ [] upper clause variableCount)
        (some (compatibilityEdgesCfg .load finalBuffer₁ finalBuffer₂ test
          tail output
          (encodeIndexedOccurrenceEntries entries.reverse ++ work₁) []
          upper clause variableCount))
        (compatibilityEdgesLoadRowsSteps entries) := by
  induction entries generalizing buffer₁ buffer₂ work₁ with
  | nil =>
      exact ⟨buffer₁, buffer₂, ⟨⟨0, by
        simp [encodeIndexedOccurrenceEntries]⟩, le_rfl⟩⟩
  | cons entry entries ih =>
      let remaining := encodeIndexedOccurrenceEntries entries ++ tail
      rcases compatibilityEdges_loadRowRun entry remaining work₁ output
          buffer₁ buffer₂ test upper clause variableCount with
        ⟨afterRowBuffer₂, first⟩
      rcases ih (buffer₁ := some .frameEnd) (buffer₂ := afterRowBuffer₂)
          (work₁ := encodeIndexedOccurrenceEntry entry ++ work₁) with
        ⟨finalBuffer₁, finalBuffer₂, rest⟩
      refine ⟨finalBuffer₁, finalBuffer₂, ?_⟩
      let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
        (compatibilityEdgesLoadRowSteps entry)
        (compatibilityEdgesLoadRowsSteps entries) _ _ _ first rest
      simpa [remaining, encodeIndexedOccurrenceEntries,
        compatibilityEdgesLoadRowsSteps, List.reverse_cons,
        List.flatMap_append, List.append_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using full

/-- Loading the whole canonical family reaches the clean outer-loop entry. -/
def compatibilityEdges_loadCanonicalRun (formula : CNF) :
    Σ finalBuffer₂,
      EvalsToInTime (step compatibilityEdgesProgram)
        (initialCfg compatibilityEdgesProgram
          (encodeIndexedOccurrenceRows formula))
        (some (compatibilityEdgesCfg .outer none finalBuffer₂ false [] []
          (encodeIndexedOccurrenceEntries
            (indexedOccurrences formula).zipIdx.reverse)
          [] 0 0 0))
        (compatibilityEdgesLoadRowsSteps
          (indexedOccurrences formula).zipIdx + 1) := by
  have hrows := compatibilityEdges_loadRowsRun
    (indexedOccurrences formula).zipIdx [] [] [] none none false 0 0 0
  rw [encodeIndexedOccurrenceEntries_zipIdx] at hrows
  rcases hrows with ⟨finalBuffer₁, finalBuffer₂, loaded⟩
  let finish : EvalsToInTime (step compatibilityEdgesProgram)
      (compatibilityEdgesCfg .load finalBuffer₁ finalBuffer₂ false
        [] [] (encodeIndexedOccurrenceEntries
          (indexedOccurrences formula).zipIdx.reverse) [] 0 0 0)
      (some (compatibilityEdgesCfg .outer none finalBuffer₂ false [] []
        (encodeIndexedOccurrenceEntries
          (indexedOccurrences formula).zipIdx.reverse) [] 0 0 0)) 1 := by
    exact ⟨⟨1, by
      rfl⟩,
      le_rfl⟩
  refine ⟨finalBuffer₂, ?_⟩
  let full := EvalsToInTime.trans (step compatibilityEdgesProgram)
    (compatibilityEdgesLoadRowsSteps (indexedOccurrences formula).zipIdx)
    1 _ _ _ loaded (by simpa using finish)
  simpa [initialCfg, compatibilityEdgesCfg, compatibilityEdgesProgram,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using full

end TMClique
end Turing
end Chapter34
end CLRS
