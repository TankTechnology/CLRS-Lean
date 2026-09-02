import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Row markers for unary triple streams

Many runtime sources emit a flat sequence of ordinary three-field unary
frames.  This fixed two-pass transducer retains every ordinary field
separator and inserts one `frameEnd` after each complete triple.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The cyclic table identifies every third ordinary separator. -/
def unaryTripleRowDelimiterTable : List UnaryFrameSym :=
  [.separator, .separator, .frameEnd]

@[simp] theorem unaryTripleRowDelimiterTable_length :
    unaryTripleRowDelimiterTable.length = 3 := by rfl

theorem unaryTripleRowDelimiterTable_nonempty :
    0 < unaryTripleRowDelimiterTable.length := by simp

/-- Expand the temporary third-field marker back to the ordinary separator
required by the triple consumer, followed by the new outer row marker. -/
def unaryTripleRowMarkBody : LoopBody UnaryFrameSym UnaryFrameSym where
  emit
    | .tick => [.tick]
    | .separator => [.separator]
    | .frameEnd => [.separator, .frameEnd]
  cost
    | .tick => 1
    | .separator => 1
    | .frameEnd => 2
  emit_length_le_cost := by intro symbol; cases symbol <;> simp

/-- Replace every third separator and then expand that temporary marker. -/
def markUnaryTripleRows (input : List UnaryFrameSym) : List UnaryFrameSym :=
  (rewriteUnaryFrameDelimiters unaryTripleRowDelimiterTable
    unaryTripleRowDelimiterTable_nonempty input).flatMap
      unaryTripleRowMarkBody.emit

/-- Ordinary flat encoding of a semantic triple family. -/
def encodeUnaryTripleRows (rows : List (Nat × Nat × Nat)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame [row.1, row.2.1, row.2.2]

/-- Row-marked encoding consumed by an enclosing family controller. -/
def encodeUnaryTripleMarkedRows (rows : List (Nat × Nat × Nat)) :
    List UnaryFrameSym :=
  rows.flatMap fun row =>
    encodeUnaryFrame [row.1, row.2.1, row.2.2] ++ [.frameEnd]

private theorem encodeUnaryTripleRows_eq_frame (rows : List (Nat × Nat × Nat)) :
    encodeUnaryTripleRows rows =
      encodeUnaryFrame (rows.flatMap fun row =>
        [row.1, row.2.1, row.2.2]) := by
  unfold encodeUnaryTripleRows encodeUnaryFrame
  rw [List.flatMap_assoc]

private theorem unaryTripleDelimiterCycle_rows
    (rows : List (Nat × Nat × Nat)) :
    encodeUnaryFrameWithDelimiterCycle unaryTripleRowDelimiterTable
        unaryTripleRowDelimiterTable_nonempty
        (rows.flatMap fun row => [row.1, row.2.1, row.2.2]) =
      rows.flatMap fun row =>
        encodeUnaryFrameWithFixedDelimiters
          [row.1, row.2.1, row.2.2]
          unaryTripleRowDelimiterTable := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨first, second, third⟩
      simp [List.cons_append, encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithDelimiterCycleFrom,
        encodeUnaryFrameWithFixedDelimiters,
        unaryTripleRowDelimiterTable,
        unaryFrameDelimiterNext, List.append_assoc]
      simpa [encodeUnaryFrameWithDelimiterCycle,
        encodeUnaryFrameWithFixedDelimiters,
        unaryTripleRowDelimiterTable] using ih

private theorem unaryTripleRowMarkBody_ticks (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap
        unaryTripleRowMarkBody.emit =
      List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

private theorem unaryTripleRowMarkBody_fixedFrame
    (first second third : Nat) :
    (encodeUnaryFrameWithFixedDelimiters [first, second, third]
        unaryTripleRowDelimiterTable).flatMap
        unaryTripleRowMarkBody.emit =
      encodeUnaryFrame [first, second, third] ++ [.frameEnd] := by
  simp only [encodeUnaryFrameWithFixedDelimiters,
    unaryTripleRowDelimiterTable, encodeUnaryFrame,
    encodeUnaryFrameBlock, List.flatMap_cons, List.flatMap_nil,
    List.flatMap_append, List.append_nil]
  rw [unaryTripleRowMarkBody_ticks, unaryTripleRowMarkBody_ticks,
    unaryTripleRowMarkBody_ticks]
  simp [unaryTripleRowMarkBody, List.append_assoc]

/-- Exact semantic action on every well-formed flat triple family. -/
theorem markUnaryTripleRows_encode (rows : List (Nat × Nat × Nat)) :
    markUnaryTripleRows (encodeUnaryTripleRows rows) =
      encodeUnaryTripleMarkedRows rows := by
  unfold markUnaryTripleRows
  rw [encodeUnaryTripleRows_eq_frame]
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  rw [unaryTripleDelimiterCycle_rows]
  unfold encodeUnaryTripleMarkedRows
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro row hrow
  rcases row with ⟨first, second, third⟩
  exact unaryTripleRowMarkBody_fixedFrame first second third

/-- The second pass is a verified finite symbol-local expansion. -/
noncomputable def unaryTripleRowMarkExpand_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        input.flatMap unaryTripleRowMarkBody.emit) :=
  boundedLoop_computableInPolyTime unaryTripleRowMarkBody

/-- A fixed polynomial-time TM2 inserts one outer boundary after each unary
triple in an ordinary flat stream. -/
noncomputable def markUnaryTripleRows_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id markUnaryTripleRows := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (unaryFrameDelimiterMap_computableInPolyTime
        unaryTripleRowDelimiterTable unaryTripleRowDelimiterTable_nonempty)
      unaryTripleRowMarkExpand_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List UnaryFrameSym =>
      (rewriteUnaryFrameDelimiters unaryTripleRowDelimiterTable
        unaryTripleRowDelimiterTable_nonempty input).flatMap
          unaryTripleRowMarkBody.emit)
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
