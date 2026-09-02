import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMapCycle
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Marking fixed-width unary field rows

An ordinary unary stream contains one `separator` after every numeric field.
For a positive verifier-fixed field count, a cyclic delimiter pass recognizes
the last separator of each row.  A symbol-local expansion restores that
separator and appends one reserved `frameEnd`, yielding a typed marked-row
family without changing any numeric payload.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Replace the final separator of each positive-width field group by a
temporary `frameEnd`. -/
def unaryFrameFixedFieldRowDelimiterTable
    (fieldCount : Nat) : List UnaryFrameSym :=
  List.replicate (fieldCount - 1) .separator ++ [.frameEnd]

theorem unaryFrameFixedFieldRowDelimiterTable_length
    (fieldCount : Nat) (hpositive : 0 < fieldCount) :
    (unaryFrameFixedFieldRowDelimiterTable fieldCount).length =
      fieldCount := by
  simp [unaryFrameFixedFieldRowDelimiterTable]
  omega

theorem unaryFrameFixedFieldRowDelimiterTable_nonempty
    (fieldCount : Nat) :
    0 < (unaryFrameFixedFieldRowDelimiterTable fieldCount).length := by
  simp [unaryFrameFixedFieldRowDelimiterTable]

/-- Restore the final ordinary separator and append the outer row marker. -/
def unaryFrameFixedFieldRowMarkBody : LoopBody UnaryFrameSym UnaryFrameSym where
  emit
    | .tick => [.tick]
    | .separator => [.separator]
    | .frameEnd => [.separator, .frameEnd]
  cost
    | .tick => 1
    | .separator => 1
    | .frameEnd => 2
  emit_length_le_cost := by intro symbol; cases symbol <;> simp

/-- Insert one outer row marker after every positive fixed-width group. -/
def markUnaryFrameFixedFieldRows
    (fieldCount : Nat) (input : List UnaryFrameSym) : List UnaryFrameSym :=
  (rewriteUnaryFrameDelimiters
      (unaryFrameFixedFieldRowDelimiterTable fieldCount)
      (unaryFrameFixedFieldRowDelimiterTable_nonempty fieldCount)
      input).flatMap unaryFrameFixedFieldRowMarkBody.emit

/-- Canonical marked encoding of ordinary numeric rows. -/
def encodeUnaryFrameFixedFieldMarkedRows
    (rows : List (List Nat)) : List UnaryFrameSym :=
  rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]

private theorem fixedFieldRowMarkBody_ticks (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap
        unaryFrameFixedFieldRowMarkBody.emit =
      List.replicate count UnaryFrameSym.tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons, ih]
      rfl

private theorem fixedFieldRowDelimiterTable_cons
    (first second : Nat) (rest : List Nat) :
    unaryFrameFixedFieldRowDelimiterTable (first :: second :: rest).length =
      .separator ::
        unaryFrameFixedFieldRowDelimiterTable (second :: rest).length := by
  simp [unaryFrameFixedFieldRowDelimiterTable, List.replicate_succ]

private theorem fixedFieldRowMarkBody_fixed
    (values : List Nat) (hnonempty : values ≠ []) :
    (encodeUnaryFrameWithFixedDelimiters values
        (unaryFrameFixedFieldRowDelimiterTable values.length)).flatMap
          unaryFrameFixedFieldRowMarkBody.emit =
      encodeUnaryFrame values ++ [.frameEnd] := by
  induction values with
  | nil => simp at hnonempty
  | cons value rest ih =>
      cases rest with
      | nil =>
          simp [unaryFrameFixedFieldRowDelimiterTable,
            encodeUnaryFrameWithFixedDelimiters, encodeUnaryFrame,
            encodeUnaryFrameBlock, unaryFrameFixedFieldRowMarkBody]
          simpa only [unaryFrameFixedFieldRowMarkBody] using
            fixedFieldRowMarkBody_ticks value
      | cons next tail =>
          have htail : next :: tail ≠ [] := by simp
          have ih' := ih htail
          rw [fixedFieldRowDelimiterTable_cons value next tail]
          simp only [encodeUnaryFrameWithFixedDelimiters,
            encodeUnaryFrame, encodeUnaryFrameBlock, List.flatMap_append,
            List.flatMap_cons]
          rw [fixedFieldRowMarkBody_ticks, ih']
          simp [unaryFrameFixedFieldRowMarkBody, encodeUnaryFrame,
            encodeUnaryFrameBlock, List.append_assoc]

private theorem fixedFieldRowMarkBody_rows
    (fieldCount : Nat) (hpositive : 0 < fieldCount)
    (rows : List (List Nat))
    (hlength : ∀ row ∈ rows, row.length = fieldCount) :
    (rows.flatMap fun row =>
      encodeUnaryFrameWithFixedDelimiters row
        (unaryFrameFixedFieldRowDelimiterTable fieldCount)).flatMap
          unaryFrameFixedFieldRowMarkBody.emit =
      encodeUnaryFrameFixedFieldMarkedRows rows := by
  unfold encodeUnaryFrameFixedFieldMarkedRows
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro row hrow
  have hrowLength := hlength row hrow
  have hrowNonempty : row ≠ [] := by
    intro hnil
    subst row
    simp at hrowLength
    omega
  rw [← hrowLength]
  exact fixedFieldRowMarkBody_fixed row hrowNonempty

/-- Exact marker insertion on every family of rows with the declared positive
fixed field count. -/
theorem markUnaryFrameFixedFieldRows_encode
    (fieldCount : Nat) (hpositive : 0 < fieldCount)
    (rows : List (List Nat))
    (hlength : ∀ row ∈ rows, row.length = fieldCount) :
    markUnaryFrameFixedFieldRows fieldCount
        (encodeUnaryFrame rows.flatten) =
      encodeUnaryFrameFixedFieldMarkedRows rows := by
  unfold markUnaryFrameFixedFieldRows
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  rw [encodeUnaryFrameWithDelimiterCycle_eq_fixedRows
    (unaryFrameFixedFieldRowDelimiterTable fieldCount)
    (unaryFrameFixedFieldRowDelimiterTable_nonempty fieldCount) rows]
  · exact fixedFieldRowMarkBody_rows fieldCount hpositive rows hlength
  · intro row hrow
    rw [unaryFrameFixedFieldRowDelimiterTable_length fieldCount hpositive]
    exact hlength row hrow

/-- The symbol-local expansion is polynomial-time. -/
noncomputable def unaryFrameFixedFieldRowMarkExpand_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List UnaryFrameSym =>
        input.flatMap unaryFrameFixedFieldRowMarkBody.emit) :=
  boundedLoop_computableInPolyTime unaryFrameFixedFieldRowMarkBody

/-- For every fixed positive field count, one concrete polynomial-time TM2
adds the outer row boundaries. -/
noncomputable def markUnaryFrameFixedFieldRows_computableInPolyTime
    (fieldCount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (markUnaryFrameFixedFieldRows fieldCount) := by
  let delimited := unaryFrameDelimiterMap_computableInPolyTime
    (unaryFrameFixedFieldRowDelimiterTable fieldCount)
    (unaryFrameFixedFieldRowDelimiterTable_nonempty fieldCount)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch delimited
      unaryFrameFixedFieldRowMarkExpand_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List UnaryFrameSym =>
      (rewriteUnaryFrameDelimiters
        (unaryFrameFixedFieldRowDelimiterTable fieldCount)
        (unaryFrameFixedFieldRowDelimiterTable_nonempty fieldCount)
        input).flatMap unaryFrameFixedFieldRowMarkBody.emit)
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
