import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameStatefulMap

/-!
# Same-input row-wise concatenation

Two aligned marked-row sources are first executed by the verified parallel
interleaver.  A fixed two-state streaming pass then erases the boundary after
each left row and retains the boundary after each right row.  Thus
`left₀/right₀/left₁/right₁/...` becomes
`(left₀ ++ right₀)/(left₁ ++ right₁)/...` with no oracle-side append.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Zip two aligned row lists by concatenating corresponding payloads. -/
def concatUnaryFrameMarkedRows :
    List (List UnaryFrameSym) → List (List UnaryFrameSym) →
      List (List UnaryFrameSym)
  | left :: lefts, right :: rights =>
      (left ++ right) :: concatUnaryFrameMarkedRows lefts rights
  | _, _ => []

/-- Row-wise concatenation preserves the common row count. -/
theorem concatUnaryFrameMarkedRows_length_of_aligned
    (left right : List (List UnaryFrameSym))
    (haligned : left.length = right.length) :
    (concatUnaryFrameMarkedRows left right).length = left.length := by
  induction left generalizing right with
  | nil =>
      have hright : right = [] :=
        List.eq_nil_of_length_eq_zero haligned.symm
      subst right
      rfl
  | cons leftRow leftRows ih =>
      cases right with
      | nil => simp at haligned
      | cons rightRow rightRows =>
          simp only [List.length_cons] at haligned
          simp only [concatUnaryFrameMarkedRows, List.length_cons]
          rw [ih rightRows (by omega)]

private theorem mem_concatUnaryFrameMarkedRows
    (left right : List (List UnaryFrameSym))
    (row : List UnaryFrameSym)
    (hrow : row ∈ concatUnaryFrameMarkedRows left right) :
    ∃ leftRow ∈ left, ∃ rightRow ∈ right, row = leftRow ++ rightRow := by
  induction left generalizing right with
  | nil => simp [concatUnaryFrameMarkedRows] at hrow
  | cons leftRow leftRows ih =>
      cases right with
      | nil => simp [concatUnaryFrameMarkedRows] at hrow
      | cons rightRow rightRows =>
          simp only [concatUnaryFrameMarkedRows, List.mem_cons] at hrow
          rcases hrow with rfl | hrow
          · exact ⟨leftRow, by simp, rightRow, by simp, rfl⟩
          · rcases ih rightRows hrow with
              ⟨tailLeft, htailLeft, tailRight, htailRight, rfl⟩
            exact ⟨tailLeft, by simp [htailLeft], tailRight,
              by simp [htailRight], rfl⟩

/-- Concatenating corresponding rows preserves delimiter safety. -/
def UnaryFrameAlignedMarkedRowPair.concatenated
    (pair : UnaryFrameAlignedMarkedRowPair) : UnaryFrameMarkedRowFamily where
  rows := concatUnaryFrameMarkedRows pair.left.rows pair.right.rows
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rcases mem_concatUnaryFrameMarkedRows _ _ row hrow with
      ⟨leftRow, hleftRow, rightRow, hrightRow, rfl⟩
    rw [List.mem_append] at hsymbol
    rcases hsymbol with hleft | hright
    · exact pair.left.frameEnd_free leftRow hleftRow symbol hleft
    · exact pair.right.frameEnd_free rightRow hrightRow symbol hright

/-- The finite-control bit records whether the next row boundary is the
erasable left/right join (`true`) or the retained outer boundary (`false`). -/
def unaryFrameMarkedRowConcatSpec : UnaryFrameStatefulMapSpec Bool where
  initial := true
  action dropBoundary symbol :=
    match symbol with
    | .frameEnd =>
        (if dropBoundary then none else some .frameEnd, !dropBoundary)
    | .tick => (some .tick, dropBoundary)
    | .separator => (some .separator, dropBoundary)

/-- Pure alternating-boundary rewrite implemented by the two-state pass. -/
def rewriteUnaryFrameMarkedRowConcat (input : List UnaryFrameSym) :
    List UnaryFrameSym :=
  rewriteUnaryFrameStateful unaryFrameMarkedRowConcatSpec input

private theorem rewriteUnaryFrameMarkedRowConcat_row
    (dropBoundary : Bool) (row tail : List UnaryFrameSym)
    (hfree : ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowConcatSpec dropBoundary
        (row ++ tail) =
      row ++ rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowConcatSpec
        dropBoundary tail := by
  induction row generalizing dropBoundary with
  | nil => rfl
  | cons symbol rest ih =>
      have hsymbol := hfree symbol (by simp)
      have hrest : ∀ item ∈ rest,
          item ≠ UnaryFrameSym.frameEnd := by
        intro item hitem
        exact hfree item (by simp [hitem])
      cases symbol with
      | tick =>
          simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
            unaryFrameMarkedRowConcatSpec]
          simpa only [unaryFrameMarkedRowConcatSpec] using
            congrArg (List.cons UnaryFrameSym.tick)
              (ih dropBoundary hrest)
      | separator =>
          simp only [List.cons_append, rewriteUnaryFrameStatefulFrom,
            unaryFrameMarkedRowConcatSpec]
          simpa only [unaryFrameMarkedRowConcatSpec] using
            congrArg (List.cons UnaryFrameSym.separator)
              (ih dropBoundary hrest)
      | frameEnd => exact (hsymbol rfl).elim

private theorem rewriteUnaryFrameMarkedRowConcat_interleavedFrom
    (left right : List (List UnaryFrameSym))
    (haligned : left.length = right.length)
    (hleftFree : ∀ row ∈ left, ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd)
    (hrightFree : ∀ row ∈ right, ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd) :
    rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowConcatSpec true
        (encodeUnaryFrameMarkedRows
          (interleaveUnaryFrameMarkedRows left right)) =
      encodeUnaryFrameMarkedRows
        (concatUnaryFrameMarkedRows left right) := by
  induction left generalizing right with
  | nil =>
      have hright : right = [] :=
        List.eq_nil_of_length_eq_zero haligned.symm
      subst right
      rfl
  | cons leftRow leftRows ih =>
      cases right with
      | nil => simp at haligned
      | cons rightRow rightRows =>
          have htailAligned : leftRows.length = rightRows.length := by
            simpa using Nat.succ.inj haligned
          have hleftRowFree : ∀ symbol ∈ leftRow,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro symbol hsymbol
            exact hleftFree leftRow (by simp) symbol hsymbol
          have hrightRowFree : ∀ symbol ∈ rightRow,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro symbol hsymbol
            exact hrightFree rightRow (by simp) symbol hsymbol
          have hleftRowsFree : ∀ row ∈ leftRows, ∀ symbol ∈ row,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro row hrow symbol hsymbol
            exact hleftFree row (by simp [hrow]) symbol hsymbol
          have hrightRowsFree : ∀ row ∈ rightRows, ∀ symbol ∈ row,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro row hrow symbol hsymbol
            exact hrightFree row (by simp [hrow]) symbol hsymbol
          simp only [interleaveUnaryFrameMarkedRows,
            concatUnaryFrameMarkedRows, encodeUnaryFrameMarkedRows_cons]
          rw [rewriteUnaryFrameMarkedRowConcat_row true leftRow _
            hleftRowFree]
          simp only [rewriteUnaryFrameStatefulFrom,
            unaryFrameMarkedRowConcatSpec, Bool.not_true, if_true]
          change leftRow ++
              rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowConcatSpec
                false (rightRow ++ _)= _
          rw [rewriteUnaryFrameMarkedRowConcat_row false rightRow _
            hrightRowFree]
          change leftRow ++ (rightRow ++ UnaryFrameSym.frameEnd ::
              rewriteUnaryFrameStatefulFrom unaryFrameMarkedRowConcatSpec
                true (encodeUnaryFrameMarkedRows
                  (interleaveUnaryFrameMarkedRows leftRows rightRows))) = _
          rw [ih rightRows htailAligned hleftRowsFree hrightRowsFree]
          simp [List.append_assoc]

/-- Deleting alternating interleaved boundaries gives the literal encoding
of corresponding-row concatenation. -/
theorem rewriteUnaryFrameMarkedRowConcat_interleaved
    (pair : UnaryFrameAlignedMarkedRowPair) :
    rewriteUnaryFrameMarkedRowConcat
        (encodeUnaryFrameMarkedRowFamily pair.interleaved) =
      encodeUnaryFrameMarkedRowFamily pair.concatenated := by
  exact rewriteUnaryFrameMarkedRowConcat_interleavedFrom pair.left.rows
    pair.right.rows pair.rowAligned pair.left.frameEnd_free
      pair.right.frameEnd_free

namespace UnaryFrameMarkedRowParallelConcat

variable {Γ : Type} [Fintype Γ]
variable {leftFamily rightFamily : List Γ → UnaryFrameMarkedRowFamily}

private def alignedPair
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length)
    (input : List Γ) : UnaryFrameAlignedMarkedRowPair :=
  { left := leftFamily input
    right := rightFamily input
    rowAligned := hAligned input }

/-- Typed row-wise concatenation family for two aligned same-input sources. -/
def concatenatedFamily
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (alignedPair hAligned input).concatenated

/-- The public row semantics of the same-input concatenated family. -/
@[simp] theorem concatenatedFamily_rows
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length)
    (input : List Γ) :
    (concatenatedFamily hAligned input).rows =
      concatUnaryFrameMarkedRows (leftFamily input).rows
        (rightFamily input).rows := rfl

/-- A fixed polynomial-time TM2 runs both sources and concatenates their
corresponding rows without retaining the internal join boundary. -/
noncomputable def computableInPolyTime
    (M₁ : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily leftFamily)
    (M₂ : _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily rightFamily)
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily (concatenatedFamily hAligned) := by
  let interleaved :=
    UnaryFrameMarkedRowParallelInterleave.computableInPolyTime M₁ M₂ hAligned
  let interleavedRaw :
      _root_.Turing.TM2ComputableInPolyTime id id
        (fun input => encodeUnaryFrameMarkedRowFamily
          (UnaryFrameMarkedRowParallelInterleave.interleavedFamily hAligned
            input)) :=
    { tm := interleaved.tm
      inputAlphabet := interleaved.inputAlphabet
      outputAlphabet := interleaved.outputAlphabet
      time := interleaved.time
      outputsFun := fun input => by
        simpa only [id_eq] using interleaved.outputsFun input }
  let joinedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch interleavedRaw
      (unaryFrameStatefulMap_computableInPolyTime
        unaryFrameMarkedRowConcatSpec)
  let joined := Classical.choice joinedExists
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have run := joined.outputsFun input
        have hrewrite := rewriteUnaryFrameMarkedRowConcat_interleaved
          (alignedPair hAligned input)
        have hrewrite' :
            (rewriteUnaryFrameStateful unaryFrameMarkedRowConcatSpec ∘
              fun input => encodeUnaryFrameMarkedRowFamily
                (UnaryFrameMarkedRowParallelInterleave.interleavedFamily
                  hAligned input)) input =
              encodeUnaryFrameMarkedRowFamily
                (concatenatedFamily hAligned input) := by
          simpa only [Function.comp_def, rewriteUnaryFrameMarkedRowConcat,
            UnaryFrameMarkedRowParallelInterleave.interleavedFamily,
            concatenatedFamily, alignedPair] using hrewrite
        rw [hrewrite'] at run
        simpa only [Function.comp_def, id_eq, concatenatedFamily,
          alignedPair] using run }

end UnaryFrameMarkedRowParallelConcat

end CLRS.Chapter34.Turing.PolyBuilder
