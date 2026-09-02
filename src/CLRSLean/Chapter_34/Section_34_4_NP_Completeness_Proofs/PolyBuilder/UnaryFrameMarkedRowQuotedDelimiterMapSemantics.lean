import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowQuotedDelimiterMapCore
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMapCycle
import Mathlib.Tactic

/-!
# Marked-row semantics of quoted delimiter materialization
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

private def quotedDelimiterAdvanceN
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Nat → Fin delimiters.length → Fin delimiters.length
  | 0, index => index
  | count + 1, index =>
      quotedDelimiterAdvanceN delimiters hnonempty count
        (unaryFrameDelimiterNext delimiters hnonempty index)

private def quotedDelimiterIndexAt
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset : Nat) :
    Fin delimiters.length :=
  ⟨offset % delimiters.length, Nat.mod_lt _ hnonempty⟩

private theorem quotedDelimiterNext_indexAt
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset : Nat) :
    unaryFrameDelimiterNext delimiters hnonempty
        (quotedDelimiterIndexAt delimiters hnonempty offset) =
      quotedDelimiterIndexAt delimiters hnonempty (offset + 1) := by
  apply Fin.ext
  unfold unaryFrameDelimiterNext quotedDelimiterIndexAt
  split <;> rename_i hnext
  · change offset % delimiters.length + 1 < delimiters.length at hnext
    change offset % delimiters.length + 1 =
      (offset + 1) % delimiters.length
    rw [Nat.add_mod]
    have hone : 1 % delimiters.length = 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hone, Nat.mod_eq_of_lt hnext]
  · change ¬ offset % delimiters.length + 1 < delimiters.length at hnext
    change 0 = (offset + 1) % delimiters.length
    have hmod := Nat.mod_lt offset hnonempty
    have hlast : offset % delimiters.length + 1 = delimiters.length := by
      omega
    rw [Nat.add_mod]
    by_cases hlength : delimiters.length = 1
    · rw [hlength, Nat.mod_one]
    · have hone : 1 % delimiters.length = 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hone, hlast, Nat.mod_self]

private theorem quotedDelimiterAdvanceN_indexAt
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset count : Nat) :
    quotedDelimiterAdvanceN delimiters hnonempty count
        (quotedDelimiterIndexAt delimiters hnonempty offset) =
      quotedDelimiterIndexAt delimiters hnonempty (offset + count) := by
  induction count generalizing offset with
  | zero => simp [quotedDelimiterAdvanceN]
  | succ count ih =>
      rw [show count + 1 = Nat.succ count by omega]
      simp only [quotedDelimiterAdvanceN]
      rw [quotedDelimiterNext_indexAt, ih (offset + 1)]
      congr 1
      omega

private theorem rewriteQuotedDelimiters_ticks
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty index
        (List.replicate count .tick ++ tail) =
      quoteUnaryFrameStream (List.replicate count .tick) ++
        rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty index
          tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameQuotedDelimitersFrom, quoteUnaryFrameStream_cons]
      rw [ih]
      simp [List.append_assoc]

private theorem rewriteQuotedDelimiters_encode_append
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (values : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty index
        (encodeUnaryFrame values ++ tail) =
      quoteUnaryFrameStream
          (encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty index
            values) ++
        rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty
          (quotedDelimiterAdvanceN delimiters hnonempty values.length index)
          tail := by
  induction values generalizing index with
  | nil => rfl
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            .separator :: (encodeUnaryFrame values ++ tail) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock, List.append_assoc]]
      rw [rewriteQuotedDelimiters_ticks]
      simp only [rewriteUnaryFrameQuotedDelimitersFrom,
        encodeUnaryFrameWithDelimiterCycleFrom, List.length_cons,
        quotedDelimiterAdvanceN, quoteUnaryFrameStream_cons]
      rw [ih]
      simp [quoteUnaryFrameStream, List.flatMap_append, List.append_assoc]

private theorem rewriteQuotedDelimiters_complete_row
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (values : List Nat) (hlength : values.length = delimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty
        ⟨0, hnonempty⟩ (encodeUnaryFrame values ++ tail) =
      quoteUnaryFrameStream
          (encodeUnaryFrameWithFixedDelimiters values delimiters) ++
        rewriteUnaryFrameQuotedDelimitersFrom delimiters hnonempty
          ⟨0, hnonempty⟩ tail := by
  rw [rewriteQuotedDelimiters_encode_append]
  have hzero :
      (⟨0, hnonempty⟩ : Fin delimiters.length) =
        quotedDelimiterIndexAt delimiters hnonempty 0 := by
    apply Fin.ext
    simp [quotedDelimiterIndexAt]
  have hadvance :
      quotedDelimiterAdvanceN delimiters hnonempty values.length
          ⟨0, hnonempty⟩ = ⟨0, hnonempty⟩ := by
    rw [hzero, quotedDelimiterAdvanceN_indexAt, hlength]
    apply Fin.ext
    simp [quotedDelimiterIndexAt]
  rw [hadvance]
  have hencoding := encodeUnaryFrameWithDelimiterCycle_eq_fixedRows
    delimiters hnonempty [values] (by
      intro row hrow
      rw [List.mem_singleton] at hrow
      subst row
      exact hlength)
  simpa [encodeUnaryFrameWithDelimiterCycle, hzero] using
    congrArg quoteUnaryFrameStream hencoding

/-- Every complete numeric row becomes the quotation of its materialized
fixed-delimiter payload followed by one literal outer boundary. -/
theorem rewriteUnaryFrameQuotedDelimiters_markedRows
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (rows : List (List Nat))
    (hlength : ∀ row ∈ rows, row.length = delimiters.length) :
    rewriteUnaryFrameQuotedDelimiters delimiters hnonempty
        (rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) =
      rows.flatMap fun row =>
        quoteUnaryFrameStream
            (encodeUnaryFrameWithFixedDelimiters row delimiters) ++
          [.frameEnd] := by
  unfold rewriteUnaryFrameQuotedDelimiters
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hrow := hlength row (by simp)
      have hrows : ∀ other ∈ rows,
          other.length = delimiters.length := by
        intro other hother
        exact hlength other (by simp [hother])
      simp only [List.flatMap_cons]
      rw [List.append_assoc]
      simp only [List.singleton_append]
      rw [rewriteQuotedDelimiters_complete_row delimiters hnonempty row hrow]
      simp only [rewriteUnaryFrameQuotedDelimitersFrom]
      rw [ih hrows]
      simp [List.append_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
