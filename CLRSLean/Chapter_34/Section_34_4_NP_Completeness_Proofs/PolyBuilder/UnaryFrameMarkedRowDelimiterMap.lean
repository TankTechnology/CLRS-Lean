import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMapCycle

/-!
# Fixed delimiter maps over marked unary rows

If every numeric row consumes one complete fixed delimiter cycle, the
delimiter transducer returns to its initial state before the reserved outer
`frameEnd`.  Existing row boundaries are preserved and do not advance the
cycle.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

private def unaryFrameDelimiterAdvanceN
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Nat → Fin delimiters.length → Fin delimiters.length
  | 0, index => index
  | count + 1, index =>
      unaryFrameDelimiterAdvanceN delimiters hnonempty count
        (unaryFrameDelimiterNext delimiters hnonempty index)

private def unaryFrameDelimiterIndexAt
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset : Nat) :
    Fin delimiters.length :=
  ⟨offset % delimiters.length, Nat.mod_lt _ hnonempty⟩

private theorem unaryFrameDelimiterNext_indexAt
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset : Nat) :
    unaryFrameDelimiterNext delimiters hnonempty
        (unaryFrameDelimiterIndexAt delimiters hnonempty offset) =
      unaryFrameDelimiterIndexAt delimiters hnonempty (offset + 1) := by
  apply Fin.ext
  unfold unaryFrameDelimiterNext unaryFrameDelimiterIndexAt
  split <;> rename_i hnext
  · change offset % delimiters.length + 1 < delimiters.length at hnext
    change offset % delimiters.length + 1 =
      (offset + 1) % delimiters.length
    rw [Nat.add_mod]
    have hone : 1 % delimiters.length = 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hone, Nat.mod_eq_of_lt hnext]
  · change ¬offset % delimiters.length + 1 < delimiters.length at hnext
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

private theorem unaryFrameDelimiterAdvanceN_indexAt
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset count : Nat) :
    unaryFrameDelimiterAdvanceN delimiters hnonempty count
        (unaryFrameDelimiterIndexAt delimiters hnonempty offset) =
      unaryFrameDelimiterIndexAt delimiters hnonempty (offset + count) := by
  induction count generalizing offset with
  | zero => simp [unaryFrameDelimiterAdvanceN]
  | succ count ih =>
      rw [show count + 1 = Nat.succ count by omega]
      simp only [unaryFrameDelimiterAdvanceN]
      rw [unaryFrameDelimiterNext_indexAt]
      rw [ih (offset + 1)]
      congr 1
      omega

private theorem unaryFrameMarkedDelimiter_ticks
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (count : Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom delimiters hnonempty index
        (List.replicate count .tick ++ tail) =
      List.replicate count .tick ++
        rewriteUnaryFrameDelimitersFrom delimiters hnonempty index tail := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append,
        rewriteUnaryFrameDelimitersFrom, unaryFrameDelimiterStep]
      exact congrArg (List.cons .tick) ih

private theorem rewriteUnaryFrameDelimitersFrom_encode_append
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (index : Fin delimiters.length) (values : List Nat)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom delimiters hnonempty index
        (encodeUnaryFrame values ++ tail) =
      encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty index
          values ++
        rewriteUnaryFrameDelimitersFrom delimiters hnonempty
          (unaryFrameDelimiterAdvanceN delimiters hnonempty values.length
            index) tail := by
  induction values generalizing index with
  | nil => rfl
  | cons value values ih =>
      rw [show encodeUnaryFrame (value :: values) ++ tail =
          List.replicate value .tick ++
            .separator :: (encodeUnaryFrame values ++ tail) by
        simp [encodeUnaryFrame, encodeUnaryFrameBlock,
          List.append_assoc]]
      rw [unaryFrameMarkedDelimiter_ticks]
      simp only [rewriteUnaryFrameDelimitersFrom,
        unaryFrameDelimiterStep,
        encodeUnaryFrameWithDelimiterCycleFrom,
        List.length_cons, unaryFrameDelimiterAdvanceN]
      rw [ih]
      simp [List.append_assoc]

private theorem rewriteUnaryFrameDelimitersFrom_complete_row
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (values : List Nat) (hlength : values.length = delimiters.length)
    (tail : List UnaryFrameSym) :
    rewriteUnaryFrameDelimitersFrom delimiters hnonempty
        ⟨0, hnonempty⟩ (encodeUnaryFrame values ++ tail) =
      encodeUnaryFrameWithFixedDelimiters values delimiters ++
        rewriteUnaryFrameDelimitersFrom delimiters hnonempty
          ⟨0, hnonempty⟩ tail := by
  rw [rewriteUnaryFrameDelimitersFrom_encode_append]
  have hzero :
      (⟨0, hnonempty⟩ : Fin delimiters.length) =
        unaryFrameDelimiterIndexAt delimiters hnonempty 0 := by
    apply Fin.ext
    simp [unaryFrameDelimiterIndexAt]
  have hadvance :
      unaryFrameDelimiterAdvanceN delimiters hnonempty values.length
          ⟨0, hnonempty⟩ =
        ⟨0, hnonempty⟩ := by
    rw [hzero, unaryFrameDelimiterAdvanceN_indexAt, hlength]
    apply Fin.ext
    simp [unaryFrameDelimiterIndexAt]
  rw [hadvance]
  have hencoding := encodeUnaryFrameWithDelimiterCycle_eq_fixedRows
    delimiters hnonempty [values] (by
      intro row hrow
      rw [List.mem_singleton] at hrow
      subst row
      exact hlength)
  simpa [encodeUnaryFrameWithDelimiterCycle, hzero] using hencoding

/-- A fixed delimiter cycle materializes every equal-width numeric row while
preserving the reserved outer boundary after each row. -/
theorem rewriteUnaryFrameDelimiters_markedRows
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (rows : List (List Nat))
    (hlength : ∀ row ∈ rows, row.length = delimiters.length) :
    rewriteUnaryFrameDelimiters delimiters hnonempty
        (rows.flatMap fun row => encodeUnaryFrame row ++ [.frameEnd]) =
      rows.flatMap fun row =>
        encodeUnaryFrameWithFixedDelimiters row delimiters ++
          [.frameEnd] := by
  unfold rewriteUnaryFrameDelimiters
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
      let restInput := rows.flatMap fun rest =>
        encodeUnaryFrame rest ++ [UnaryFrameSym.frameEnd]
      change rewriteUnaryFrameDelimitersFrom delimiters hnonempty
          ⟨0, hnonempty⟩
          (encodeUnaryFrame row ++ .frameEnd :: restInput) = _
      rw [rewriteUnaryFrameDelimitersFrom_complete_row delimiters hnonempty
        row hrow (.frameEnd :: restInput)]
      simp only [rewriteUnaryFrameDelimitersFrom,
        unaryFrameDelimiterStep]
      rw [ih hrows]
      simp [List.append_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
