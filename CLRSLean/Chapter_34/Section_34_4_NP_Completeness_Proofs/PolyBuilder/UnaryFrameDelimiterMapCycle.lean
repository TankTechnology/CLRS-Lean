import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMap
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedWidthPacketMark
import Mathlib.Tactic

/-!
# Whole-cycle semantics for unary-frame delimiter maps

The delimiter mapper is intentionally defined from a finite cyclic index.
This file proves the higher-level fact needed by fixed-layout compilers: if
each value row has exactly one complete delimiter cycle, then the cyclic
encoding is exactly the concatenation of the corresponding fixed-delimiter
rows.  The proof is generic and keeps all wraparound arithmetic out of the
Cook--Levin-specific source modules.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Natural-offset presentation of the same cyclic delimiter encoding. -/
def encodeUnaryFrameWithDelimiterOffset
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    Nat → List Nat → List UnaryFrameSym
  | _, [] => []
  | offset, value :: values =>
      List.replicate value .tick ++
        [delimiters.get
          ⟨offset % delimiters.length,
            Nat.mod_lt _ hnonempty⟩] ++
        encodeUnaryFrameWithDelimiterOffset delimiters hnonempty
          (offset + 1) values

private theorem unaryFrameDelimiterNext_mod
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) (offset : Nat) :
    unaryFrameDelimiterNext delimiters hnonempty
        ⟨offset % delimiters.length, Nat.mod_lt _ hnonempty⟩ =
      ⟨(offset + 1) % delimiters.length, Nat.mod_lt _ hnonempty⟩ := by
  apply Fin.ext
  unfold unaryFrameDelimiterNext
  split <;> rename_i hnext
  · change offset % delimiters.length + 1 =
      (offset + 1) % delimiters.length
    rw [Nat.add_mod]
    have hone : 1 % delimiters.length = 1 :=
      Nat.mod_eq_of_lt (by omega)
    rw [hone, Nat.mod_eq_of_lt hnext]
  · change ¬offset % delimiters.length + 1 < delimiters.length at hnext
    change 0 = (offset + 1) % delimiters.length
    have hmod : offset % delimiters.length < delimiters.length :=
      Nat.mod_lt _ hnonempty
    have hlast : offset % delimiters.length + 1 = delimiters.length := by
      omega
    rw [Nat.add_mod]
    by_cases honeLength : delimiters.length = 1
    · rw [honeLength, Nat.mod_one]
    · have hone : 1 % delimiters.length = 1 :=
        Nat.mod_eq_of_lt (by omega)
      rw [hone, hlast, Nat.mod_self]

private theorem encodeUnaryFrameWithDelimiterCycleFrom_eq_offset
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (offset : Nat) (values : List Nat) :
    encodeUnaryFrameWithDelimiterCycleFrom delimiters hnonempty
        ⟨offset % delimiters.length, Nat.mod_lt _ hnonempty⟩ values =
      encodeUnaryFrameWithDelimiterOffset delimiters hnonempty offset
        values := by
  induction values generalizing offset with
  | nil => rfl
  | cons value values ih =>
      simp only [encodeUnaryFrameWithDelimiterCycleFrom,
        encodeUnaryFrameWithDelimiterOffset]
      rw [unaryFrameDelimiterNext_mod]
      rw [ih (offset + 1)]

private theorem encodeUnaryFrameWithDelimiterOffset_append
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (offset : Nat) (left right : List Nat) :
    encodeUnaryFrameWithDelimiterOffset delimiters hnonempty offset
        (left ++ right) =
      encodeUnaryFrameWithDelimiterOffset delimiters hnonempty offset left ++
        encodeUnaryFrameWithDelimiterOffset delimiters hnonempty
          (offset + left.length) right := by
  induction left generalizing offset with
  | nil => simp [encodeUnaryFrameWithDelimiterOffset]
  | cons value left ih =>
      simp only [List.cons_append, List.length_cons,
        encodeUnaryFrameWithDelimiterOffset]
      rw [ih (offset + 1)]
      rw [show offset + 1 + left.length =
          offset + (left.length + 1) by omega]
      simp [List.append_assoc]

private theorem encodeUnaryFrameWithDelimiterOffset_period
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (offset : Nat) (values : List Nat) :
    encodeUnaryFrameWithDelimiterOffset delimiters hnonempty
        (offset + delimiters.length) values =
      encodeUnaryFrameWithDelimiterOffset delimiters hnonempty offset
        values := by
  induction values generalizing offset with
  | nil => rfl
  | cons value values ih =>
      simp only [encodeUnaryFrameWithDelimiterOffset]
      have hindex :
          (offset + delimiters.length) % delimiters.length =
            offset % delimiters.length := by
        rw [Nat.add_mod]
        simp
      have hfin :
          (⟨(offset + delimiters.length) % delimiters.length,
            Nat.mod_lt _ hnonempty⟩ : Fin delimiters.length) =
          ⟨offset % delimiters.length,
            Nat.mod_lt _ hnonempty⟩ :=
        Fin.ext hindex
      have hget := congrArg (fun index : Fin delimiters.length =>
        delimiters.get index) hfin
      rw [hget]
      rw [show offset + delimiters.length + 1 =
          (offset + 1) + delimiters.length by omega]
      rw [ih (offset + 1)]

private theorem encodeUnaryFrameWithDelimiterOffset_eq_fixed
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (offset : Nat) (values : List Nat)
    (hfit : offset + values.length = delimiters.length) :
    encodeUnaryFrameWithDelimiterOffset delimiters hnonempty offset values =
      encodeUnaryFrameWithFixedDelimiters values
        (delimiters.drop offset) := by
  induction values generalizing offset with
  | nil =>
      have hoffset : offset = delimiters.length := by omega
      subst offset
      simp [encodeUnaryFrameWithDelimiterOffset,
        encodeUnaryFrameWithFixedDelimiters]
  | cons value values ih =>
      have hposition : offset < delimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      have htail : offset + 1 + values.length = delimiters.length := by
        simp only [List.length_cons] at hfit
        omega
      simp only [encodeUnaryFrameWithDelimiterOffset]
      have hfin :
          (⟨offset % delimiters.length,
            Nat.mod_lt _ hnonempty⟩ : Fin delimiters.length) =
          ⟨offset, hposition⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hposition)
      have hget := congrArg (fun index : Fin delimiters.length =>
        delimiters.get index) hfin
      rw [hget]
      rw [List.drop_eq_getElem_cons hposition]
      simp only [encodeUnaryFrameWithFixedDelimiters]
      rw [ih (offset + 1) htail]
      simp [List.append_assoc]

/-- A family of equal-length value rows consumes one complete delimiter cycle
per row, so cyclic encoding is identical to explicit fixed-delimiter row
encoding. -/
theorem encodeUnaryFrameWithDelimiterCycle_eq_fixedRows
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (rows : List (List Nat))
    (hlength : ∀ row ∈ rows, row.length = delimiters.length) :
    encodeUnaryFrameWithDelimiterCycle delimiters hnonempty rows.flatten =
      rows.flatMap fun row =>
        encodeUnaryFrameWithFixedDelimiters row delimiters := by
  unfold encodeUnaryFrameWithDelimiterCycle
  have hzero :
      (⟨0, hnonempty⟩ : Fin delimiters.length) =
        ⟨0 % delimiters.length, Nat.mod_lt _ hnonempty⟩ := by
    apply Fin.ext
    simp
  rw [hzero]
  rw [encodeUnaryFrameWithDelimiterCycleFrom_eq_offset]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      have hrow : row.length = delimiters.length := hlength row (by simp)
      have hrows : ∀ other ∈ rows,
          other.length = delimiters.length := by
        intro other hother
        exact hlength other (by simp [hother])
      simp only [List.flatten_cons, List.flatMap_cons]
      rw [encodeUnaryFrameWithDelimiterOffset_append]
      rw [encodeUnaryFrameWithDelimiterOffset_eq_fixed delimiters hnonempty
        0 row (by simpa using hrow)]
      rw [show delimiters.drop 0 = delimiters by rfl]
      rw [hrow]
      rw [encodeUnaryFrameWithDelimiterOffset_period delimiters hnonempty
        0 rows.flatten]
      exact congrArg
        (fun suffix =>
          encodeUnaryFrameWithFixedDelimiters row delimiters ++ suffix)
        (ih hrows)

/-- Fixed-delimiter encoding distributes over an aligned prefix. -/
theorem encodeUnaryFrameWithFixedDelimiters_append
    (leftValues rightValues : List Nat)
    (leftDelimiters rightDelimiters : List UnaryFrameSym)
    (hlength : leftValues.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (leftValues ++ rightValues)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters leftValues leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters rightValues rightDelimiters := by
  induction leftValues generalizing leftDelimiters with
  | nil =>
      have hnil : leftDelimiters = [] :=
        List.eq_nil_of_length_eq_zero hlength.symm
      subst leftDelimiters
      rfl
  | cons value values ih =>
      cases leftDelimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          simp only [List.cons_append,
            encodeUnaryFrameWithFixedDelimiters]
          rw [ih delimiters (by omega)]
          simp [List.append_assoc]

/-- Giving a nonempty value row ordinary separators followed by one final
delimiter is exactly the fixed-width packet encoding with that delimiter in
place of `frameEnd`. -/
theorem encodeUnaryFrameWithOwnFinalDelimiter
    (values : List Nat) (finalDelimiter : UnaryFrameSym)
    (hne : values ≠ []) :
    encodeUnaryFrameWithFixedDelimiters values
        (List.replicate (values.length - 1) .separator ++
          [finalDelimiter]) =
      (encodeUnaryFrameFixedWidthPacketBody values ++ [finalDelimiter]) := by
  induction values with
  | nil => exact False.elim (hne rfl)
  | cons value values ih =>
      cases values with
      | nil =>
          simp [encodeUnaryFrameWithFixedDelimiters,
            encodeUnaryFrameFixedWidthPacketBody]
      | cons next rest =>
          have htail : next :: rest ≠ [] := by simp
          have hlength : (value :: next :: rest).length - 1 =
              (next :: rest).length := by simp
          rw [hlength]
          change encodeUnaryFrameWithFixedDelimiters (value :: next :: rest)
              (List.replicate (rest.length + 1) .separator ++
                [finalDelimiter]) = _
          rw [List.replicate_succ]
          simp only [encodeUnaryFrameWithFixedDelimiters,
            encodeUnaryFrameFixedWidthPacketBody, List.cons_append]
          have hrec := ih htail
          simp only [List.length_cons, Nat.add_sub_cancel] at hrec
          rw [hrec]
          simp [List.append_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
