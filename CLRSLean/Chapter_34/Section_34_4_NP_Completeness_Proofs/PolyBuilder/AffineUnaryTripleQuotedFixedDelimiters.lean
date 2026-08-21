import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleMapSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteCore
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import Mathlib.Tactic

/-!
# Quoted fixed-delimiter affine rows

Replacing one unary value `v` by the pair `(2v, 0)` leaves enough delimiter
positions to emit the two-symbol quotation of its original delimiter.  This
turns an arbitrary fixed-delimiter affine row into a delimiter-safe quoted
row while keeping every numeric field affine in the original seed.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Scalar multiplication of a nonnegative affine triple form. -/
def AffineUnaryTripleForm.scale (factor : Nat)
    (form : AffineUnaryTripleForm) : AffineUnaryTripleForm :=
  { constant := factor * form.constant
    first := factor * form.first
    second := factor * form.second
    third := factor * form.third }

@[simp] theorem AffineUnaryTripleForm.scale_value
    (factor : Nat) (form : AffineUnaryTripleForm)
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleFormValue (form.scale factor) seed =
      factor * affineUnaryTripleFormValue form seed := by
  simp [AffineUnaryTripleForm.scale, affineUnaryTripleFormValue]
  ring

/-- Zero field used as the second half of every quoted unary block. -/
def affineUnaryTripleZeroForm : AffineUnaryTripleForm :=
  { constant := 0, first := 0, second := 0, third := 0 }

@[simp] theorem affineUnaryTripleZeroForm_value
    (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleFormValue affineUnaryTripleZeroForm seed = 0 := by
  simp [affineUnaryTripleZeroForm, affineUnaryTripleFormValue]

/-- Double every unary payload and follow it by one empty field. -/
def quoteAffineUnaryTripleForms :
    List AffineUnaryTripleForm → List AffineUnaryTripleForm
  | [] => []
  | form :: forms =>
      form.scale 2 :: affineUnaryTripleZeroForm ::
        quoteAffineUnaryTripleForms forms

/-- Value-level counterpart of `quoteAffineUnaryTripleForms`. -/
def quoteAffineUnaryValues : List Nat → List Nat
  | [] => []
  | value :: values => 2 * value :: 0 :: quoteAffineUnaryValues values

/-- Two delimiter positions for every original delimiter codeword. -/
def quoteFixedDelimiterTable :
    List UnaryFrameSym → List UnaryFrameSym
  | [] => []
  | delimiter :: delimiters =>
      quoteUnaryFrameSym delimiter ++ quoteFixedDelimiterTable delimiters

@[simp] theorem quoteAffineUnaryTripleForms_length
    (forms : List AffineUnaryTripleForm) :
    (quoteAffineUnaryTripleForms forms).length = 2 * forms.length := by
  induction forms with
  | nil => rfl
  | cons form forms ih =>
      simp [quoteAffineUnaryTripleForms, ih]
      omega

@[simp] theorem quoteAffineUnaryValues_length (values : List Nat) :
    (quoteAffineUnaryValues values).length = 2 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [quoteAffineUnaryValues, ih]
      omega

@[simp] theorem quoteFixedDelimiterTable_length
    (delimiters : List UnaryFrameSym) :
    (quoteFixedDelimiterTable delimiters).length =
      2 * delimiters.length := by
  induction delimiters with
  | nil => rfl
  | cons delimiter delimiters ih =>
      simp [quoteFixedDelimiterTable, ih]
      omega

/-- The expanded affine table evaluates to the expanded value table. -/
theorem affineUnaryTripleMap_quoteForms
    (forms : List AffineUnaryTripleForm) (seed : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (quoteAffineUnaryTripleForms forms) seed =
      quoteAffineUnaryValues (affineUnaryTripleMap forms seed) := by
  induction forms with
  | nil => rfl
  | cons form forms ih =>
      simp only [quoteAffineUnaryTripleForms, quoteAffineUnaryValues,
        affineUnaryTripleMap, List.map_cons,
        AffineUnaryTripleForm.scale_value,
        affineUnaryTripleZeroForm_value]
      rw [show List.map (fun next =>
            affineUnaryTripleFormValue next seed)
              (quoteAffineUnaryTripleForms forms) =
            quoteAffineUnaryValues
              (List.map (fun next => affineUnaryTripleFormValue next seed)
                forms) by
        simpa only [affineUnaryTripleMap] using ih]

private theorem quoteUnaryFrameStream_replicate_tick (count : Nat) :
    quoteUnaryFrameStream (List.replicate count .tick) =
      List.replicate (2 * count) .tick := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [List.replicate_succ, quoteUnaryFrameStream_cons,
        quoteUnaryFrameSym, ih]
      rw [show 2 * (count + 1) = 2 + 2 * count by omega,
        List.replicate_add]
      rfl

/-- Fixed-delimiter encoding of the expanded fields is exactly the quotation
of the original fixed-delimiter row. -/
theorem encodeUnaryFrameWithFixedDelimiters_quote
    (values : List Nat) (delimiters : List UnaryFrameSym)
    (hlength : values.length = delimiters.length) :
    encodeUnaryFrameWithFixedDelimiters
        (quoteAffineUnaryValues values)
        (quoteFixedDelimiterTable delimiters) =
      quoteUnaryFrameStream
        (encodeUnaryFrameWithFixedDelimiters values delimiters) := by
  induction values generalizing delimiters with
  | nil =>
      have hdelimiters : delimiters = [] :=
        List.eq_nil_of_length_eq_zero hlength.symm
      subst delimiters
      rfl
  | cons value values ih =>
      cases delimiters with
      | nil => simp at hlength
      | cons delimiter delimiters =>
          simp only [List.length_cons] at hlength
          have htail : values.length = delimiters.length :=
            Nat.add_right_cancel hlength
          simp only [quoteAffineUnaryValues, quoteFixedDelimiterTable]
          rw [quoteUnaryFrameSym_eq_pair]
          simp only [List.cons_append,
            encodeUnaryFrameWithFixedDelimiters, List.replicate_zero,
            List.nil_append]
          rw [ih delimiters htail]
          rw [show quoteUnaryFrameStream
                (List.replicate value .tick ++ delimiter ::
                  encodeUnaryFrameWithFixedDelimiters values delimiters) =
              quoteUnaryFrameStream (List.replicate value .tick) ++
                quoteUnaryFrameStream
                  (delimiter :: encodeUnaryFrameWithFixedDelimiters values
                    delimiters) by
            exact quoteUnaryFrameStream_append _ _]
          rw [quoteUnaryFrameStream_replicate_tick]
          simp [quoteUnaryFrameStream_cons, quoteUnaryFrameSym_eq_pair]

/-- Fixed-delimiter encoding distributes over aligned list append. -/
theorem encodeUnaryFrameWithFixedDelimiters_append_of_length
    (left right : List Nat) (leftDelimiters rightDelimiters :
      List UnaryFrameSym)
    (hlength : left.length = leftDelimiters.length) :
    encodeUnaryFrameWithFixedDelimiters (left ++ right)
        (leftDelimiters ++ rightDelimiters) =
      encodeUnaryFrameWithFixedDelimiters left leftDelimiters ++
        encodeUnaryFrameWithFixedDelimiters right rightDelimiters := by
  induction left generalizing leftDelimiters with
  | nil =>
      have hdelimiters : leftDelimiters = [] :=
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
          rw [ih delimiters (Nat.add_right_cancel hlength)]
          simp [List.append_assoc]

end CLRS.Chapter34.Turing.PolyBuilder
