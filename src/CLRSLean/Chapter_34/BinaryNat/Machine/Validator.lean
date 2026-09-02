import CLRSLean.Chapter_34.BinaryNat.RoundTrip
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-!
# Fixed validator for canonical binary naturals

Canonicality is regular in the big-endian grammar: the word is either the
single zero bit or begins with one.  The verified finite-state flat-map
controller therefore decides it in linear time and emits one Boolean result.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.BinaryNat

open PolyBuilder

inductive ValidatorMode
  | empty
  | singleZero
  | positive
  | invalid
deriving DecidableEq, Fintype

private def nextMode : ValidatorMode → Bool → ValidatorMode
  | .empty, false => .singleZero
  | .empty, true => .positive
  | .singleZero, _ => .invalid
  | .positive, _ => .positive
  | .invalid, _ => .invalid

private def modeAccepts : ValidatorMode → Bool
  | .singleZero | .positive => true
  | .empty | .invalid => false

/-- A fixed streaming controller that delays its one-bit answer until EOF. -/
def validatorSpec : StatefulFlatMapSpec ValidatorMode Bool Bool where
  initial := .empty
  action mode bit := ([], nextMode mode bit)
  finish mode := [modeAccepts mode]

private theorem rewrite_positive (bits : List Bool) :
    rewriteStatefulFlatMapFrom validatorSpec .positive bits = [true] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [validatorSpec, nextMode] using ih

private theorem rewrite_invalid (bits : List Bool) :
    rewriteStatefulFlatMapFrom validatorSpec .invalid bits = [false] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [rewriteStatefulFlatMapFrom.eq_def]
      simpa [validatorSpec, nextMode] using ih

/-- Pure output of the finite-state validator. -/
theorem validatorSpec_eq (bits : List Bool) :
    rewriteStatefulFlatMap validatorSpec bits =
      [CLRS.Chapter34.isCanonicalBinaryNat bits] := by
  unfold rewriteStatefulFlatMap
  change rewriteStatefulFlatMapFrom validatorSpec .empty bits = _
  cases bits with
  | nil => rfl
  | cons first rest =>
      cases first with
      | false =>
          cases rest with
          | nil => rfl
          | cons next tail =>
              change rewriteStatefulFlatMapFrom validatorSpec .singleZero
                (next :: tail) = [false]
              rw [rewriteStatefulFlatMapFrom.eq_def]
              change rewriteStatefulFlatMapFrom validatorSpec .invalid tail =
                [false]
              exact rewrite_invalid tail
      | true =>
          change rewriteStatefulFlatMapFrom validatorSpec .positive rest =
            [true]
          exact rewrite_positive rest

/-- A genuine fixed TM2 validates canonical binary-natural payloads in
polynomial (in fact linear) time. -/
noncomputable def validatorComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun bits : List Bool =>
        [CLRS.Chapter34.isCanonicalBinaryNat bits]) := by
  have heq : rewriteStatefulFlatMap validatorSpec =
      (fun bits : List Bool =>
        [CLRS.Chapter34.isCanonicalBinaryNat bits]) :=
    funext validatorSpec_eq
  rw [← heq]
  exact statefulFlatMap_computableInPolyTime validatorSpec

theorem validator_accepts_iff (bits : List Bool) :
    [CLRS.Chapter34.isCanonicalBinaryNat bits] = [true] ↔
      ∃ n, CLRS.Chapter34.decodeBinaryNat bits = some n := by
  constructor
  · intro h
    have hcanonical : CLRS.Chapter34.isCanonicalBinaryNat bits = true := by
      simpa using h
    exact ⟨CLRS.Chapter34.binaryNatValue bits, by
      simp [CLRS.Chapter34.decodeBinaryNat, hcanonical]⟩
  · rintro ⟨n, h⟩
    have hcanonical :=
      (CLRS.Chapter34.decodeBinaryNat_eq_some_iff.mp h).1
    simpa [hcanonical]

end CLRS.Chapter34.Turing.BinaryNat
