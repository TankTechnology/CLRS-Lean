import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorInputBoundaryArmsLayout
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelConcat

/-!
# Uniform sources with one row per verifier-input arm

Every input-boundary channel has the same candidate-length index.  This
interface packages that shared row count and its concrete source machine.
Pointwise append is implemented by the verified parallel row concatenator.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- A raw-input source with exactly one marked row per possible certificate
length. -/
structure VerifierInputArmRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) where
  row : (input : List Γ) →
    Fin (W.certificateBound.eval input.length + 1) → List UnaryFrameSym
  family : List Γ → UnaryFrameMarkedRowFamily
  rows_eq : ∀ input, (family input).rows = List.ofFn (row input)
  computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily family

namespace VerifierInputArmRowSource

/-- Every arm source has the common candidate-count row length. -/
theorem rows_length
    {Γ : Type} {L : Language Γ} {W : VerifierWitness L}
    (source : VerifierInputArmRowSource W) (input : List Γ) :
    (source.family input).rows.length =
      W.certificateBound.eval input.length + 1 := by
  rw [source.rows_eq]
  simp

private theorem concat_ofFn_rows
    {count : Nat}
    (left right : Fin count → List UnaryFrameSym) :
    concatUnaryFrameMarkedRows (List.ofFn left) (List.ofFn right) =
      List.ofFn fun index => left index ++ right index := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [concatUnaryFrameMarkedRows]
      congr 1
      exact ih (fun index => left index.succ)
        (fun index => right index.succ)

/-- Append two independently compiled arm channels pointwise. -/
noncomputable def append
    {Γ : Type} {L : Language Γ} {W : VerifierWitness L}
    (left right : VerifierInputArmRowSource W) :
    VerifierInputArmRowSource W := by
  letI : Fintype Γ := W.alphabetFintype
  let aligned : ∀ input,
      (left.family input).rows.length =
        (right.family input).rows.length := fun input => by
    rw [left.rows_length, right.rows_length]
  exact
    { row := fun input arm => left.row input arm ++ right.row input arm
      family := UnaryFrameMarkedRowParallelConcat.concatenatedFamily aligned
      rows_eq := fun input => by
        change concatUnaryFrameMarkedRows
            (left.family input).rows (right.family input).rows = _
        rw [left.rows_eq, right.rows_eq]
        exact concat_ofFn_rows (left.row input) (right.row input)
      computableInPolyTime :=
        UnaryFrameMarkedRowParallelConcat.computableInPolyTime
          left.computableInPolyTime right.computableInPolyTime aligned }

@[simp] theorem append_row
    {Γ : Type} {L : Language Γ} {W : VerifierWitness L}
    (left right : VerifierInputArmRowSource W)
    (input : List Γ)
    (arm : Fin (W.certificateBound.eval input.length + 1)) :
    (left.append right).row input arm =
      left.row input arm ++ right.row input arm := rfl

end VerifierInputArmRowSource

end CLRS.Chapter34.Turing.CookLevin
