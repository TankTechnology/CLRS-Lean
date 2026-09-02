import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-!
# Second projection of a separator-encoded pair

A two-state streaming pass discards the left component and the unique `none`
separator, then copies the right component.  This complements the existing
stack-based first projection.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.PairSecondProjection

open _root_.Turing
open PolyBuilder

def spec (Γ : Type) : StatefulFlatMapSpec Bool (Option Γ) Γ where
  initial := false
  action afterSeparator symbol :=
    if afterSeparator then
      match symbol with
      | some value => ([value], true)
      | none => ([], true)
    else
      match symbol with
      | some _ => ([], false)
      | none => ([], true)
  finish _ := []

def project (Γ : Type) (input : List (Option Γ)) : List Γ :=
  rewriteStatefulFlatMap (spec Γ) input

private theorem from_true_map {Γ : Type} (right : List Γ) :
    rewriteStatefulFlatMapFrom (spec Γ) true (right.map some) = right := by
  induction right with
  | nil => rfl
  | cons symbol right ih =>
      rw [PolyBuilder.rewriteStatefulFlatMapFrom.eq_def]
      change [symbol] ++
        rewriteStatefulFlatMapFrom (spec Γ) true (right.map some) =
          symbol :: right
      rw [ih]
      rfl

private theorem from_false_pair {Γ : Type} (left right : List Γ) :
    rewriteStatefulFlatMapFrom (spec Γ) false
      (pairEncoding left right) = right := by
  induction left with
  | nil =>
      rw [show pairEncoding ([] : List Γ) right =
          none :: right.map some by rfl]
      rw [PolyBuilder.rewriteStatefulFlatMapFrom.eq_def]
      change [] ++ rewriteStatefulFlatMapFrom (spec Γ) true
        (right.map some) = right
      exact from_true_map right
  | cons symbol left ih =>
      rw [show pairEncoding (symbol :: left) right =
          some symbol :: pairEncoding left right by rfl]
      rw [PolyBuilder.rewriteStatefulFlatMapFrom.eq_def]
      change [] ++ rewriteStatefulFlatMapFrom (spec Γ) false
        (pairEncoding left right) = right
      exact ih

theorem project_pairEncoding {Γ : Type} (left right : List Γ) :
    project Γ (pairEncoding left right) = right := by
  unfold project rewriteStatefulFlatMap
  exact from_false_pair left right

/-- A fixed linear-time TM2 computes the right component of a pair encoding. -/
noncomputable def computableInPolyTime (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime
      (fun pr : List Γ × List Γ => pairEncoding pr.1 pr.2)
      id Prod.snd := by
  let machine := statefulFlatMap_computableInPolyTime (spec Γ)
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun pr => by
        have output := machine.outputsFun (pairEncoding pr.1 pr.2)
        have hsemantic : rewriteStatefulFlatMap (spec Γ)
            (pairEncoding pr.1 pr.2) = pr.2 := by
          exact project_pairEncoding pr.1 pr.2
        rw [hsemantic] at output
        simpa using output }

end CLRS.Chapter34.Turing.PolyBuilder.PairSecondProjection
