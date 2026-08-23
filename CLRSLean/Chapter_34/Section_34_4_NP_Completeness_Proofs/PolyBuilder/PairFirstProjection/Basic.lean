import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time
import Mathlib.Tactic.DeriveFintype

/-!
# First projection of a separator-encoded pair

This is the reusable counterpart of `Turing.Prj`: it retains the symbols
before the unique `none` separator and discards the right component.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection

/-- Finite control for copying the first component in forward order. -/
inductive Label (Γ : Type)
  | scan | save (symbol : Γ) | discard | restore | emit (symbol : Γ) | halt
deriving Fintype

/-- Fixed first-projection controller. -/
def program (Γ : Type) [Fintype Γ] : Program (Option Γ) Γ where
  Label := Label Γ
  labelDecidableEq := Classical.decEq _
  labelFintype := inferInstance
  main := .scan
  op
    | .scan => .popInput .restore fun
        | none => .discard
        | some symbol => .save symbol
    | .save symbol => .pushWork₁ (some symbol) .scan
    | .discard => .popInput .restore fun _ => .discard
    | .restore => .popWork₁ .halt fun
        | none => .restore
        | some symbol => .emit symbol
    | .emit symbol => .pushOutput symbol .restore
    | .halt => .halt

/-- Proof-facing configuration. -/
def cfg (Γ : Type) [Fintype Γ] (label : Label Γ)
    (buffer₁ buffer₂ : Option (Option Γ)) (test : Bool)
    (input : List (Option Γ)) (output : List Γ)
    (work₁ work₂ : List (Option Γ)) : BuilderCfg (program Γ) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := work₁
  work₂ := work₂
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.PolyBuilder.PairFirstProjection
