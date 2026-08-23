import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import Mathlib.Tactic.DeriveFintype

/-!
# Formatting the left half of an option-separated pair
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft

/-- Embed a raw stream as the left component and append the `none` separator. -/
def format {Γ : Type} (input : List Γ) : List (Option Γ) :=
  input.map some ++ [none]

inductive Label (Γ : Type)
  | scan | emit (symbol : Γ) | separator | halt
deriving Fintype

/-- Reversed-output formatter. -/
def program (Γ : Type) [Fintype Γ] : Program Γ (Option Γ) where
  Label := Label Γ
  labelDecidableEq := Classical.decEq _
  labelFintype := inferInstance
  main := .scan
  op
    | .scan => .popInput .separator .emit
    | .emit symbol => .pushOutput (some symbol) .scan
    | .separator => .pushOutput none .halt
    | .halt => .halt

def cfg (Γ : Type) [Fintype Γ] (label : Label Γ)
    (buffer₁ buffer₂ : Option Γ) (test : Bool)
    (input : List Γ) (output : List (Option Γ)) : BuilderCfg (program Γ) where
  label := some label
  buffer₁ := buffer₁
  buffer₂ := buffer₂
  test := test
  input := input
  output := output
  work₁ := []
  work₂ := []
  counter₁ := []
  counter₂ := []
  counter₃ := []

end CLRS.Chapter34.Turing.PolyBuilder.OptionPairLeft
