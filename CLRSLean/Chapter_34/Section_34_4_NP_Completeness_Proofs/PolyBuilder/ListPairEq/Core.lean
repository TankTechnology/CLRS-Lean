import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time

/-! # Fixed equality checker for an option-separated pair of lists -/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder.ListPairEq

inductive Label (Γ : Type)
  | loadLeft
  | storeLeft (symbol : Γ)
  | loadRight
  | storeRight (symbol : Γ)
  | compareLeft (equal : Bool)
  | compareRight (equal : Bool) (left : Option Γ)
  | drainLeft
  | drainRight
  | finish (result : Bool)
  | halt
deriving Fintype

noncomputable instance {Γ : Type} : DecidableEq (Label Γ) :=
  Classical.decEq _

/-- Both sides are loaded onto separate stacks, reversing them equally; the
comparison phase can therefore inspect corresponding symbols in lockstep. -/
def program (Γ : Type) [Fintype Γ] [DecidableEq Γ] :
    Program (Option Γ) Bool where
  Label := Label Γ
  main := .loadLeft
  op
    | .loadLeft => .popInput (.finish false) fun
        | none => .loadRight
        | some symbol => .storeLeft symbol
    | .storeLeft symbol => .pushWork₁ (some symbol) .loadLeft
    | .loadRight => .popInput (.compareLeft true) fun
        | none => .finish false
        | some symbol => .storeRight symbol
    | .storeRight symbol => .pushWork₂ (some symbol) .loadRight
    | .compareLeft equal =>
        .popWork₁ (.compareRight equal none) fun
          | none => .drainLeft
          | some symbol => .compareRight equal (some symbol)
    | .compareRight equal left => .popWork₂
        (match left with
          | none => .finish equal
          | some _ => .drainLeft)
        fun
          | none => .drainRight
          | some right =>
              match left with
              | none => .drainRight
              | some left => .compareLeft (equal && decide (left = right))
    | .drainLeft => .popWork₁ (.finish false) fun _ => .drainLeft
    | .drainRight => .popWork₂ (.finish false) fun _ => .drainRight
    | .finish result => .pushOutput result .halt
    | .halt => .halt

def cfg (Γ : Type) [Fintype Γ] [DecidableEq Γ]
    (label : Label Γ) (buffer₁ buffer₂ : Option (Option Γ))
    (input : List (Option Γ)) (output : List Bool)
    (work₁ work₂ : List (Option Γ)) : BuilderCfg (program Γ) :=
  { initialCfg (program Γ) input with
      label := some label
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      output := output
      work₁ := work₁
      work₂ := work₂ }

end CLRS.Chapter34.Turing.PolyBuilder.ListPairEq
