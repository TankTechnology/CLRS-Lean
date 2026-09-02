import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Support

/-!
# Chapter 34 verifier-input support regressions

Focused interface and concrete-alphabet checks for the pure support bridge used
by the certificate-shaped first tableau row.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open Computability StateTransition
open _root_.Turing _root_.Turing.TM2 _root_.Turing.TM2.Stmt

noncomputable section

#check verifierInputSymbol
#check verifierInputSymbol_val
#check verifierInputSymbol_apply
#check verifierInputCode
#check verifierInputCode_ne_blank
#check IsVerifierInput
#check verifierInputBound_le_height
#check StackBits.Represents.height_eq_true_iff
#check StackBits.Represents.active_cell_eq_true_iff

/-! ## Empty verifier alphabet regression -/

private inductive EmptyStack
  | input
  | output
deriving DecidableEq, Fintype

private abbrev EmptyAlphabet : EmptyStack → Type
  | .input => Option Empty
  | .output => Bool

private instance : Fintype (EmptyAlphabet .input) :=
  inferInstanceAs (Fintype (Option Empty))

private abbrev constantFalseMachine : FinTM2 where
  K := EmptyStack
  k₀ := .input
  k₁ := .output
  Γ := EmptyAlphabet
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := pop .input (fun state _ => state)
    (push .output (fun _ => false) halt)

private def constantFalseInputAlphabet :
    constantFalseMachine.Γ constantFalseMachine.k₀ ≃ Option Empty :=
  Equiv.refl _

private def constantFalseOutputAlphabet :
    constantFalseMachine.Γ constantFalseMachine.k₁ ≃ Bool :=
  Equiv.refl _

private noncomputable def constantFalseInPolyTime : TM2ComputableInPolyTime
    (fun pr : List Empty × List Empty => pairEncoding pr.1 pr.2)
    boolEncoding (fun _ => false) where
  tm := constantFalseMachine
  inputAlphabet := constantFalseInputAlphabet
  outputAlphabet := constantFalseOutputAlphabet
  time := 1
  outputsFun := fun pr => by
    rcases pr with ⟨c, x⟩
    cases c with
    | cons a _ => exact a.elim
    | nil =>
      cases x with
      | cons a _ => exact a.elim
      | nil =>
        simp [TM2OutputsInTime, constantFalseInputAlphabet,
          constantFalseOutputAlphabet, boolEncoding]
        refine { steps := 1, evals_in_steps := ?_, steps_le_m := by simp }
        simp [constantFalseMachine, initList, haltList, TM2.step, flip]
        change @Eq (Option (TM2.Cfg EmptyAlphabet Unit Unit)) _ _
        congr 1
        apply Turing.TM2Comp.Cfg_ext <;> try rfl
        funext k
        cases k <;> simp [pairEncoding, Turing.TM2Comp.boolEncoding]

private def emptyLanguage : Language Empty := ∅

private noncomputable def emptyVerifierWitness : VerifierWitness emptyLanguage where
  verify := fun _ _ => false
  certificateBound := 0
  machine := constantFalseInPolyTime
  correct := by simp [emptyLanguage]

example : (verifierInputSymbol emptyVerifierWitness none).val = none := by
  simp [emptyVerifierWitness, constantFalseInPolyTime,
    constantFalseInputAlphabet]

example : emptyVerifierWitness.machine.inputAlphabet
    (verifierInputSymbol emptyVerifierWitness none).val = none := by
  exact verifierInputSymbol_apply emptyVerifierWitness none

example : verifierInputCode emptyVerifierWitness none ≠
    Fin.last
      (reachableAlphabet emptyVerifierWitness.machine.tm
        emptyVerifierWitness.machine.tm.k₀).card :=
  verifierInputCode_ne_blank emptyVerifierWitness none

example : IsVerifierInput emptyVerifierWitness [] [none] := by
  refine ⟨[], by simp [emptyVerifierWitness], ?_⟩
  simp [emptyVerifierWitness, constantFalseInPolyTime,
    constantFalseInputAlphabet, pairEncoding]

example : (verifierInputBound emptyVerifierWitness).eval 0 ≤
    (verifierHeight emptyVerifierWitness).eval 0 :=
  verifierInputBound_le_height emptyVerifierWitness 0

/-! ## Nonempty supported-symbol projection regression -/

private abbrev symbolMachine : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := halt

private theorem true_mem_symbolMachine_support :
    true ∈ reachableAlphabet symbolMachine () := by
  unfold reachableAlphabet
  simp

private def supportedTrue : SupportedSymbol symbolMachine () :=
  ⟨true, true_mem_symbolMachine_support⟩

private def oneSymbolBits : StackBits symbolMachine 1 () :=
  encodeBoundedStackBits
    (encodeBoundedStack symbolMachine () [true]
      (by simpa using true_mem_symbolMachine_support) (by simp))

private theorem oneSymbolBits_represents :
    oneSymbolBits.Represents [true] := by
  exact StackBits.Represents.of_encode (tm := symbolMachine) (W := 1) (k := ()) [true]
    (by simpa using true_mem_symbolMachine_support) (by simp)

example : oneSymbolBits.height ⟨1, by omega⟩ = true := by
  exact (oneSymbolBits_represents.height_eq_true_iff ⟨1, by omega⟩).2 rfl

example : oneSymbolBits.cell ⟨0, by omega⟩
    (encodeAlphabetSymbol symbolMachine () supportedTrue.val
      supportedTrue.property) = true := by
  exact (oneSymbolBits_represents.active_cell_eq_true_iff
    ⟨0, by omega⟩ (by simp) supportedTrue).2 rfl

end

end CLRS.Chapter34.Turing.CookLevin
