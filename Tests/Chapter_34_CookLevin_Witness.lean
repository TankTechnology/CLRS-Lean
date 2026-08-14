import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization

namespace CLRS.Chapter34.Turing.CookLevin.WitnessTest

open Computability StateTransition
open _root_.Turing _root_.Turing.TM2 _root_.Turing.TM2.Stmt

private inductive Stack
  | input
  | output
deriving DecidableEq, Fintype

private abbrev Alphabet : Stack → Type
  | .input => Option Empty
  | .output => Bool

private instance : Fintype (Alphabet .input) :=
  inferInstanceAs (Fintype (Option Empty))

/-- A one-step machine that ignores its pair input, writes `false` on a
separate output stack, and halts. -/
private abbrev constantFalseMachine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
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
        change @Eq (Option (TM2.Cfg Alphabet Unit Unit)) _ _
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

private theorem emptyLanguageVerifiable : PolyTimeVerifiable emptyLanguage := by
  exact ⟨emptyVerifierWitness.verify, emptyVerifierWitness.certificateBound,
    ⟨emptyVerifierWitness.machine⟩, emptyVerifierWitness.correct⟩

private noncomputable def normalizedEmptyWitness : VerifierWitness emptyLanguage :=
  VerifierWitness.ofPolyTimeVerifiable emptyLanguageVerifiable

example : ∀ x, x ∈ emptyLanguage ↔ ∃ c,
    c.length ≤ normalizedEmptyWitness.certificateBound.eval x.length ∧
      normalizedEmptyWitness.verify c x = true :=
  normalizedEmptyWitness.correct

example : emptyVerifierWitness.verify [] [] = false := rfl

example : (pairEncoding [true] [false, true]).length = 4 := by
  simp

example : (List.map emptyVerifierWitness.machine.inputAlphabet.invFun
    (pairEncoding ([] : List Empty) [])).length = 1 := by
  simp

example : (verifierInputBound emptyVerifierWitness).eval 3 = 4 := by
  simp [emptyVerifierWitness]

example : emptyVerifierWitness.machine.time.eval
    (pairEncoding ([] : List Empty) []).length <
    (verifierHorizon emptyVerifierWitness).eval 0 := by
  exact emptyVerifierWitness.machineTime_lt_horizon (by simp [emptyVerifierWitness])

example : (List.map emptyVerifierWitness.machine.inputAlphabet.invFun
    (pairEncoding [] [])).length ≤ (verifierHeight emptyVerifierWitness).eval 0 := by
  exact emptyVerifierWitness.machineInput_length_le_height
    (by simp [emptyVerifierWitness])

example : Nonempty (TM2OutputsInTime emptyVerifierWitness.machine.tm
    (List.map emptyVerifierWitness.machine.inputAlphabet.invFun
      (pairEncoding [] []))
    (some (List.map emptyVerifierWitness.machine.outputAlphabet.invFun
      (boolEncoding (emptyVerifierWitness.verify [] []))))
    ((verifierHorizon emptyVerifierWitness).eval 0)) :=
  ⟨emptyVerifierWitness.outputsInHorizon (by simp [emptyVerifierWitness])⟩

example :
    (stutterStep emptyVerifierWitness.machine.tm)^[
        (verifierHorizon emptyVerifierWitness).eval 0]
      (initList emptyVerifierWitness.machine.tm
        (List.map emptyVerifierWitness.machine.inputAlphabet.invFun
          (pairEncoding [] []))) =
    haltList emptyVerifierWitness.machine.tm
      (List.map emptyVerifierWitness.machine.outputAlphabet.invFun
        (boolEncoding (emptyVerifierWitness.verify [] []))) :=
  emptyVerifierWitness.stutter_horizon_eq_haltList
    (c := []) (x := []) (by simp [emptyVerifierWitness])

end CLRS.Chapter34.Turing.CookLevin.WitnessTest
