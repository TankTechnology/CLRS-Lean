import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.ReachableAlphabet

namespace CLRS.Chapter34.Turing.CookLevin

open Computability StateTransition
open _root_.Turing.TM2.Stmt

#check stmtPushSet
#check reachableAlphabet
#check CfgAlphabetBounded
#check stmtPushSet_program_subset
#check initList_alphabetBounded
#check stepAux_alphabetBounded
#check stepAux_program_alphabetBounded
#check step_alphabetBounded
#check evalsInSteps_alphabetBounded
#check reachableAlphabet_finite

private inductive SupportK
  | input | work
deriving DecidableEq, Fintype

private abbrev SupportΓ : SupportK → Type
  | .input => Bool
  | .work => Nat → Nat

private inductive SupportLabel
  | main | cleanup | done
deriving DecidableEq, Fintype

/-- A finite-control machine with an intentionally infinite work alphabet.
Its program covers recursive push continuations, both branch arms, pop, peek,
load, goto, and halt. -/
private abbrev supportMachine : _root_.Turing.FinTM2 where
  K := SupportK
  k₀ := .input
  k₁ := .input
  Γ := SupportΓ
  Λ := SupportLabel
  main := .main
  σ := Bool
  initialState := true
  m
    | .main => branch id
        (push .work (fun state _ => if state then 7 else 8)
          (push .work (fun _ _ => 11) (goto fun _ => .cleanup)))
        (push .work (fun _ _ => 13) (goto fun _ => .cleanup))
    | .cleanup => pop .work (fun state top => state && top.isSome)
        (peek .work (fun state top => state || top.isSome)
          (load not (push .work (fun _ _ => 17) (goto fun _ => .done))))
    | .done => halt

-- Constructing `supportMachine` typechecks although its work alphabet has
-- neither a `Fintype` nor a computational equality instance.
example : supportMachine.Γ .work = (Nat → Nat) := rfl
example : Infinite (supportMachine.Γ .work) := inferInstance

-- The recursive continuation and both branch arms are in program support.
example : (fun _ : Nat => 11) ∈
    stmtPushSet supportMachine (supportMachine.m .main) .work := by
  simp [stmtPushSet, supportMachine]

example : (fun _ : Nat => 7) ∈
    stmtPushSet supportMachine (supportMachine.m .main) .work := by
  simp [stmtPushSet, supportMachine]

-- The finite state image records the value emitted by the other state too.
example : (fun _ : Nat => 8) ∈
    stmtPushSet supportMachine (supportMachine.m .main) .work := by
  simp [stmtPushSet, supportMachine]

example : (fun _ : Nat => 13) ∈
    stmtPushSet supportMachine (supportMachine.m .main) .work := by
  simp [stmtPushSet, supportMachine]

-- Pushes remain visible after pop/peek/load continuations.
example : (fun _ : Nat => 17) ∈
    stmtPushSet supportMachine (supportMachine.m .cleanup) .work := by
  simp [stmtPushSet, supportMachine]

example : false ∈ reachableAlphabet supportMachine .input := by
  simp [reachableAlphabet, supportMachine]

private def supportC₀ : supportMachine.Cfg :=
  _root_.Turing.initList supportMachine [false, true]

private def supportC₁ : supportMachine.Cfg :=
  _root_.Turing.TM2.stepAux (supportMachine.m .main) supportC₀.var supportC₀.stk

private def supportC₂ : supportMachine.Cfg :=
  _root_.Turing.TM2.stepAux (supportMachine.m .cleanup) supportC₁.var supportC₁.stk

private def supportHalted : supportMachine.Cfg where
  l := none
  var := false
  stk := fun _ => []

example : CfgAlphabetBounded supportMachine supportC₀ :=
  initList_alphabetBounded supportMachine [false, true]

-- The arbitrary-statement theorem is used only with its essential support premise.
example : CfgAlphabetBounded supportMachine supportC₁ := by
  apply stepAux_alphabetBounded supportMachine
      (fun k => stmtPushSet_program_subset supportMachine .main k)
      (initList_alphabetBounded supportMachine [false, true])
  rfl

-- Specialized one-step preservation discharges the program-support premise.
example : CfgAlphabetBounded supportMachine supportC₁ := by
  apply step_alphabetBounded supportMachine
      (initList_alphabetBounded supportMachine [false, true])
  rfl

-- Two concrete machine steps preserve the invariant.
example : CfgAlphabetBounded supportMachine supportC₂ := by
  apply evalsInSteps_alphabetBounded supportMachine (n := 2)
      (initList_alphabetBounded supportMachine [false, true])
  rfl

-- A halted configuration is absorbing for every positive bind iteration.
example (n : Nat) (c' : supportMachine.Cfg) :
    (flip bind supportMachine.step)^[n + 1] (some supportHalted) ≠ some c' := by
  induction n with
  | zero =>
      change supportMachine.step supportHalted ≠ some c'
      simp [supportHalted, _root_.Turing.FinTM2.step, _root_.Turing.TM2.step]
  | succ n ih =>
      rw [Nat.succ_add, Function.iterate_succ_apply]
      exact ih

example : Set.Finite {a | a ∈ reachableAlphabet supportMachine .work} :=
  reachableAlphabet_finite supportMachine .work

private abbrev EmptyInputΓ : SupportK → Type
  | .input => Empty
  | .work => Nat → Nat

/-- Empty finite input alphabets still permit an infinite internal alphabet. -/
private abbrev emptyInputMachine : _root_.Turing.FinTM2 where
  K := SupportK
  k₀ := .input
  k₁ := .input
  Γ := EmptyInputΓ
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := push .work (fun _ _ => 42) halt

example : CfgAlphabetBounded emptyInputMachine
    (_root_.Turing.initList emptyInputMachine []) :=
  initList_alphabetBounded emptyInputMachine []

example : (fun _ : Nat => 42) ∈ reachableAlphabet emptyInputMachine .work := by
  simp [reachableAlphabet, stmtPushSet, emptyInputMachine]

end CLRS.Chapter34.Turing.CookLevin
