import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.HamiltonianCycle.VerifierMachine.CyclePairs.Run
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# HAM-CYCLE consecutive-pair generator: polynomial runtime

This module packages the exact three-counter run as a fixed polynomial-time
TM2 and composes it with the verified reversal machine.  The public output is
the canonical forward serialization of every consecutive cycle edge.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs

open PolyBuilder

private theorem rowsStepsFrom_le (previous : Nat) (vertices : List Nat) :
    rowsStepsFrom previous vertices ≤
      7 * (previous + 2 * vertices.sum + vertices.length) := by
  induction vertices generalizing previous with
  | nil => simp [rowsStepsFrom]
  | cons current vertices ih =>
      have htail := ih current
      simp only [rowsStepsFrom, List.sum_cons, List.length_cons]
      omega

private theorem lastFrom_le (first : Nat) (rest : List Nat) :
    CliqueInstance.lastFrom first rest ≤ first + rest.sum := by
  induction rest generalizing first with
  | nil => simp [CliqueInstance.lastFrom]
  | cons next rest ih =>
      simp only [CliqueInstance.lastFrom, List.sum_cons]
      have h := ih next
      omega

private theorem encodeCliqueCertificate_length_eq (vertices : List Nat) :
    (encodeCliqueCertificate vertices).length =
      1 + vertices.sum + 2 * vertices.length := by
  have records : (vertices.flatMap encodeCliqueVertex).length =
      vertices.sum + 2 * vertices.length := by
    induction vertices with
    | nil => simp
    | cons vertex vertices ih =>
        simp only [List.flatMap_cons, List.length_append,
          encodeCliqueVertex_length, List.sum_cons, List.length_cons]
        omega
  simp [encodeCliqueCertificate, records]
  omega

/-- The exact controller cost is quadratically bounded by the physical
certificate encoding length. -/
theorem revSteps_le_input (vertices : List Nat) :
    revSteps vertices ≤
      50 * ((encodeCliqueCertificate vertices).length + 1) ^ 2 := by
  cases vertices with
  | nil => simp [revSteps, encodeCliqueCertificate]
  | cons first rest =>
      let inputLength := (encodeCliqueCertificate (first :: rest)).length
      have hrows := rowsStepsFrom_le first rest
      have hlast := lastFrom_le first rest
      have hlength := encodeCliqueCertificate_length_eq (first :: rest)
      simp only [List.sum_cons, List.length_cons] at hlength
      have hfirst : first ≤ inputLength := by
        simp only [inputLength] at *
        omega
      have hsum : rest.sum ≤ inputLength := by
        simp only [inputLength] at *
        omega
      have hcount : rest.length ≤ inputLength := by
        simp only [inputLength] at *
        omega
      simp only [revSteps]
      nlinarith [sq_nonneg (inputLength + 1)]

/-- The compiled fixed controller produces the reverse physical stream. -/
noncomputable def revComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate id
      (fun vertices : List Nat => (encodeCyclePairs vertices).reverse) where
  tm := compile revProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 50 * (Polynomial.X + 1) ^ 2
  outputsFun := fun vertices => by
    have builderRun := revRun vertices
    have compiledRun := compile_evalsToInTime revProgram builderRun
    have machineRun : EvalsToInTime
        (compile revProgram).step
        (_root_.Turing.initList (compile revProgram)
          (encodeCliqueCertificate vertices))
        (some (_root_.Turing.haltList (compile revProgram)
          (encodeCyclePairs vertices).reverse))
        (revSteps vertices) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime := revSteps_le_input vertices
    have polynomialBound : revSteps vertices ≤
        (50 * (Polynomial.X + 1) ^ 2).eval
          (encodeCliqueCertificate vertices).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        Polynomial.eval_ofNat] using htime
    have boundedRun : EvalsToInTime
        (compile revProgram).step
        (_root_.Turing.initList (compile revProgram)
          (encodeCliqueCertificate vertices))
        (some (_root_.Turing.haltList (compile revProgram)
          (encodeCyclePairs vertices).reverse))
        ((50 * (Polynomial.X + 1) ^ 2).eval
          (encodeCliqueCertificate vertices).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans polynomialBound⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- A fixed polynomial-time TM2 maps a canonical HAM certificate to the
canonical stream of its consecutive path edges and closing edge. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate id
      encodeCyclePairs := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      revComputableInPolyTime
      (reverse_computableInPolyTime (Γ := CliqueSym))
  simpa [Function.comp_def] using Classical.choice composed

/-- Semantic packaging of the same fixed machine at the pair-family
boundary used by the batch edge lookup stage. -/
noncomputable def pairsComputableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeCliqueCertificate
      (fun pairs => pairs.flatMap encodeCliqueEdge) cyclePairs := by
  let machine := computableInPolyTime
  exact
    { tm := machine.tm
      inputAlphabet := machine.inputAlphabet
      outputAlphabet := machine.outputAlphabet
      time := machine.time
      outputsFun := fun vertices => by
        simpa [encodeCyclePairs] using machine.outputsFun vertices }

end CLRS.Chapter34.Turing.HamiltonianCycle.VerifierMachine.CyclePairs
