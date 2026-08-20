import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.Witness
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Configuration

/-!
# Cook--Levin polynomial execution envelope

For a normalized verifier witness, this module publishes polynomial input,
time-horizon, and stack-height bounds.  The bounded run retains the machine's
actual execution length; only its upper-bound proof is widened.  A separate
theorem converts that run into an exact-horizon stuttering equality.
-/

open Computability StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open _root_.Turing _root_.Turing.TM2

noncomputable section

/-- A uniform upper bound for a pair-encoded verifier input at instance size
`n`; the final `1` accounts for the separator. -/
def verifierInputBound {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  W.certificateBound + Polynomial.X + 1

@[simp] theorem verifierInputBound_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    (verifierInputBound W).eval n = W.certificateBound.eval n + n + 1 := by
  simp [verifierInputBound]

/-- Every admissible certificate gives a pair encoding below the uniform
input bound. -/
theorem VerifierWitness.pairEncoding_length_le_inputBound {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    (pairEncoding c x).length ≤ (verifierInputBound W).eval x.length := by
  rw [pairEncoding_length, verifierInputBound_eval]
  omega

/-- The verifier's polynomial time evaluated at the uniform input bound, plus
one.  The extra step makes the envelope strictly larger than the original
machine bound. -/
def verifierHorizon {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  W.machine.time.comp (verifierInputBound W) + 1

@[simp] theorem verifierHorizon_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    (verifierHorizon W).eval n =
      W.machine.time.eval ((verifierInputBound W).eval n) + 1 := by
  simp [verifierHorizon]

/-- The machine's native pair-input time bound is strictly below the uniform
horizon. -/
theorem VerifierWitness.machineTime_lt_horizon {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    W.machine.time.eval (pairEncoding c x).length <
      (verifierHorizon W).eval x.length := by
  rw [verifierHorizon_eval]
  exact Nat.lt_succ_of_le
    (Turing.TM2Comp.Polynomial.eval_mono_nat
      (W.pairEncoding_length_le_inputBound hc))

/-- Non-strict form of `machineTime_lt_horizon`, convenient for widening an
`EvalsToInTime` proof. -/
theorem VerifierWitness.machineTime_le_horizon {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    W.machine.time.eval (pairEncoding c x).length ≤
      (verifierHorizon W).eval x.length :=
  Nat.le_of_lt (W.machineTime_lt_horizon hc)

/-- The original verifier run, with its actual step count unchanged and only
the recorded upper bound widened to the uniform horizon. -/
def VerifierWitness.outputsInHorizon {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    TM2OutputsInTime W.machine.tm
      (List.map W.machine.inputAlphabet.invFun (pairEncoding c x))
      (some (List.map W.machine.outputAlphabet.invFun
        (boolEncoding (W.verify c x))))
      ((verifierHorizon W).eval x.length) := by
  let run := W.machine.outputsFun (c, x)
  have hbound := W.machineTime_le_horizon hc
  exact { run with steps_le_m := run.steps_le_m.trans hbound }

/-- At the uniform horizon the padded/stuttering computation is exactly the
canonical halt configuration carrying the verifier's Boolean output. -/
theorem VerifierWitness.stutter_horizon_eq_haltList {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    (stutterStep W.machine.tm)^[(verifierHorizon W).eval x.length]
        (initList W.machine.tm
          (List.map W.machine.inputAlphabet.invFun (pairEncoding c x))) =
      haltList W.machine.tm
        (List.map W.machine.outputAlphabet.invFun
          (boolEncoding (W.verify c x))) := by
  exact (tm2OutputsInTime_iff_stutter_haltList W.machine.tm _ _ _).mp
    ⟨W.outputsInHorizon hc⟩

/-- Polynomial height sufficient for the initial verifier input and for every
stack at every row up to the uniform horizon.  The final machine-static
summand reserves two cells per possible selected-stack action.  This slack is
semantically inert (the cells remain blank) and lets the concrete transition
generator normalize an arbitrary fixed push/pop sequence without crossing the
public stack boundary. -/
def verifierHeight {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    Polynomial Nat :=
  verifierInputBound W +
    verifierHorizon W * Polynomial.C (maxPushesPerStep W.machine.tm) +
    Polynomial.C (2 * maxStackActionsPerStep W.machine.tm)

@[simp] theorem verifierHeight_eval {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    (verifierHeight W).eval n =
      (verifierInputBound W).eval n +
        (verifierHorizon W).eval n * maxPushesPerStep W.machine.tm +
        2 * maxStackActionsPerStep W.machine.tm := by
  simp [verifierHeight]

/-- The published height contains the complete machine-static routing slack;
the extra unit comes from the mandatory pair-encoding separator in the input
envelope. -/
theorem verifierHeight_actionPadding_le {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (n : Nat) :
    2 * maxStackActionsPerStep W.machine.tm + 1 ≤
      (verifierHeight W).eval n := by
  rw [verifierHeight_eval, verifierInputBound_eval]
  omega

/-- The mapped initial verifier input itself fits the published height. -/
theorem VerifierWitness.machineInput_length_le_height {Γ : Type}
    {L : Language Γ} (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length) :
    (List.map W.machine.inputAlphabet.invFun (pairEncoding c x)).length ≤
      (verifierHeight W).eval x.length := by
  rw [W.machineInput_length, verifierHeight_eval]
  refine le_trans
    (by simpa only [pairEncoding_length] using
      W.pairEncoding_length_le_inputBound hc)
    ?_
  omega

/-- Every machine stack at every row no later than the horizon fits the
published polynomial height. -/
theorem VerifierWitness.stack_length_le_height {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) {c x : List Γ}
    (hc : c.length ≤ W.certificateBound.eval x.length)
    {t : Nat} (ht : t ≤ (verifierHorizon W).eval x.length)
    (k : W.machine.tm.K) :
    (((stutterStep W.machine.tm)^[t]
      (initList W.machine.tm
        (List.map W.machine.inputAlphabet.invFun (pairEncoding c x)))).stk k).length ≤
      (verifierHeight W).eval x.length := by
  refine le_trans (stack_length_at_horizon_le W.machine.tm _ ht k) ?_
  rw [verifierHeight_eval]
  have hinput :
      (List.map W.machine.inputAlphabet.invFun
        (pairEncoding c x)).length ≤
        (verifierInputBound W).eval x.length := by
    simpa only [List.length_map] using
      W.pairEncoding_length_le_inputBound hc
  omega

end

end CLRS.Chapter34.Turing.CookLevin
