import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Guarded

/-! # General-circuit formula emitter: polynomial-time machine -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open _root_.Turing

def stepBound (inputLength : Nat) : Nat :=
  16 * (inputLength + 1) ^ 2 + 2

theorem guardedReverseSteps_le (guarded : Option Circuit) :
    guardedReverseSteps guarded ≤
      stepBound (encodeGuardedCircuit guarded).length := by
  cases guarded with
  | none => simp [guardedReverseSteps, invalidReverseSteps, stepBound,
      encodeGuardedCircuit]
  | some c =>
      have h := reverseSuccessfulSteps_le c
      simpa [guardedReverseSteps, stepBound, encodeGuardedCircuit] using
        (show reverseSuccessfulSteps c ≤
            16 * ((encodeNormalizedCircuit c).length + 1) ^ 2 + 2 by
          omega)

/-- The reverse-output emitter returns the guarded formula within one uniform
quadratic budget. -/
theorem allGuardedInputsWithinPolynomial (guarded : Option Circuit) :
    Nonempty (TM2OutputsInTime reverseMachine
      (encodeGuardedCircuit guarded)
      (some (guardedCircuitFormulaList guarded).reverse)
      (stepBound (encodeGuardedCircuit guarded).length)) := by
  refine ⟨{
    steps := guardedReverseSteps guarded
    evals_in_steps := guarded_reverse_run guarded
    steps_le_m := guardedReverseSteps_le guarded }⟩

noncomputable def runtimePolynomial : Polynomial Nat :=
  16 * (Polynomial.X + 1) ^ 2 + 2

@[simp] theorem runtimePolynomial_eval (n : Nat) :
    runtimePolynomial.eval n = stepBound n := by
  simp [runtimePolynomial, stepBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

/-- Concrete polynomial-time TM2 implementation of guarded circuit formula
emission.  Its list output is reversed so the finite controller can push it
directly; a verified generic reversal removes this implementation detail. -/
noncomputable def reverseComputableInPolyTime :
    TM2ComputableInPolyTime encodeGuardedCircuit id
      (fun guarded => (guardedCircuitFormulaList guarded).reverse) where
  tm := reverseMachine
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := runtimePolynomial
  outputsFun := fun guarded => by
    simpa using Classical.choice (allGuardedInputsWithinPolynomial guarded)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
