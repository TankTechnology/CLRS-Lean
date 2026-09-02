import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectPhases

/-!
# Concrete verifier: bounded rejection composition

This module refines the qualitative rejection relation with an explicit step
budget.  It supplies the small composition API used to lift every rejecting
verifier phase without changing the underlying machine.

Main results:

- Definition `RejectsIn`: canonical rejection within a stated step bound.
- Theorem `RejectsIn.before_steps`: compose an exact prefix with a bounded
  rejection suffix.
- Theorem `RejectsIn.mono`: weaken a local exact bound to a common envelope.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- A configuration reaches the canonical one-symbol rejection halt within
the stated number of machine steps. -/
def RejectsIn (start : machine.Cfg) (bound : Nat) : Prop :=
  Nonempty <| StateTransition.EvalsToInTime step start
    (some (haltList machine [false])) bound

/-- Forgetting the quantitative budget recovers the existing rejection API. -/
theorem RejectsIn.rejects {start : machine.Cfg} {bound : Nat}
    (hrun : RejectsIn start bound) : Rejects start := by
  rcases hrun with ⟨hrun⟩
  exact ⟨hrun.steps, hrun.evals_in_steps⟩

/-- A one-step transition into cleanup rejects in the exact cleanup cost plus
that initial step. -/
theorem rejectsIn_after_cleanup_step (start : machine.Cfg) (state : State)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (gateCount index saved : Nat)
    (hstep : step start = some (cfg (some (.clearInput false)) state input []
      certificate values scratch gateCount index saved)) :
    RejectsIn start
      (cleanupSteps input certificate values scratch gateCount index saved + 1) := by
  refine ⟨{
    steps := cleanupSteps input certificate values scratch gateCount index saved + 1
    evals_in_steps := ?_
    steps_le_m := Nat.le_refl _ }⟩
  exact step_then _ hstep
    (cleanup_phase state false input certificate values scratch gateCount index saved)

/-- Bounded rejection is closed under one preceding concrete transition. -/
theorem RejectsIn.before_step {start next : machine.Cfg} {rejectBound : Nat}
    (hstep : step start = some next) (hreject : RejectsIn next rejectBound) :
    RejectsIn start (rejectBound + 1) := by
  rcases hreject with ⟨hreject⟩
  have hprefix : EvalsToInTime step start (some next) 1 := by
    refine { steps := 1, evals_in_steps := ?_, steps_le_m := Nat.le_refl 1 }
    exact hstep
  exact ⟨EvalsToInTime.trans step 1 rejectBound start next
    (some (haltList machine [false])) hprefix hreject⟩

/-- Compose an exact prefix phase with a bounded rejecting suffix. -/
theorem RejectsIn.before_steps {start next : machine.Cfg}
    (phaseSteps : Nat) {rejectBound : Nat}
    (hrun : transition^[phaseSteps] (some start) = some next)
    (hreject : RejectsIn next rejectBound) :
    RejectsIn start (rejectBound + phaseSteps) := by
  rcases hreject with ⟨hreject⟩
  have hprefix : EvalsToInTime step start (some next) phaseSteps :=
    { steps := phaseSteps
      evals_in_steps := hrun
      steps_le_m := Nat.le_refl phaseSteps }
  exact ⟨EvalsToInTime.trans step phaseSteps rejectBound start next
    (some (haltList machine [false])) hprefix hreject⟩

/-- A bounded rejecting run remains valid under any larger budget. -/
theorem RejectsIn.mono {start : machine.Cfg} {small large : Nat}
    (hrun : RejectsIn start small) (hbound : small ≤ large) :
    RejectsIn start large := by
  rcases hrun with ⟨hrun⟩
  exact ⟨{ hrun with steps_le_m := hrun.steps_le_m.trans hbound }⟩

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
