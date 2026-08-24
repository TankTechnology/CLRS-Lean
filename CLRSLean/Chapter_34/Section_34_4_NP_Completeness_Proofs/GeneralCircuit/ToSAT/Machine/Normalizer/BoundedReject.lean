import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Runtime

/-!
# Guarded circuit normalizer: bounded rejection composition
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- A configuration reaches the canonical invalid record within a stated
number of concrete machine steps. -/
def RejectsIn (start : machine.Cfg) (bound : Nat) : Prop :=
  Nonempty <| StateTransition.EvalsToInTime step start
    (some (haltList machine [.invalidMark])) bound

/-- Exact cleanup packaged in the bounded evaluator interface. -/
theorem cleanup_rejectsIn (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    RejectsIn
      (cfg (some .clearInput) state input output rows inputCount gateCount
        operand saved outputIndex)
      (clearAndEmitInvalidSteps input output rows inputCount gateCount operand
        saved outputIndex) := by
  exact ⟨{
    steps := clearAndEmitInvalidSteps input output rows inputCount gateCount
      operand saved outputIndex
    evals_in_steps := clearAndEmitInvalid_phase state input output rows
      inputCount gateCount operand saved outputIndex
    steps_le_m := le_rfl }⟩

/-- Prepend one exact transition to a bounded rejecting suffix. -/
theorem RejectsIn.before_step {start next : machine.Cfg} {rejectBound : Nat}
    (hstep : step start = some next) (hreject : RejectsIn next rejectBound) :
    RejectsIn start (rejectBound + 1) := by
  rcases hreject with ⟨hreject⟩
  have hprefix : EvalsToInTime step start (some next) 1 :=
    { steps := 1, evals_in_steps := hstep, steps_le_m := le_rfl }
  exact ⟨EvalsToInTime.trans step 1 rejectBound start next
    (some (haltList machine [.invalidMark])) hprefix hreject⟩

/-- Prepend an exact multi-step phase to a bounded rejecting suffix. -/
theorem RejectsIn.before_steps {start next : machine.Cfg}
    (phaseSteps : Nat) {rejectBound : Nat}
    (hrun : transition^[phaseSteps] (some start) = some next)
    (hreject : RejectsIn next rejectBound) :
    RejectsIn start (rejectBound + phaseSteps) := by
  rcases hreject with ⟨hreject⟩
  have hprefix : EvalsToInTime step start (some next) phaseSteps :=
    { steps := phaseSteps, evals_in_steps := hrun, steps_le_m := le_rfl }
  exact ⟨EvalsToInTime.trans step phaseSteps rejectBound start next
    (some (haltList machine [.invalidMark])) hprefix hreject⟩

/-- Weaken a local bound to any larger envelope. -/
theorem RejectsIn.mono {start : machine.Cfg} {small large : Nat}
    (hrun : RejectsIn start small) (hbound : small ≤ large) :
    RejectsIn start large := by
  rcases hrun with ⟨hrun⟩
  exact ⟨{ hrun with steps_le_m := hrun.steps_le_m.trans hbound }⟩

/-- A transition directly into cleanup rejects in cleanup cost plus one. -/
theorem rejectsInAfterCleanupStep {start : machine.Cfg} (state : State)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hstep : step start = some (cfg (some .clearInput) state input output rows
      inputCount gateCount operand saved outputIndex)) :
    RejectsIn start
      (clearAndEmitInvalidSteps input output rows inputCount gateCount operand
        saved outputIndex + 1) :=
  RejectsIn.before_step hstep
    (cleanup_rejectsIn state input output rows inputCount gateCount operand
      saved outputIndex)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
