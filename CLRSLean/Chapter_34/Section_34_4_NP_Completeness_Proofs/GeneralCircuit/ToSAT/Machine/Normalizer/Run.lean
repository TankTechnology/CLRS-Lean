import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.MalformedRun

/-!
# Guarded circuit normalizer: public exact run

This small facade packages total exact semantics in Mathlib's standard
`TM2OutputsInTime` interface.  The time parameter is the chosen exact run
length; the next layer replaces it with one uniform polynomial in input size.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

/-- The fixed normalizer outputs the guarded normalization on every raw input
in some finite number of steps. -/
theorem outputs (input : List CircuitSym) :
    ∃ steps,
      Nonempty (_root_.Turing.TM2OutputsInTime machine input
        (some (normalizeGeneralCircuit input)) steps) := by
  rcases normalizer_run input with ⟨steps, hrun⟩
  refine ⟨steps, ⟨{
    steps := steps
    evals_in_steps := ?_
    steps_le_m := le_rfl }⟩⟩
  change (flip Option.bind step)^[steps]
    (some (_root_.Turing.initList machine input)) =
      some (_root_.Turing.haltList machine (normalizeGeneralCircuit input))
  exact hrun

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
