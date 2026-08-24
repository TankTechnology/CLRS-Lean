import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Bounds

/-! # General-circuit formula emitter: guarded semantic interface -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Semantic encoder for the only two record shapes produced by the verified
normalizer. -/
def encodeGuardedCircuit : Option Circuit → List NormalizedCircuitSym
  | none => [.invalidMark]
  | some c => encodeNormalizedCircuit c

/-- Invalid records become false; valid records become the exact consistency
formula stream for their circuit. -/
def guardedCircuitFormulaList : Option Circuit → List FormulaSym
  | none => enc (.const false)
  | some c => generalCircuitFormulaList c

def guardedReverseSteps : Option Circuit → Nat
  | none => invalidReverseSteps
  | some c => reverseSuccessfulSteps c

/-- One total exact-run theorem for the guarded semantic input type. -/
theorem guarded_reverse_run (guarded : Option Circuit) :
    (flip Option.bind step)^[guardedReverseSteps guarded]
      (some (_root_.Turing.initList reverseMachine
        (encodeGuardedCircuit guarded))) =
    some (_root_.Turing.haltList reverseMachine
      (guardedCircuitFormulaList guarded).reverse) := by
  cases guarded with
  | none => simpa [guardedReverseSteps, encodeGuardedCircuit,
      guardedCircuitFormulaList] using invalid_reverse_run
  | some c => simpa [guardedReverseSteps, encodeGuardedCircuit,
      guardedCircuitFormulaList] using canonical_reverse_run c

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
