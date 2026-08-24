import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.PolynomialRuntime
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-! # General-circuit formula emitter: forward polynomial-time interface -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Composing the direct emitter with the verified generic reversal machine
returns the forward exact formula stream. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime encodeGuardedCircuit id
      guardedCircuitFormulaList := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reverseComputableInPolyTime
      (PolyBuilder.reverse_computableInPolyTime (Γ := FormulaSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
