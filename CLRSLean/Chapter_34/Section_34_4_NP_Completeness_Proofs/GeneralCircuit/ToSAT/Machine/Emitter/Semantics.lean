import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.Encoding

/-!
# General-circuit formula emitter: list semantics
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- The exposed expression stream is the ordinary formula encoding. -/
theorem generalCircuitGateExprList_eq_enc (c : Circuit) (gate : CircuitGate) :
    generalCircuitGateExprList c.inputCount gate =
      enc (generalCircuitGateExpr c gate) := by
  cases gate <;> simp [generalCircuitGateExprList, generalCircuitGateExpr,
    generalCircuitGateVar, enc]

/-- The exposed indexed gate equation is the ordinary formula encoding. -/
theorem generalCircuitGateFormulaList_eq_enc (c : Circuit) (gateIndex : Nat)
    (gate : CircuitGate) :
    generalCircuitGateFormulaList c.inputCount gateIndex gate =
      enc (generalCircuitGateFormula c gateIndex gate) := by
  simp [generalCircuitGateFormulaList, generalCircuitGateFormula, enc,
    generalCircuitGateVar, generalCircuitGateExprList_eq_enc]

/-- Gate-family emission agrees with the recursive formula constructor at any
chronological starting index. -/
theorem generalCircuitGateFamilyListFrom_eq_enc (c : Circuit) :
    ∀ gateIndex gates,
      generalCircuitGateFamilyListFrom c.inputCount gateIndex gates =
        enc (generalCircuitGateFormulasAux c gateIndex gates)
  | _, [] => by simp [generalCircuitGateFamilyListFrom,
      generalCircuitGateFormulasAux, enc]
  | gateIndex, gate :: gates => by
      simp [generalCircuitGateFamilyListFrom,
        generalCircuitGateFormulasAux, enc,
        generalCircuitGateFormulaList_eq_enc,
        generalCircuitGateFamilyListFrom_eq_enc c (gateIndex + 1) gates]

/-- Whole list-level emission is exactly the pre-existing encoded formula. -/
theorem generalCircuitFormulaList_eq_enc (c : Circuit) :
    generalCircuitFormulaList c = enc (generalCircuitToFormula c) := by
  simp [generalCircuitFormulaList, generalCircuitToFormula, enc,
    generalCircuitGateVar, generalCircuitGateFamilyListFrom_eq_enc]

/-- Total emitter semantics on guarded records.  Every noncanonical record,
including the invalid sentinel, maps to the canonical false formula. -/
def emitNormalizedCircuitFormula (input : List NormalizedCircuitSym) :
    List FormulaSym :=
  match decodeNormalizedCircuit input with
  | some c => generalCircuitFormulaList c
  | none => enc (.const false)

/-- Normalization followed by list-level emission is definitionally the
existing total raw-string reduction map. -/
theorem emit_normalize_eq (input : List CircuitSym) :
    emitNormalizedCircuitFormula (normalizeGeneralCircuit input) =
      generalCircuitToSATMap input := by
  cases hdecode : decodeCircuit input with
  | none =>
      simp [normalizeGeneralCircuit, hdecode, emitNormalizedCircuitFormula,
        generalCircuitToSATMap, decodeNormalizedCircuit, enc]
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · simp [normalizeGeneralCircuit, hdecode, hwellFormed,
          emitNormalizedCircuitFormula, decode_encodeNormalizedCircuit,
          generalCircuitToSATMap, generalCircuitFormulaList_eq_enc]
      · simp [normalizeGeneralCircuit, hdecode, hwellFormed,
          emitNormalizedCircuitFormula, decodeNormalizedCircuit,
          generalCircuitToSATMap, enc]

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
