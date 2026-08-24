import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding

/-!
# General-circuit formula emitter: exact list encoding

These definitions expose the prefix-polish output stream directly, one gate
row at a time.  The later TM2 proof targets these lists rather than unfolding
the recursive `Formula` encoder inside machine configurations.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

/-- Prefix stream for the expression on the right-hand side of one circuit
gate equation. -/
def generalCircuitGateExprList (inputCount : Nat) : CircuitGate →
    List FormulaSym
  | .input inputIndex => varEnc inputIndex
  | .const value => [.lit value]
  | .not source => .notMark :: varEnc (inputCount + source)
  | .and left right =>
      .andMark :: (varEnc (inputCount + left) ++
        varEnc (inputCount + right))
  | .or left right =>
      .orMark :: (varEnc (inputCount + left) ++
        varEnc (inputCount + right))

/-- Prefix stream for one indexed gate-consistency equation. -/
def generalCircuitGateFormulaList (inputCount gateIndex : Nat)
    (gate : CircuitGate) : List FormulaSym :=
  .iffMark :: (varEnc (inputCount + gateIndex) ++
    generalCircuitGateExprList inputCount gate)

/-- Right-associated conjunction stream for a chronological gate suffix. -/
def generalCircuitGateFamilyListFrom (inputCount : Nat) :
    Nat → List CircuitGate → List FormulaSym
  | _, [] => [.lit true]
  | gateIndex, gate :: gates =>
      .andMark :: (generalCircuitGateFormulaList inputCount gateIndex gate ++
        generalCircuitGateFamilyListFrom inputCount (gateIndex + 1) gates)

/-- Exact prefix stream of the textbook general-circuit consistency formula. -/
def generalCircuitFormulaList (c : Circuit) : List FormulaSym :=
  .andMark :: (varEnc (c.inputCount + c.output) ++
    generalCircuitGateFamilyListFrom c.inputCount 0 c.gates)

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
