import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Encoding

/-!
# General-circuit-to-SAT machine: internal encoding

The concrete reduction first rewrites a raw circuit into a guarded finite
record.  Natural numbers and chronological gate indices remain unary so later
TM2 controllers need no unbounded finite-control state.

Main definitions:

- `NormalizedCircuitSym`: the finite work alphabet;
- `encodeNormalizedCircuit`: the canonical indexed circuit record;
- `normalizeGeneralCircuit`: the total guarded map from raw circuit strings.
-/

namespace CLRS.Chapter34

/-- Finite work alphabet for guarded, index-annotated circuit records. -/
inductive NormalizedCircuitSym : Type
  | invalidMark | validMark
  | inputCountMark | outputIndexMark | gateCountMark | gateRowMark
  | inputGateMark | constFalseMark | constTrueMark
  | notGateMark | andGateMark | orGateMark
  | tick | fieldEnd | rowEnd
deriving DecidableEq, Repr, Fintype, Inhabited

/-- Encode a natural number as unary ticks followed by a field terminator. -/
def encodeNormalizedNat (n : Nat) : List NormalizedCircuitSym :=
  List.replicate n .tick ++ [.fieldEnd]

/-- Encode one gate using the normalized finite tags and unary operands. -/
def encodeNormalizedGate : CircuitGate → List NormalizedCircuitSym
  | .input inputIndex => .inputGateMark :: encodeNormalizedNat inputIndex
  | .const false => [.constFalseMark]
  | .const true => [.constTrueMark]
  | .not source => .notGateMark :: encodeNormalizedNat source
  | .and left right =>
      .andGateMark :: (encodeNormalizedNat left ++ encodeNormalizedNat right)
  | .or left right =>
      .orGateMark :: (encodeNormalizedNat left ++ encodeNormalizedNat right)

/-- Encode one gate row together with its chronological gate index. -/
def encodeNormalizedGateRow (gateIndex : Nat) (gate : CircuitGate) :
    List NormalizedCircuitSym :=
  .gateRowMark ::
    (encodeNormalizedNat gateIndex ++ encodeNormalizedGate gate ++ [.rowEnd])

/-- Encode gate rows starting from an explicit chronological index. -/
def encodeNormalizedGateRowsFrom : Nat → List CircuitGate →
    List NormalizedCircuitSym
  | _, [] => []
  | gateIndex, gate :: gates =>
      encodeNormalizedGateRow gateIndex gate ++
        encodeNormalizedGateRowsFrom (gateIndex + 1) gates

/-- Canonical guarded record for a decoded circuit.  This codec records syntax;
well-formedness is enforced by `normalizeGeneralCircuit`. -/
def encodeNormalizedCircuit (c : Circuit) : List NormalizedCircuitSym :=
  [.validMark, .inputCountMark] ++
    encodeNormalizedNat c.inputCount ++
    [.outputIndexMark] ++
    encodeNormalizedNat c.output ++
    [.gateCountMark] ++
    encodeNormalizedNat c.gates.length ++
    encodeNormalizedGateRowsFrom 0 c.gates

/-- Total guarded normalization.  Malformed and decoded-but-ill-formed raw
circuits share the single canonical invalid record. -/
def normalizeGeneralCircuit (input : List CircuitSym) :
    List NormalizedCircuitSym :=
  match decodeCircuit input with
  | some c =>
      if c.WellFormed then encodeNormalizedCircuit c else [.invalidMark]
  | none => [.invalidMark]

end CLRS.Chapter34
