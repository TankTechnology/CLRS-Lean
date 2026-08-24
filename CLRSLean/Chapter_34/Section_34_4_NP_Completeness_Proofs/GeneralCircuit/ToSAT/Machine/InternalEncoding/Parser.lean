import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.InternalEncoding.Basic

/-!
# Guarded circuit work-record parser

The parser consumes every delimiter and every chronological row index.  A
successful top-level decode therefore represents one complete canonical work
record with no trailing symbols.
-/

namespace CLRS.Chapter34

/-- Decode one terminated unary work-field and return its unused suffix. -/
def decodeNormalizedNat : List NormalizedCircuitSym →
    Option (Nat × List NormalizedCircuitSym)
  | [] => none
  | .tick :: rest =>
      (decodeNormalizedNat rest).map fun (value, suffix) =>
        (value + 1, suffix)
  | .fieldEnd :: rest => some (0, rest)
  | _ => none

/-- Decode one normalized gate body and return its unused suffix. -/
def decodeNormalizedGate : List NormalizedCircuitSym →
    Option (CircuitGate × List NormalizedCircuitSym)
  | .inputGateMark :: rest => do
      let (inputIndex, suffix) ← decodeNormalizedNat rest
      pure (.input inputIndex, suffix)
  | .constFalseMark :: rest => some (.const false, rest)
  | .constTrueMark :: rest => some (.const true, rest)
  | .notGateMark :: rest => do
      let (source, suffix) ← decodeNormalizedNat rest
      pure (.not source, suffix)
  | .andGateMark :: rest => do
      let (left, middle) ← decodeNormalizedNat rest
      let (right, suffix) ← decodeNormalizedNat middle
      pure (.and left right, suffix)
  | .orGateMark :: rest => do
      let (left, middle) ← decodeNormalizedNat rest
      let (right, suffix) ← decodeNormalizedNat middle
      pure (.or left right, suffix)
  | _ => none

/-- Decode one gate row and check its explicit chronological index. -/
def decodeNormalizedGateRow (expectedIndex : Nat) :
    List NormalizedCircuitSym →
      Option (CircuitGate × List NormalizedCircuitSym)
  | .gateRowMark :: rest => do
      let (gateIndex, rest) ← decodeNormalizedNat rest
      if gateIndex = expectedIndex then
        let (gate, rest) ← decodeNormalizedGate rest
        match rest with
        | .rowEnd :: suffix => some (gate, suffix)
        | _ => none
      else none
  | _ => none

/-- Decode exactly `gateCount` chronological rows from `expectedIndex`. -/
def decodeNormalizedGateRowsFrom : Nat → Nat →
    List NormalizedCircuitSym →
      Option (List CircuitGate × List NormalizedCircuitSym)
  | _, 0, input => some ([], input)
  | expectedIndex, gateCount + 1, input => do
      let (gate, rest) ← decodeNormalizedGateRow expectedIndex input
      let (gates, suffix) ←
        decodeNormalizedGateRowsFrom (expectedIndex + 1) gateCount rest
      pure (gate :: gates, suffix)

/-- Decode a complete canonical valid record.  The invalid sentinel and every
malformed or trailing work stream decode to `none`. -/
def decodeNormalizedCircuit : List NormalizedCircuitSym → Option Circuit
  | .validMark :: .inputCountMark :: rest => do
      let (inputCount, rest) ← decodeNormalizedNat rest
      match rest with
      | .outputIndexMark :: rest => do
          let (output, rest) ← decodeNormalizedNat rest
          match rest with
          | .gateCountMark :: rest => do
              let (gateCount, rest) ← decodeNormalizedNat rest
              let (gates, trailing) ←
                decodeNormalizedGateRowsFrom 0 gateCount rest
              if trailing.isEmpty then
                some { inputCount, gates, output }
              else none
          | _ => none
      | _ => none
  | _ => none

end CLRS.Chapter34
