import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Semantics

/-!
# General circuit satisfiability to SAT: encoded map

This file lifts the semantic consistency-formula construction to the honest
finite encodings used by the Chapter 34 languages.  The map is total: malformed
inputs and decoded but ill-formed circuits are sent to `false`.  Successful,
well-formed decodes are sent to the prefix encoding of
`generalCircuitToFormula`.

The final results are:

- `generalCircuitToSATMap_mem_SAT_iff`, exact language preservation on every
  raw input string;
- `generalCircuitToSATMap_length_le`, a coarse polynomial output-size bound in
  the raw input length.

The latter is the representation-size part of the textbook reduction.  A
concrete TM2 implementation and its running-time theorem are intentionally a
separate refinement boundary.
-/

namespace CLRS.Chapter34

/-! ## Total encoded reduction -/

/-- Total raw-string map from general-circuit encodings to formula encodings.
Malformed or ill-formed inputs map to the canonical encoding of `false`. -/
def generalCircuitToSATMap (input : List CircuitSym) : List FormulaSym :=
  match decodeCircuit input with
  | some c =>
      if c.WellFormed then enc (generalCircuitToFormula c)
      else enc (.const false)
  | none => enc (.const false)

/-- On a canonical well-formed circuit encoding, the total map is exactly the
encoding of the direct consistency formula. -/
lemma generalCircuitToSATMap_encodeCircuit (c : Circuit) (h : c.WellFormed) :
    generalCircuitToSATMap (encodeCircuit c) = enc (generalCircuitToFormula c) := by
  simp [generalCircuitToSATMap, decodeCircuit_encodeCircuit, h]

/-- The total encoded map preserves membership exactly, including malformed
and decoded-but-ill-formed raw inputs. -/
theorem generalCircuitToSATMap_mem_SAT_iff (input : List CircuitSym) :
    generalCircuitToSATMap input ∈ SAT ↔ input ∈ GeneralCircuitSAT := by
  cases hdecode : decodeCircuit input with
  | none =>
      simp [generalCircuitToSATMap, hdecode, SAT, decode_enc, Formula.Satisfiable,
        Formula.eval, GeneralCircuitSAT]
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
        subst input
        simp [generalCircuitToSATMap, decodeCircuit_encodeCircuit, hwellFormed,
          SAT, decode_enc, encodeCircuit_mem_generalCircuitSAT_iff,
          generalCircuitSatisfiable_iff_satisfiable_generalCircuitToFormula c hwellFormed]
      · simp [generalCircuitToSATMap, hdecode, hwellFormed, SAT, decode_enc,
          Formula.Satisfiable, Formula.eval, GeneralCircuitSAT,
          GeneralCircuitSatisfiable]

/-! ## Formula-encoding size -/

private lemma enc_generalCircuitGateExpr_length_le
    (c : Circuit) (i : Nat) (hi : i < c.gates.length)
    (gate : CircuitGate) (hvalid : gate.ValidAt c.inputCount i) :
    (enc (generalCircuitGateExpr c gate)).length ≤
      4 * (c.gates.length + c.inputCount + 1) := by
  cases gate with
  | input inputIndex =>
      simp [CircuitGate.ValidAt, generalCircuitGateExpr, enc, varEnc] at hvalid ⊢
      omega
  | const value =>
      simp [generalCircuitGateExpr, enc]
      omega
  | not source =>
      simp [CircuitGate.ValidAt, generalCircuitGateExpr, generalCircuitGateVar,
        enc, varEnc] at hvalid ⊢
      omega
  | and left right =>
      simp [CircuitGate.ValidAt, generalCircuitGateExpr, generalCircuitGateVar,
        enc, varEnc] at hvalid ⊢
      omega
  | or left right =>
      simp [CircuitGate.ValidAt, generalCircuitGateExpr, generalCircuitGateVar,
        enc, varEnc] at hvalid ⊢
      omega

private lemma enc_generalCircuitGateFormula_length_le
    (c : Circuit) (i : Nat) (hi : i < c.gates.length)
    (gate : CircuitGate) (hvalid : gate.ValidAt c.inputCount i) :
    (enc (generalCircuitGateFormula c i gate)).length ≤
      8 * (c.gates.length + c.inputCount + 1) := by
  have hexpr := enc_generalCircuitGateExpr_length_le c i hi gate hvalid
  simp only [generalCircuitGateFormula, enc, List.length_cons, List.length_append,
    varEnc, List.length_replicate, generalCircuitGateVar]
  omega

private lemma enc_generalCircuitGateFormulasAux_length_le
    (c : Circuit) (hwellFormed : c.WellFormed)
    (pre rest : List CircuitGate) (hsplit : c.gates = pre ++ rest) :
    (enc (generalCircuitGateFormulasAux c pre.length rest)).length ≤
      rest.length * (8 * (c.gates.length + c.inputCount + 1) + 1) + 1 := by
  induction rest generalizing pre with
  | nil => simp [generalCircuitGateFormulasAux, enc]
  | cons gate rest ih =>
      have hi : pre.length < c.gates.length := by
        rw [hsplit]
        simp
      have hgate : c.gates.get ⟨pre.length, hi⟩ = gate := by
        have hgateOption : c.gates[pre.length]? = some gate := by
          rw [hsplit]
          simp
        rw [List.getElem?_eq_getElem hi] at hgateOption
        exact Option.some.inj hgateOption
      have hvalid := hwellFormed.2 pre.length hi
      rw [hgate] at hvalid
      have hhead := enc_generalCircuitGateFormula_length_le
        c pre.length hi gate hvalid
      have htail := ih (pre := pre ++ [gate])
        (by simpa [List.append_assoc] using hsplit)
      have htail' :
          (enc (generalCircuitGateFormulasAux c (pre.length + 1) rest)).length ≤
            rest.length * (8 * (c.gates.length + c.inputCount + 1) + 1) + 1 := by
        simpa using htail
      simp only [generalCircuitGateFormulasAux, enc, List.length_cons,
        List.length_append, List.length_cons]
      rw [Nat.add_mul]
      simp only [one_mul]
      omega

/-- A well-formed circuit's generated formula encoding is polynomial in its
gate and input counts. -/
lemma generalCircuitToFormula_enc_length_le (c : Circuit) (h : c.WellFormed) :
    (enc (generalCircuitToFormula c)).length ≤
      16 * (c.gates.length + 1) * (c.gates.length + c.inputCount + 1) := by
  have hconstraints := enc_generalCircuitGateFormulasAux_length_le c h
    [] c.gates (by simp)
  have houtput := h.1
  simp only [generalCircuitToFormula, enc, List.length_cons, List.length_append,
    varEnc, List.length_replicate, generalCircuitGateVar]
  simp only [List.length_nil] at hconstraints
  nlinarith

private lemma gates_length_le_encodeCircuit_length (c : Circuit) :
    c.gates.length ≤ (encodeCircuit c).length := by
  have hgate : ∀ gate : CircuitGate, 1 ≤ (encodeCircuitGate gate).length := by
    intro gate
    cases gate with
    | input inputIndex => simp [encodeCircuitGate]
    | const value => cases value <;> simp [encodeCircuitGate]
    | not source => simp [encodeCircuitGate]
    | and left right => simp [encodeCircuitGate]
    | or left right => simp [encodeCircuitGate]
  have hflat : c.gates.length ≤ (c.gates.flatMap encodeCircuitGate).length := by
    induction c.gates with
    | nil => simp
    | cons gate gates ih =>
        simp only [List.length_cons, List.flatMap_cons, List.length_append]
        have := hgate gate
        omega
  simp only [encodeCircuit, List.length_append, List.length_cons]
  omega

/-- Coarse raw-input polynomial bound for the total map.  It is deliberately
stated only in terms of the input-string length, so malformed strings and
representation overhead are accounted for by the public theorem. -/
theorem generalCircuitToSATMap_length_le (input : List CircuitSym) :
    (generalCircuitToSATMap input).length ≤ 32 * (input.length + 1) ^ 3 := by
  cases hdecode : decodeCircuit input with
  | none =>
      simp only [generalCircuitToSATMap, hdecode, enc, List.length_singleton]
      have hpositive : 0 < 32 * (input.length + 1) ^ 3 := by positivity
      omega
  | some c =>
      by_cases hwellFormed : c.WellFormed
      · have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
        have hinputs := inputCount_lt_length_of_decodeCircuit_eq_some hdecode
        have hgates : c.gates.length ≤ input.length := by
          rw [← hcanonical]
          exact gates_length_le_encodeCircuit_length c
        have hformula := generalCircuitToFormula_enc_length_le c hwellFormed
        have hgates' : c.gates.length + 1 ≤ input.length + 1 := by omega
        have htotal : c.gates.length + c.inputCount + 1 ≤
            2 * (input.length + 1) := by omega
        simp only [generalCircuitToSATMap, hdecode, hwellFormed, if_pos]
        calc
          (enc (generalCircuitToFormula c)).length ≤
              16 * (c.gates.length + 1) *
                (c.gates.length + c.inputCount + 1) := hformula
          _ ≤ 16 * (input.length + 1) * (2 * (input.length + 1)) := by
              gcongr
          _ ≤ 32 * (input.length + 1) ^ 3 := by
              have hpositive : 1 ≤ input.length + 1 := by omega
              calc
                16 * (input.length + 1) * (2 * (input.length + 1)) =
                    32 * (input.length + 1) ^ 2 := by ring
                _ ≤ 32 * (input.length + 1) ^ 2 * (input.length + 1) :=
                  by simpa only [Nat.mul_one] using
                    Nat.mul_le_mul_left (32 * (input.length + 1) ^ 2) hpositive
                _ = 32 * (input.length + 1) ^ 3 := by ring
      · rw [show generalCircuitToSATMap input = enc (.const false) by
            simp [generalCircuitToSATMap, hdecode, hwellFormed]]
        simp only [enc, List.length_singleton]
        have hpositive : 0 < 32 * (input.length + 1) ^ 3 := by positivity
        omega

end CLRS.Chapter34
