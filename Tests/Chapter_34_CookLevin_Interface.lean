import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit

namespace CLRS.Chapter34

#check CircuitGate
#check Circuit
#check CircuitGate.ValidAt
#check CircuitGate.evalWith
#check Circuit.WellFormed
#check Circuit.wellFormedGatesAux
#check Circuit.wellFormedGatesAux_eq_true_iff
#check Circuit.evalValues
#check Circuit.eval
#check Circuit.evalValues_size
#check Circuit.evalPrefix_push
#check Circuit.evalPrefix_gate_value
#check Circuit.evalValues_getElem_eq_evalPrefix
#check CircuitGate.GateEquation
#check Circuit.evalValues_getElem_eq_gateEquation
#check Circuit.eval_eq_getElem
#check GeneralCircuitSatisfiable

private def interfaceFanOutCircuit : Circuit where
  inputCount := 1
  gates := [.input 0, .not 0, .and 0 1, .or 0 1]
  output := 2

example : interfaceFanOutCircuit.WellFormed := by decide

example : interfaceFanOutCircuit.evalValues (fun _ => true) = #[true, false, false, true] := by
  native_decide

example : interfaceFanOutCircuit.eval (fun _ => true) = false := by
  native_decide

private def interfaceInvalidInputCircuit : Circuit where
  inputCount := 1
  gates := [.input 1]
  output := 0

example : ¬interfaceInvalidInputCircuit.WellFormed := by decide

private def interfaceSelfReferenceCircuit : Circuit where
  inputCount := 0
  gates := [.not 0]
  output := 0

example : ¬interfaceSelfReferenceCircuit.WellFormed := by decide

private def interfaceInvalidOutputCircuit : Circuit where
  inputCount := 1
  gates := [.input 0]
  output := 1

example : ¬interfaceInvalidOutputCircuit.WellFormed := by decide

#check CircuitSym
#check encNat
#check decNat
#check decNat_encNat
#check encodeCircuitGate
#check encodeCircuit
#check decodeCircuitGate
#check decodeCircuit
#check decodeCircuit_encodeCircuit
#check encodeCircuit_of_decodeCircuit_eq_some
#check inputCount_lt_length_of_decodeCircuit_eq_some
#check encodeCircuit_length_le
#check GeneralCircuitSAT
#check encodeCircuit_mem_generalCircuitSAT_iff
#check not_mem_generalCircuitSAT_of_decode_none

example : decNat (encNat 3 ++ [.inputMark]) = some (3, [.inputMark]) := by
  exact decNat_encNat 3 [.inputMark]

example : decodeCircuit (encodeCircuit interfaceFanOutCircuit) =
    some interfaceFanOutCircuit := by
  exact decodeCircuit_encodeCircuit interfaceFanOutCircuit

example {x : List CircuitSym}
    (h : decodeCircuit x = some interfaceFanOutCircuit) :
    encodeCircuit interfaceFanOutCircuit = x := by
  exact encodeCircuit_of_decodeCircuit_eq_some h

example : interfaceFanOutCircuit.inputCount <
    (encodeCircuit interfaceFanOutCircuit).length := by
  exact inputCount_lt_length_of_decodeCircuit_eq_some
    (decodeCircuit_encodeCircuit interfaceFanOutCircuit)

example : decodeCircuit [] = none := by native_decide

example : decodeCircuit (encodeCircuit interfaceFanOutCircuit ++ [.argMark]) = none := by
  native_decide

example : decodeCircuit (encodeCircuit interfaceInvalidInputCircuit) =
    some interfaceInvalidInputCircuit := by
  exact decodeCircuit_encodeCircuit interfaceInvalidInputCircuit

example : encodeCircuit interfaceInvalidInputCircuit ∉ GeneralCircuitSAT := by
  rw [encodeCircuit_mem_generalCircuitSAT_iff]
  exact fun h => (by decide : ¬interfaceInvalidInputCircuit.WellFormed) h.1

example : decodeCircuit (encodeCircuit interfaceSelfReferenceCircuit) =
    some interfaceSelfReferenceCircuit := by
  exact decodeCircuit_encodeCircuit interfaceSelfReferenceCircuit

example : encodeCircuit interfaceSelfReferenceCircuit ∉ GeneralCircuitSAT := by
  rw [encodeCircuit_mem_generalCircuitSAT_iff]
  exact fun h => (by decide : ¬interfaceSelfReferenceCircuit.WellFormed) h.1

example : decodeCircuit (encodeCircuit interfaceInvalidOutputCircuit) =
    some interfaceInvalidOutputCircuit := by
  exact decodeCircuit_encodeCircuit interfaceInvalidOutputCircuit

example : encodeCircuit interfaceInvalidOutputCircuit ∉ GeneralCircuitSAT := by
  rw [encodeCircuit_mem_generalCircuitSAT_iff]
  exact fun h => (by decide : ¬interfaceInvalidOutputCircuit.WellFormed) h.1

example : (encodeCircuit interfaceFanOutCircuit).length ≤
    12 * (interfaceFanOutCircuit.gates.length + 1) *
      (interfaceFanOutCircuit.gates.length + interfaceFanOutCircuit.inputCount + 1) := by
  exact encodeCircuit_length_le interfaceFanOutCircuit (by decide)

#check Turing.CookLevin.stmtPushSet
#check Turing.CookLevin.reachableAlphabet
#check Turing.CookLevin.CfgAlphabetBounded
#check Turing.CookLevin.initList_alphabetBounded
#check Turing.CookLevin.step_alphabetBounded
#check Turing.CookLevin.evalsInSteps_alphabetBounded
#check Turing.CookLevin.reachableAlphabet_finite
#check Turing.CookLevin.StackBits.Represents
#check Turing.CookLevin.StackBits.Represents.rawDecodable
#check Turing.CookLevin.represents_hasCapacity_iff
#check Turing.CookLevin.pushStackBits_represents
#check Turing.CookLevin.peekStackBits_represents
#check Turing.CookLevin.popStackBits_represents
#check Turing.CookLevin.popStackBits_encodeBoundedStackBits
#check Turing.CookLevin.pushStackBits_encodeBoundedStackBits
#check Turing.CookLevin.evalBundle_stack_represents
#check Turing.CookLevin.SymbolWires
#check Turing.CookLevin.HeadWires
#check Turing.CookLevin.pushStackWires_represents
#check Turing.CookLevin.peekStackWires_represents
#check Turing.CookLevin.popStackWires
#check Turing.CookLevin.stackCapacity_eval_iff
#check Turing.CookLevin.pushCfgWires_represents_of_evalBundle
#check Turing.CookLevin.popCfgWires_represents_of_evalBundle
#check Turing.CookLevin.cfgStackCapacity_eval_iff_length_lt
#check Turing.CookLevin.OneHotMapResult
#check Turing.CookLevin.oneHotMap
#check Turing.CookLevin.oneHotMap_gate_delta
#check Turing.CookLevin.oneHotMap_eval
#check Turing.CookLevin.oneHotMap_eval_encodeOneHot
#check Turing.CookLevin.oneHotMap_oneHot
#check Turing.CookLevin.OneHotPairMapResult
#check Turing.CookLevin.oneHotPairMap
#check Turing.CookLevin.oneHotPairMap_gate_delta
#check Turing.CookLevin.oneHotPairMap_eval
#check Turing.CookLevin.oneHotPairMap_eval_encodeOneHot
#check Turing.CookLevin.OneHotPredicateResult
#check Turing.CookLevin.oneHotPredicate
#check Turing.CookLevin.oneHotPredicate_gate_delta
#check Turing.CookLevin.oneHotPredicate_gate_bound
#check Turing.CookLevin.oneHotPredicate_eval
#check Turing.CookLevin.oneHotPredicate_eval_encodeOneHot
#check Turing.CookLevin.StateWires
#check Turing.CookLevin.StateBits
#check Turing.CookLevin.evalStateBits
#check Turing.CookLevin.LabelWires
#check Turing.CookLevin.LabelBits
#check Turing.CookLevin.evalLabelBits
#check Turing.CookLevin.CfgBundle.replaceState
#check Turing.CookLevin.CfgBundle.replaceStatus
#check Turing.CookLevin.evalCfgBits_replaceState
#check Turing.CookLevin.evalCfgBits_replaceStatus
#check Turing.CookLevin.encodeStateWires
#check Turing.CookLevin.encodeStateWires_eval
#check Turing.CookLevin.encodeLabelWires
#check Turing.CookLevin.encodeLabelWires_eval
#check Turing.CookLevin.encodeLabelHaltedWire
#check Turing.CookLevin.encodeLabelHaltedWire_eval
#check Turing.CookLevin.evalBundle_eq_some_canonical
#check Turing.CookLevin.evalStateBits_of_evalBundle
#check Turing.CookLevin.evalLabelBits_of_evalBundle
#check Turing.CookLevin.evalHaltedBit_of_evalBundle
#check Turing.CookLevin.evalBundle_replaceState
#check Turing.CookLevin.evalBundle_replaceStatus
#check Turing.CookLevin.cfgPushStack
#check Turing.CookLevin.cfgPopStack
#check Turing.CookLevin.pushCfgWires_evalBundle
#check Turing.CookLevin.peekCfgWires_head_eq_encode_of_evalBundle
#check Turing.CookLevin.popCfgWires_head_eq_encode_of_evalBundle
#check Turing.CookLevin.popCfgWires_evalBundle
#check Turing.CookLevin.compileStmtGateCost
#check Turing.CookLevin.compileStmtGateCoefficient
#check Turing.CookLevin.compileStmtGateCost_le
#check Turing.CookLevin.CompileStmtResult
#check Turing.CookLevin.compileStmt
#check Turing.CookLevin.compileStmt_gate_delta
#check Turing.CookLevin.compileStmt_evalBundle
#check Turing.CookLevin.compileStmt_gate_count_le
#check Turing.CookLevin.compileStmt_proof_irrel
#check Turing.CookLevin.dispatchGateCost
#check Turing.CookLevin.dispatchGateCoefficient
#check Turing.CookLevin.dispatchGateCost_le
#check Turing.CookLevin.dispatchLabels_gate_delta
#check Turing.CookLevin.dispatchLabels_gate_count_le
#check Turing.CookLevin.transitionCircuitGateCost
#check Turing.CookLevin.transitionCircuitGateCoefficient
#check Turing.CookLevin.transitionCircuitGateCost_le
#check Turing.CookLevin.TransitionCircuitResult
#check Turing.CookLevin.transitionCircuit
#check Turing.CookLevin.transitionCircuit_gate_delta
#check Turing.CookLevin.transitionCircuit_gate_count_le
#check Turing.CookLevin.transitionCircuit_eval_iff
#check Turing.CookLevin.transitionCircuit_sound
#check Turing.CookLevin.validCfgGateCoefficient
#check Turing.CookLevin.validCfgGateCost_le
#check Turing.CookLevin.validCfgCircuit_gate_count_le
#check Turing.CookLevin.validCfgCircuitFinished
#check Turing.CookLevin.validCfgCircuit_finish_wellFormed
#check Turing.CookLevin.validCfgCircuit_finish_eval
#check Turing.CookLevin.validCfgCircuitFinished_proof_irrel
#check Turing.CookLevin.transitionCircuitFinished
#check Turing.CookLevin.transitionCircuit_finish_wellFormed
#check Turing.CookLevin.transitionCircuit_finish_eval
#check Turing.CookLevin.transitionCircuitFinished_proof_irrel

-- Normalized verifier witnesses and their polynomial execution envelope
-- (Cook--Levin circuitization, milestone 9).
#check Turing.CookLevin.VerifierWitness
#check Turing.CookLevin.VerifierWitness.ofPolyTimeVerifiable
#check Turing.CookLevin.VerifierWitness.ofPolyTimeVerifiable_proof_irrel
#check Turing.CookLevin.pairEncoding_length
#check Turing.CookLevin.VerifierWitness.machineInput_length
#check Turing.CookLevin.verifierInputBound
#check Turing.CookLevin.verifierInputBound_eval
#check Turing.CookLevin.VerifierWitness.pairEncoding_length_le_inputBound
#check Turing.CookLevin.verifierHorizon
#check Turing.CookLevin.verifierHorizon_eval
#check Turing.CookLevin.VerifierWitness.machineTime_lt_horizon
#check Turing.CookLevin.VerifierWitness.machineTime_le_horizon
#check Turing.CookLevin.VerifierWitness.outputsInHorizon
#check Turing.CookLevin.VerifierWitness.stutter_horizon_eq_haltList
#check Turing.CookLevin.verifierHeight
#check Turing.CookLevin.verifierHeight_eval
#check Turing.CookLevin.VerifierWitness.machineInput_length_le_height
#check Turing.CookLevin.VerifierWitness.stack_length_le_height

-- Whole-tableau consecutive row layout and proof-carrying allocation.
#check Turing.CookLevin.tableauRowCount
#check Turing.CookLevin.tableauInputCount
#check Turing.CookLevin.tableauRowLayoutAt
#check Turing.CookLevin.tableauRowLayout
#check Turing.CookLevin.tableauRowLayout_finish
#check Turing.CookLevin.tableauRowLayout_fits
#check Turing.CookLevin.tableauRowLayout_disjoint
#check Turing.CookLevin.tableauRowLayout_index_ne
#check Turing.CookLevin.TableauRowsAllocation
#check Turing.CookLevin.allocateTableauRowsAt
#check Turing.CookLevin.allocateTableauRowsAt_proof_irrel
#check Turing.CookLevin.tableauStart
#check Turing.CookLevin.allocateTableauRows
#check Turing.CookLevin.allocateTableauRows_inputCount
#check Turing.CookLevin.allocateTableauRows_gate_delta
#check Turing.CookLevin.allocateTableauRows_gates_eq
#check Turing.CookLevin.allocateTableauRows_row_valid
#check Turing.CookLevin.allocateTableauRows_wire_ne
#check Turing.CookLevin.writeTableauBitsAt
#check Turing.CookLevin.writeTableauBitsAt_at
#check Turing.CookLevin.writeTableauBitsAt_outside
#check Turing.CookLevin.writeTableauBits
#check Turing.CookLevin.TableauRowsAllocation.evalCfgBits_writeTableau

-- Exact boundary constraints (milestone 8G).
#check Turing.CookLevin.BoundaryCircuitResult
#check Turing.CookLevin.staticCfgWires
#check Turing.CookLevin.staticCfgWires_eval
#check Turing.CookLevin.initialCfgCircuitGateCost
#check Turing.CookLevin.initialCfgCircuit
#check Turing.CookLevin.initialCfgCircuit_gate_delta
#check Turing.CookLevin.initialCfgCircuit_eval_iff
#check Turing.CookLevin.AcceptingOutputFits
#check Turing.CookLevin.acceptingOutputCircuitGateCost
#check Turing.CookLevin.acceptingOutputCircuit
#check Turing.CookLevin.acceptingOutputCircuit_gate_delta
#check Turing.CookLevin.acceptingOutputCircuit_eval_iff
#check Turing.CookLevin.symbolicInitialCfgWires
#check Turing.CookLevin.symbolicInitialCfgCircuit
#check Turing.CookLevin.symbolicInitialCfgCircuit_gate_delta
#check Turing.CookLevin.symbolicInitialCfgCircuit_eval_iff
#check Turing.CookLevin.FreshTransitionCircuitAtResult
#check Turing.CookLevin.freshTransitionCircuitAt
#check Turing.CookLevin.freshTransitionCircuitAt_gate_delta
#check Turing.CookLevin.freshTransitionCircuitAt_complete_nat
#check Turing.CookLevin.freshTransitionRowsAt_wire_ne
#check Turing.CookLevin.freshTransitionInputsAt_outside
#check Turing.CookLevin.FreshTransitionCircuitResult
#check Turing.CookLevin.freshTransitionCircuit
#check Turing.CookLevin.freshTransitionCircuit_gate_delta
#check Turing.CookLevin.freshTransitionCircuit_complete
#check Turing.CookLevin.freshTransitionCircuit_sound
#check Turing.CookLevin.verifierCircuit_satisfiable_iff
#check Turing.CookLevin.verifierCircuitInputBound
#check Turing.CookLevin.verifierCircuit_input_count_le
#check Turing.CookLevin.verifierCircuitEncodingBound
#check Turing.CookLevin.verifierCircuit_encoding_length_le

-- Function-level Cook--Levin reduction map.
#check Turing.CookLevin.cookLevinMap
#check Turing.CookLevin.cookLevinMap_mem_generalCircuitSAT_iff
#check Turing.CookLevin.cookLevinMap_length_le
#check Turing.CookLevin.VerifierWitness.alphabetFintype
#check Turing.CookLevin.verifierHorizonClock_length
#check Turing.CookLevin.verifierHorizonClock_computableInPolyTime
#check Turing.CookLevin.verifierHeightClock_length
#check Turing.CookLevin.verifierHeightClock_computableInPolyTime
#check Turing.CookLevin.verifierGateBoundClock_computableInPolyTime
#check Turing.CookLevin.verifierEncodingBoundClock_computableInPolyTime
#check Turing.CookLevin.verifierTableauInputPolynomial_eval
#check Turing.CookLevin.verifierTableauInputClock_computableInPolyTime
#check Turing.CookLevin.verifierCircuitHeader_eq
#check Turing.CookLevin.verifierCircuitHeader_computableInPolyTime
#check Turing.CookLevin.verifierInputGateStream_eq
#check Turing.CookLevin.verifierInputGateStream_computableInPolyTime

-- Exact finite-certificate semantics for the target language.
#check generalCircuitVerifier_accepts_iff
#check mem_generalCircuitSAT_iff_exists_certificate
#check Turing.GeneralCircuitVerifier.generalCircuitVerifierComputableInPolyTime
#check generalCircuitSAT_verifiable
#check generalCircuitSAT_mem_ClassNP

-- Headline axiom audit for the newly sealed bridge layer.
#print axioms Turing.CookLevin.verifierCircuit_input_count_le
#print axioms Turing.CookLevin.verifierCircuit_encoding_length_le
#print axioms Turing.CookLevin.cookLevinMap_mem_generalCircuitSAT_iff
#print axioms mem_generalCircuitSAT_iff_exists_certificate

end CLRS.Chapter34
