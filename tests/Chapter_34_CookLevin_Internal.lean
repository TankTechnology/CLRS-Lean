import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackPrimitives
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.FiniteLookup
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StackCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ControlCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.PrimitiveRowSemantics

namespace CLRS.Chapter34.Turing.CookLevin

open Computability StateTransition
open _root_.Turing.TM2 _root_.Turing.TM2.Stmt

#check labelCount
#check stateCount
#check labelCount_pos
#check stateCount_pos
#check BoundedStack
#check BoundedStack.Valid
#check BoundedCfg
#check BoundedCfg.Valid
#check labelEquivFin
#check stateEquivFin
#check alphabetEquivFin
#check encodeCfg
#check encodeCfg_valid
#check decodeCfg?
#check decodeCfg
#check decodeCfg_encodeCfg
#check encodeCfg_decodeCfg
#check decoded_alphabetBounded
#check decoded_stack_length_le
#check stutterStep
#check stutterStep_halted
#check stutterStep_alphabetBounded
#check stutter_iterate_alphabetBounded
#check evalsToInTime_iff_stutter_accepts
#check tm2OutputsInTime_iff_stutter_haltList
#check stmtMaxPushes
#check maxPushesPerStep
#check stepAux_stack_length_le
#check stutterStep_stack_length_le
#check stack_length_iterate_le
#check stack_length_at_horizon_le
#check VerifierWitness
#check VerifierWitness.ofPolyTimeVerifiable
#check pairEncoding_length
#check verifierInputBound
#check verifierHorizon
#check VerifierWitness.outputsInHorizon
#check verifierHeight
#check VerifierWitness.stack_length_le_height
#check tableauRowCount
#check tableauInputCount
#check tableauRowLayout
#check TableauRowsAllocation
#check allocateTableauRowsAt
#check allocateTableauRows
#check writeTableauBits
#check TableauRowsAllocation.evalCfgBits_writeTableau
#check CircuitBuilder
#check CircuitBuilder.empty
#check CircuitBuilder.Wire
#check CircuitBuilder.WireValid
#check CircuitBuilder.Extends
#check CircuitBuilder.Extends.refl
#check CircuitBuilder.Extends.trans
#check CircuitBuilder.Extends.length_le
#check CircuitBuilder.Extends.wireValid
#check CircuitBuilder.evalWire
#check CircuitBuilder.Extends.evalWire_eq
#check CircuitBuilder.input
#check CircuitBuilder.input_extends
#check CircuitBuilder.input_wireValid
#check CircuitBuilder.input_gate_delta
#check CircuitBuilder.input_eval
#check CircuitBuilder.const
#check CircuitBuilder.const_extends
#check CircuitBuilder.const_wireValid
#check CircuitBuilder.const_gate_delta
#check CircuitBuilder.const_eval
#check CircuitBuilder.BoolWirePool
#check CircuitBuilder.BoolWirePool.falseWire
#check CircuitBuilder.BoolWirePool.trueWire
#check CircuitBuilder.BoolWirePool.falseValid
#check CircuitBuilder.BoolWirePool.trueValid
#check CircuitBuilder.BoolWirePool.false_eval
#check CircuitBuilder.BoolWirePool.true_eval
#check CircuitBuilder.BoolWirePool.mono
#check CircuitBuilder.BoolWirePool.mono_falseWire
#check CircuitBuilder.BoolWirePool.mono_trueWire
#check CircuitBuilder.BoolWirePool.mono_proof_irrel
#check CircuitBuilder.BoolWirePoolAllocation
#check CircuitBuilder.BoolWirePoolAllocation.builder
#check CircuitBuilder.BoolWirePoolAllocation.pool
#check CircuitBuilder.BoolWirePoolAllocation.extension
#check CircuitBuilder.BoolWirePoolAllocation.gate_delta
#check CircuitBuilder.allocateBoolWirePool
#check CircuitBuilder.allocateBoolWirePool_extends
#check CircuitBuilder.allocateBoolWirePool_falseWire
#check CircuitBuilder.allocateBoolWirePool_trueWire
#check CircuitBuilder.allocateBoolWirePool_false_wireValid
#check CircuitBuilder.allocateBoolWirePool_true_wireValid
#check CircuitBuilder.allocateBoolWirePool_gate_delta
#check CircuitBuilder.allocateBoolWirePool_false_eval
#check CircuitBuilder.allocateBoolWirePool_true_eval
#check CircuitBuilder.allocateBoolWirePool_proof_irrel
#check CircuitBuilder.not
#check CircuitBuilder.not_extends
#check CircuitBuilder.not_wireValid
#check CircuitBuilder.not_gate_delta
#check CircuitBuilder.not_eval
#check CircuitBuilder.and
#check CircuitBuilder.and_extends
#check CircuitBuilder.and_wireValid
#check CircuitBuilder.and_gate_delta
#check CircuitBuilder.and_eval
#check CircuitBuilder.or
#check CircuitBuilder.or_extends
#check CircuitBuilder.or_wireValid
#check CircuitBuilder.or_gate_delta
#check CircuitBuilder.or_eval
#check CircuitBuilder.conjunction
#check CircuitBuilder.conjunction_extends
#check CircuitBuilder.conjunction_wireValid
#check CircuitBuilder.conjunction_gate_delta
#check CircuitBuilder.conjunction_eval
#check CircuitBuilder.disjunction
#check CircuitBuilder.disjunction_extends
#check CircuitBuilder.disjunction_wireValid
#check CircuitBuilder.disjunction_gate_delta
#check CircuitBuilder.disjunction_eval
#check CircuitBuilder.eq
#check CircuitBuilder.eq_extends
#check CircuitBuilder.eq_wireValid
#check CircuitBuilder.eq_gate_delta
#check CircuitBuilder.eq_eval
#check CircuitBuilder.mux
#check CircuitBuilder.mux_extends
#check CircuitBuilder.mux_wireValid
#check CircuitBuilder.mux_gate_delta
#check CircuitBuilder.mux_eval
#check CircuitBuilder.MuxFinResult
#check CircuitBuilder.muxFin
#check CircuitBuilder.muxFin_extends
#check CircuitBuilder.muxFin_wireValid
#check CircuitBuilder.muxFin_gate_delta
#check CircuitBuilder.muxFin_eval
#check CircuitBuilder.muxFin_proof_irrel
#check CircuitBuilder.EqFinResult
#check CircuitBuilder.eqFin
#check CircuitBuilder.eqFin_extends
#check CircuitBuilder.eqFin_wireValid
#check CircuitBuilder.eqFin_gate_delta
#check CircuitBuilder.eqFin_eval_iff
#check CircuitBuilder.eqFin_proof_irrel
#check CircuitBuilder.finish
#check CircuitBuilder.finish_wellFormed
#check CircuitBuilder.finish_eval
#check CfgSlot
#check cfgBitCount
#check card_cfgSlot
#check cfgSlotEquivFin
#check CfgWires
#check CfgBits
#check StackBundle
#check StackBundle.height
#check StackBundle.cell
#check StackWires
#check StackBits
#check SupportedSymbol
#check SymbolBundle
#check SymbolBits
#check HeadBundle
#check HeadBits
#check SupportedHead
#check encodeSupportedSymbol
#check decodeSupportedSymbol
#check decodeSupportedSymbol_encode
#check encodeSupportedSymbol_decode
#check encodeHeadCode
#check decodeHeadCode
#check decodeHeadCode_encode
#check encodeHeadCode_decode
#check encodeSymbolBits
#check decodeSymbolBits?
#check decodeSymbolBits_encode
#check decodeSymbolBits_eq_some_iff
#check decodeSymbolBits_of_card_eq_zero
#check encodeHeadBits
#check decodeHeadBits?
#check decodeHeadBits_encode
#check decodeHeadBits_eq_some_iff
#check decodeHeadValue?
#check decodeHeadValue_encode
#check decodeHeadValue_eq_some_iff
#check pushStackBits
#check pushStackBits_height_zero
#check pushStackBits_height_succ
#check pushStackBits_cell_zero_supported
#check pushStackBits_cell_zero_blank
#check pushStackBits_cell_zero_encodeSymbol
#check pushStackBits_cell_succ
#check pushStackBits_height_eq_false_of_full
#check peekStackBits
#check peekStackBits_zero
#check peekStackBits_of_pos
#check PopStackBitsResult
#check PopStackBitsResult.stack
#check PopStackBitsResult.head
#check popStackBits
#check popStackBits_head
#check popStackBits_height_zero
#check popStackBits_height_succ
#check popStackBits_cell_of_next
#check popStackBits_cell_last
#check popStackBits_zero_stack
#check popStackBits_zero_head
#check StackBits.RawDecodable
#check StackBits.RawDecodable.height
#check StackBits.RawDecodable.cell
#check StackBits.HasCapacity
#check peekStackBits_oneHot
#check peekStackBits_zero_oneHot
#check popStackBits_rawDecodable
#check pushStackBits_rawDecodable
#check pushStackBits_not_rawDecodable_of_full
#check encodeBoundedStackBits
#check encodeBoundedStackBits_height
#check encodeBoundedStackBits_cell
#check encodeBoundedStackBits_rawDecodable
#check StackBits.Represents
#check StackBits.Represents.rawDecodable
#check StackBits.Represents.of_encode
#check StackBits.Represents.eq_encode
#check represents_hasCapacity_iff
#check peekStackBits_represents
#check popStackBits_represents
#check popStackBits_encodeBoundedStackBits
#check pushStackBits_encodeBoundedStackBits
#check pushStackBits_represents
#check encodeRawCfgBits_stack
#check evalBundle_stack_represents
#check SymbolWires
#check HeadWires
#check SymbolWires.ValidIn
#check HeadWires.ValidIn
#check StackWires.ValidIn
#check evalSymbolBits
#check evalHeadBits
#check evalStackBits
#check CfgWires.ValidIn.stack
#check evalStackBits_cfgStack
#check evalSymbolBits_extends
#check evalHeadBits_extends
#check evalStackBits_extends
#check CfgWires.ValidIn.replaceStack
#check evalCfgBits_replaceStack
#check encodeSymbolWires
#check encodeSymbolWires_valid
#check encodeSymbolWires_eval
#check encodeHeadWires
#check encodeHeadWires_valid
#check encodeHeadWires_eval
#check pushStackWires
#check pushStackWires_valid
#check pushStackWires_eval
#check pushStackWires_represents
#check peekStackWires
#check peekStackWires_valid
#check peekStackWires_eval
#check peekStackWires_represents
#check popStackWireGateCost
#check popStackWireGateCost_zero
#check popStackWireGateCost_succ
#check PopStackWiresResult
#check popStackWires
#check popStackWires_proof_irrel
#check StackCapacityResult
#check stackCapacity
#check stackCapacity_eval_iff
#check cfgStackCapacity
#check cfgStackCapacity_eval_iff_length_lt
#check pushCfgWires
#check pushCfgWires_valid
#check pushCfgWires_eval
#check pushCfgWires_represents_of_evalBundle
#check pushCfgWires_halted
#check pushCfgWires_label
#check pushCfgWires_state
#check pushCfgWires_stack_same
#check pushCfgWires_stack_other
#check OneHotMapResult
#check oneHotMap
#check oneHotMap_extends
#check oneHotMap_wireValid
#check oneHotMap_gate_delta
#check oneHotMap_eval
#check oneHotMap_proof_irrel
#check oneHotMap_eval_encodeOneHot
#check oneHotMap_oneHot
#check OneHotPairMapResult
#check oneHotPairMap
#check oneHotPairMap_extends
#check oneHotPairMap_wireValid
#check oneHotPairMap_gate_delta
#check oneHotPairMap_eval
#check oneHotPairMap_proof_irrel
#check oneHotPairMap_eval_encodeOneHot
#check OneHotPredicateResult
#check oneHotPredicate
#check oneHotPredicate_extends
#check oneHotPredicate_wireValid
#check oneHotPredicate_gate_delta
#check oneHotPredicate_gate_bound
#check oneHotPredicate_eval
#check oneHotPredicate_proof_irrel
#check oneHotPredicate_eval_encodeOneHot
#check StateWires
#check StateBits
#check StateWires.ValidIn
#check StateWires.ValidIn.mono
#check evalStateBits
#check evalStateBits_extends
#check LabelWires
#check LabelBits
#check LabelWires.ValidIn
#check LabelWires.ValidIn.mono
#check evalLabelBits
#check evalLabelBits_extends
#check CfgBundle.replaceState
#check CfgBundle.replaceStatus
#check CfgWires.ValidIn.replaceState
#check CfgWires.ValidIn.replaceStatus
#check evalCfgBits_replaceState
#check evalCfgBits_replaceStatus
#check encodeStateWires
#check encodeStateWires_valid
#check encodeStateWires_eval
#check encodeStateWires_mono
#check encodeStateWires_proof_irrel
#check encodeLabelWires
#check encodeLabelWires_valid
#check encodeLabelWires_eval
#check encodeLabelWires_mono
#check encodeLabelWires_proof_irrel
#check encodeLabelHaltedWire
#check encodeLabelHaltedWire_valid
#check encodeLabelHaltedWire_eval
#check encodeLabelHaltedWire_mono
#check encodeLabelHaltedWire_proof_irrel
#check evalBundle_eq_some_canonical
#check evalStateBits_of_evalBundle
#check evalLabelBits_of_evalBundle
#check evalHaltedBit_of_evalBundle
#check evalBundle_replaceState
#check evalBundle_replaceStatus
#check cfgPushStack
#check cfgPopStack
#check pushCfgWires_evalBundle
#check peekCfgWires_head_eq_encode_of_evalBundle
#check popCfgWires_head_eq_encode_of_evalBundle
#check popCfgWires_evalBundle
#check compileStmtGateCost
#check compileStmtGateCoefficient
#check compileStmtGateCost_le
#check CompileStmtResult
#check compileStmt
#check compileStmt_gate_delta
#check compileStmt_evalBundle
#check compileStmt_gate_count_le
#check compileStmt_proof_irrel
#check dispatchGateCoefficient
#check dispatchGateCost_le
#check dispatchLabels_gate_count_le
#check TransitionCircuitResult
#check transitionCircuit
#check transitionCircuitGateCoefficient
#check transitionCircuitGateCost_le
#check transitionCircuit_gate_count_le
#check transitionCircuit_eval_iff
#check transitionCircuit_sound
#check transitionCircuitFinished
#check transitionCircuit_finish_wellFormed
#check transitionCircuit_finish_eval
#check transitionCircuitFinished_proof_irrel
#check BoundaryCircuitResult
#check staticCfgWires
#check staticCfgWires_valid
#check staticCfgWires_eval
#check staticCfgWires_mono
#check initialCfgCircuitGateCost
#check initialCfgCircuit
#check initialCfgCircuit_gate_delta
#check initialCfgCircuit_eval_iff
#check AcceptingOutputFits
#check acceptingOutputCircuitGateCost
#check acceptingOutputCircuit
#check acceptingOutputCircuit_gate_delta
#check acceptingOutputCircuit_eval_iff
#check symbolicInitialCfgWires
#check symbolicInitialCfgWires_valid
#check symbolicInitialCfgCircuit
#check symbolicInitialCfgCircuit_gate_delta
#check symbolicInitialCfgCircuit_eval_iff
#check FreshTransitionCircuitAtResult
#check freshTransitionCircuitAt
#check freshTransitionCircuitAt_gate_delta
#check freshTransitionCircuitAt_complete_nat
#check FreshTransitionCircuitResult
#check freshTransitionCircuit
#check freshTransitionCircuit_gate_delta
#check freshTransitionCircuit_complete
#check freshTransitionCircuit_sound
#check peekCfgWires
#check peekCfgWires_valid
#check peekCfgWires_eval
#check peekCfgWires_represents_of_evalBundle
#check PopCfgWiresResult
#check popCfgWires
#check popCfgWires_proof_irrel
#check popCfgWires_halted
#check popCfgWires_label
#check popCfgWires_state
#check popCfgWires_stack_same
#check popCfgWires_stack_other
#check popCfgWires_represents_of_evalBundle
#check CfgBundle.stack
#check CfgBundle.replaceStack
#check CfgBundle.replaceStack_halted
#check CfgBundle.replaceStack_label
#check CfgBundle.replaceStack_state
#check CfgBundle.replaceStack_stack_same
#check CfgBundle.replaceStack_stack_other
#check CfgMuxResult
#check CfgMuxResult.builder
#check CfgMuxResult.wires
#check CfgMuxResult.extension
#check CfgMuxResult.valid
#check CfgMuxResult.gate_delta
#check CfgMuxResult.eval
#check cfgMux
#check cfgMux_extends
#check cfgMux_valid
#check cfgMux_gate_delta
#check cfgMux_eval
#check cfgMux_proof_irrel
#check CfgEqResult
#check CfgEqResult.builder
#check CfgEqResult.wire
#check CfgEqResult.extension
#check CfgEqResult.valid
#check CfgEqResult.gate_delta
#check CfgEqResult.eval
#check cfgEq
#check cfgEq_extends
#check cfgEq_wireValid
#check cfgEq_gate_delta
#check cfgEq_eval_iff
#check cfgEq_proof_irrel
#check CfgWires.ValidIn
#check CfgWires.ValidIn.mono
#check evalCfgBits
#check evalCfgBits_extends
#check CfgInputIndex
#check CfgInputLayout
#check CfgInputLayout.finish
#check CfgInputLayout.index
#check CfgInputLayout.Fits
#check CfgInputLayout.Disjoint
#check CfgInputLayout.index_lt
#check CfgInputLayout.index_injective
#check CfgInputLayout.next
#check CfgInputLayout.next_disjoint
#check CfgInputLayout.index_ne_of_disjoint
#check OneHot
#check decodeOneHot
#check decodeOneHot_eq_some_iff
#check decodeOneHot_isSome_iff
#check decodeOneHot_eq_none_iff
#check decodeOneHot_fin_zero
#check encodeOneHot
#check oneHot_encodeOneHot
#check decodeOneHot_encodeOneHot
#check CfgBits.RawDecodable
#check rawCfgOf
#check decodeRawCfg?
#check encodeRawCfgBits
#check decodeRawCfg_encode
#check encodeRawCfg_decode
#check decodeRawCfg_eq_some_iff
#check evalRawBundle
#check evalBundle
#check evalRawBundle_extends
#check evalBundle_extends
#check evalBundle_encodeCfg
#check CfgInputLayout.decodeIndex
#check CfgInputLayout.decodeIndex_index
#check CfgInputLayout.writeCfgBits
#check CfgInputLayout.writeCfgBits_at
#check CfgInputLayout.writeCfgBits_outside
#check CfgInputLayout.writeCfgBits_index_of_disjoint
#check BuiltWire
#check BuiltWire.builder
#check BuiltWire.wire
#check BuiltWire.extension
#check BuiltWire.valid
#check CfgInputAllocation
#check allocateCfgInputs
#check CfgInputAllocation.gate_delta
#check CfgInputAllocation.wire_eq
#check CfgInputAllocation.eval_slot
#check CfgInputAllocation.evalCfgBits_write
#check CfgInputAllocation.evalCfgBits_extends
#check CfgInputAllocation.evalRawBundle_write_encode
#check CfgInputAllocation.evalBundle_write_encodeCfg
#check exactlyOne
#check exactlyOne_extends
#check exactlyOne_wireValid
#check exactlyOne_gate_delta
#check exactlyOne_eval_iff
#check exactlyOne_rejects_aliased_pair
#check CfgBits.Canonical
#check evalBundle_isSome_iff_canonical
#check validCfgGateCost
#check validCfgGateCoefficient
#check validCfgGateCost_le
#check validCfgCircuit
#check validCfgCircuit_extends
#check validCfgCircuit_wireValid
#check validCfgCircuit_gate_delta
#check validCfgCircuit_eval_iff
#check validCfgCircuit_eval_exists_iff
#check validCfgCircuit_accepts_encodeCfg
#check validCfgCircuit_gate_count_le
#check validCfgCircuitFinished
#check validCfgCircuit_finish_wellFormed
#check validCfgCircuit_finish_eval
#check validCfgCircuitFinished_proof_irrel
#check workHeight
#check widenCfgBits
#check CfgBits.FitsHeight
#check narrowCfgBits
#check WidenCfgResult
#check WidenCfgResult.constants
#check widenCfg
#check widenCfg_extends
#check widenCfg_valid
#check widenCfg_gate_delta
#check widenCfg_eval
#check widenCfg_decode_preserved
#check NarrowCfgResult
#check narrowCfg
#check narrowCfg_extends
#check narrowCfg_valid
#check narrowCfg_fit_wireValid
#check narrowCfg_gate_delta
#check narrowCfg_fit_iff
#check narrowCfg_eval
#check narrowCfg_decode_preserved

/-- Regression: selecting a freshly built constant as the final output
preserves both well-formedness and its Boolean value. -/
example (inputs : Nat → Bool) :
    let base := CircuitBuilder.empty 0
    let built := base.const true
    (built.1.finish built.2 (CircuitBuilder.const_wireValid base true)).eval inputs =
      true := by
  dsimp only
  rw [CircuitBuilder.finish_eval, CircuitBuilder.const_eval]

/-- Two existing literal wires used to exercise the public combinator API. -/
private def circuitBuilderLiterals : CircuitBuilder where
  inputCount := 0
  gates := [.const true, .const false]
  valid := by
    intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> trivial

private theorem circuitBuilderLiteralValid (wire : Nat) (hwire : wire < 2) :
    circuitBuilderLiterals.WireValid wire := by
  simpa [CircuitBuilder.WireValid, circuitBuilderLiterals] using hwire

private theorem circuitBuilderLiteralZero_eval :
    circuitBuilderLiterals.evalWire (fun _ => false) 0 = true := by
  native_decide

private theorem circuitBuilderLiteralOne_eval :
    circuitBuilderLiterals.evalWire (fun _ => false) 1 = false := by
  native_decide

private def literalBoolWirePool :=
  CircuitBuilder.allocateBoolWirePool circuitBuilderLiterals

-- Pool allocation uses the exact fresh wire identities 2 and 3, executes both
-- constants, and appends exactly two gates.
example : literalBoolWirePool.pool.falseWire = 2 ∧
    literalBoolWirePool.pool.trueWire = 3 ∧
    literalBoolWirePool.builder.gates.length = 4 ∧
    literalBoolWirePool.builder.evalWire (fun _ => true)
        literalBoolWirePool.pool.falseWire = false ∧
    literalBoolWirePool.builder.evalWire (fun _ => false)
        literalBoolWirePool.pool.trueWire = true := by
  native_decide

private def literalBoolWirePoolExtended :=
  literalBoolWirePool.builder.not literalBoolWirePool.pool.trueWire
    literalBoolWirePool.pool.trueValid

private def literalBoolWirePoolMono :
    CircuitBuilder.BoolWirePool literalBoolWirePoolExtended.1 :=
  literalBoolWirePool.pool.mono
    (CircuitBuilder.not_extends literalBoolWirePool.builder
      literalBoolWirePool.pool.trueWire literalBoolWirePool.pool.trueValid)

-- Monotone reuse keeps both old wire identities and their values after a
-- further builder extension.
example : literalBoolWirePoolMono.falseWire = literalBoolWirePool.pool.falseWire ∧
    literalBoolWirePoolMono.trueWire = literalBoolWirePool.pool.trueWire ∧
    literalBoolWirePoolExtended.1.evalWire (fun _ => true)
        literalBoolWirePoolMono.falseWire = false ∧
    literalBoolWirePoolExtended.1.evalWire (fun _ => false)
        literalBoolWirePoolMono.trueWire = true := by
  exact ⟨rfl, rfl, literalBoolWirePoolMono.false_eval _,
    literalBoolWirePoolMono.true_eval _⟩

-- Extending the prefix preserves the value of an old wire.
example (inputs : Nat → Bool) :
    let htrue := circuitBuilderLiteralValid 0 (by omega)
    let extended := circuitBuilderLiterals.not 0 htrue
    extended.1.evalWire inputs 0 = circuitBuilderLiterals.evalWire inputs 0 := by
  dsimp only
  exact (CircuitBuilder.not_extends circuitBuilderLiterals 0
    (circuitBuilderLiteralValid 0 (by omega))).evalWire_eq inputs
      (circuitBuilderLiteralValid 0 (by omega))

private theorem circuitBuilderPairValid :
    ∀ wire ∈ ([0, 1] : List Nat), circuitBuilderLiterals.WireValid wire := by
  intro wire hwire
  simp at hwire
  rcases hwire with rfl | rfl <;> exact circuitBuilderLiteralValid _ (by omega)

private def finiteFamilyTrue : Fin 3 → CircuitBuilder.Wire := fun _ => 0

private def finiteFamilyFalse : Fin 3 → CircuitBuilder.Wire := fun _ => 1

private def finiteFamilyLastTrue : Fin 3 → CircuitBuilder.Wire := fun i =>
  if i.val = 2 then 0 else 1

private theorem finiteFamilyTrueValid :
    ∀ i, circuitBuilderLiterals.WireValid (finiteFamilyTrue i) := by
  intro i
  exact circuitBuilderLiteralValid 0 (by omega)

private theorem finiteFamilyFalseValid :
    ∀ i, circuitBuilderLiterals.WireValid (finiteFamilyFalse i) := by
  intro i
  exact circuitBuilderLiteralValid 1 (by omega)

private theorem finiteFamilyLastTrueValid :
    ∀ i, circuitBuilderLiterals.WireValid (finiteFamilyLastTrue i) := by
  intro i
  unfold finiteFamilyLastTrue
  split <;> exact circuitBuilderLiteralValid _ (by omega)

private theorem finiteFamilyLastTrueEncoded :
    (fun i => circuitBuilderLiterals.evalWire (fun _ => false)
      (finiteFamilyLastTrue i)) = encodeOneHot (2 : Fin 3) := by
  native_decide

/-! ### Exact finite one-hot lookup circuits -/

private def lookupEmptySource : Fin 0 → CircuitBuilder.Wire := fun i => Fin.elim0 i

private theorem lookupEmptySourceValid :
    ∀ i, circuitBuilderLiterals.WireValid (lookupEmptySource i) :=
  fun i => Fin.elim0 i

private def lookupEmptyFunction : Fin 0 → Fin 0 := fun i => Fin.elim0 i

private noncomputable def lookupEmptyMap :=
  oneHotMap circuitBuilderLiterals lookupEmptySource lookupEmptyFunction
    lookupEmptySourceValid

-- Both empty dimensions allocate no gates; in particular `m = 0` is genuine.
example : lookupEmptyMap.builder.gates.length = 2 := by
  simpa [lookupEmptyMap, circuitBuilderLiterals] using
    oneHotMap_gate_delta circuitBuilderLiterals lookupEmptySource
      lookupEmptyFunction lookupEmptySourceValid

private def lookupEmptyToTwo : Fin 0 → Fin 2 := fun i => Fin.elim0 i

private noncomputable def lookupEmptyToTwoMap :=
  oneHotMap circuitBuilderLiterals lookupEmptySource lookupEmptyToTwo
    lookupEmptySourceValid

-- Empty source fibers each execute their own false seed: exact delta two and
-- both actual output values false.
example : lookupEmptyToTwoMap.builder.gates.length = 4 ∧
    lookupEmptyToTwoMap.builder.evalWire (fun _ => false)
        (lookupEmptyToTwoMap.wires 0) = false ∧
    lookupEmptyToTwoMap.builder.evalWire (fun _ => false)
        (lookupEmptyToTwoMap.wires 1) = false := by
  constructor
  · simpa [lookupEmptyToTwoMap, circuitBuilderLiterals] using
      oneHotMap_gate_delta circuitBuilderLiterals lookupEmptySource
        lookupEmptyToTwo lookupEmptySourceValid
  · constructor
    · simpa [lookupEmptyToTwoMap, oneHotPreimage] using
        oneHotMap_eval circuitBuilderLiterals lookupEmptySource lookupEmptyToTwo
          lookupEmptySourceValid (fun _ => false) (0 : Fin 2)
    · simpa [lookupEmptyToTwoMap, oneHotPreimage] using
        oneHotMap_eval circuitBuilderLiterals lookupEmptySource lookupEmptyToTwo
          lookupEmptySourceValid (fun _ => false) (1 : Fin 2)

private def lookupConstant : Fin 3 → Fin 2 := fun _ => 0

private def lookupNoninjective (i : Fin 3) : Fin 2 :=
  if i.val < 2 then 0 else 1

private def lookupPermutation (i : Fin 3) : Fin 3 :=
  if i.val = 0 then 1 else if i.val = 1 then 2 else 0

private noncomputable def lookupConstantMap :=
  oneHotMap circuitBuilderLiterals finiteFamilyLastTrue lookupConstant
    finiteFamilyLastTrueValid

private noncomputable def lookupNoninjectiveMap :=
  oneHotMap circuitBuilderLiterals finiteFamilyLastTrue lookupNoninjective
    finiteFamilyLastTrueValid

private noncomputable def lookupPermutationMap :=
  oneHotMap circuitBuilderLiterals finiteFamilyLastTrue lookupPermutation
    finiteFamilyLastTrueValid

-- A constant map coalesces all three source coordinates into target zero and
-- realizes the promised actual delta `3 + 2`.
example : lookupConstantMap.builder.gates.length = 7 ∧
    lookupConstantMap.builder.evalWire (fun _ => false)
        (lookupConstantMap.wires 0) = true ∧
    lookupConstantMap.builder.evalWire (fun _ => false)
        (lookupConstantMap.wires 1) = false := by
  constructor
  · simpa [lookupConstantMap, circuitBuilderLiterals] using
      oneHotMap_gate_delta circuitBuilderLiterals finiteFamilyLastTrue
        lookupConstant finiteFamilyLastTrueValid
  · have hcanonical := oneHotMap_eval_encodeOneHot circuitBuilderLiterals
      finiteFamilyLastTrue lookupConstant finiteFamilyLastTrueValid
      (fun _ => false) (2 : Fin 3) finiteFamilyLastTrueEncoded
    exact ⟨by simpa [lookupConstantMap, lookupConstant, encodeOneHot] using
        congrFun hcanonical 0,
      by simpa [lookupConstantMap, lookupConstant, encodeOneHot] using
        congrFun hcanonical 1⟩

-- A noninjective map still selects the image of the unique true source.
example : lookupNoninjectiveMap.builder.gates.length = 7 ∧
    lookupNoninjectiveMap.builder.evalWire (fun _ => false)
        (lookupNoninjectiveMap.wires 0) = false ∧
    lookupNoninjectiveMap.builder.evalWire (fun _ => false)
        (lookupNoninjectiveMap.wires 1) = true := by
  constructor
  · simpa [lookupNoninjectiveMap, circuitBuilderLiterals] using
      oneHotMap_gate_delta circuitBuilderLiterals finiteFamilyLastTrue
        lookupNoninjective finiteFamilyLastTrueValid
  · have hcanonical := oneHotMap_eval_encodeOneHot circuitBuilderLiterals
      finiteFamilyLastTrue lookupNoninjective finiteFamilyLastTrueValid
      (fun _ => false) (2 : Fin 3) finiteFamilyLastTrueEncoded
    exact ⟨by simpa [lookupNoninjectiveMap, lookupNoninjective, encodeOneHot] using
        congrFun hcanonical 0,
      by simpa [lookupNoninjectiveMap, lookupNoninjective, encodeOneHot] using
        congrFun hcanonical 1⟩

-- A permutation moves the last selected source to target zero at exact delta
-- `3 + 3`.
example : lookupPermutationMap.builder.gates.length = 8 ∧
    lookupPermutationMap.builder.evalWire (fun _ => false)
        (lookupPermutationMap.wires 0) = true ∧
    lookupPermutationMap.builder.evalWire (fun _ => false)
        (lookupPermutationMap.wires 1) = false ∧
    lookupPermutationMap.builder.evalWire (fun _ => false)
        (lookupPermutationMap.wires 2) = false := by
  constructor
  · simpa [lookupPermutationMap, circuitBuilderLiterals] using
      oneHotMap_gate_delta circuitBuilderLiterals finiteFamilyLastTrue
        lookupPermutation finiteFamilyLastTrueValid
  · have hcanonical := oneHotMap_eval_encodeOneHot circuitBuilderLiterals
      finiteFamilyLastTrue lookupPermutation finiteFamilyLastTrueValid
      (fun _ => false) (2 : Fin 3) finiteFamilyLastTrueEncoded
    exact ⟨by simpa [lookupPermutationMap, lookupPermutation, encodeOneHot] using
        congrFun hcanonical 0,
      by simpa [lookupPermutationMap, lookupPermutation, encodeOneHot] using
        congrFun hcanonical 1,
      by simpa [lookupPermutationMap, lookupPermutation, encodeOneHot] using
        congrFun hcanonical 2⟩

private def lookupLeftTwo : Fin 2 → CircuitBuilder.Wire := fun i =>
  if i.val = 1 then 0 else 1

private def lookupRightThree : Fin 3 → CircuitBuilder.Wire := finiteFamilyLastTrue

private theorem lookupLeftTwoValid :
    ∀ i, circuitBuilderLiterals.WireValid (lookupLeftTwo i) := by
  intro i
  unfold lookupLeftTwo
  split <;> exact circuitBuilderLiteralValid _ (by omega)

private theorem lookupLeftTwoEncoded :
    (fun i => circuitBuilderLiterals.evalWire (fun _ => false)
      (lookupLeftTwo i)) = encodeOneHot (1 : Fin 2) := by
  native_decide

private theorem lookupRightThreeValid :
    ∀ i, circuitBuilderLiterals.WireValid (lookupRightThree i) :=
  finiteFamilyLastTrueValid

private def lookupPairParity (i : Fin 2) (j : Fin 3) : Fin 2 :=
  ⟨(i.val + j.val) % 2, Nat.mod_lt _ (by omega)⟩

private noncomputable def lookupPairTwoByThree :=
  oneHotPairMap circuitBuilderLiterals lookupLeftTwo lookupRightThree
    lookupPairParity lookupLeftTwoValid lookupRightThreeValid

-- The 2×3 pair test executes six serial ANDs plus a six-coordinate map:
-- actual delta `2*2*3+2 = 14`, with the selected pair `(1,2)` mapped to one.
example : lookupPairTwoByThree.builder.gates.length = 16 ∧
    lookupPairTwoByThree.builder.evalWire (fun _ => false)
        (lookupPairTwoByThree.wires 0) = false ∧
    lookupPairTwoByThree.builder.evalWire (fun _ => false)
        (lookupPairTwoByThree.wires 1) = true := by
  constructor
  · simpa [lookupPairTwoByThree, circuitBuilderLiterals] using
      oneHotPairMap_gate_delta circuitBuilderLiterals lookupLeftTwo
        lookupRightThree lookupPairParity lookupLeftTwoValid
        lookupRightThreeValid
  · have hcanonical := oneHotPairMap_eval_encodeOneHot circuitBuilderLiterals
      lookupLeftTwo lookupRightThree lookupPairParity lookupLeftTwoValid
      lookupRightThreeValid (fun _ => false) (1 : Fin 2) (2 : Fin 3)
      lookupLeftTwoEncoded finiteFamilyLastTrueEncoded
    exact ⟨by simpa [lookupPairTwoByThree, lookupPairParity, encodeOneHot] using
        congrFun hcanonical 0,
      by simpa [lookupPairTwoByThree, lookupPairParity, encodeOneHot] using
        congrFun hcanonical 1⟩

private def lookupPairRightEmpty : Fin 0 → CircuitBuilder.Wire :=
  fun j => Fin.elim0 j

private theorem lookupPairRightEmptyValid :
    ∀ j, circuitBuilderLiterals.WireValid (lookupPairRightEmpty j) :=
  fun j => Fin.elim0 j

private def lookupPairEmptyFunction : Fin 2 → Fin 0 → Fin 2 :=
  fun _ j => Fin.elim0 j

private noncomputable def lookupPairEmpty :=
  oneHotPairMap circuitBuilderLiterals lookupLeftTwo lookupPairRightEmpty
    lookupPairEmptyFunction lookupLeftTwoValid lookupPairRightEmptyValid

-- At `p = 0` no pair AND exists; only two empty target-fiber seeds execute.
example : lookupPairEmpty.builder.gates.length = 4 ∧
    lookupPairEmpty.builder.evalWire (fun _ => false)
        (lookupPairEmpty.wires 0) = false ∧
    lookupPairEmpty.builder.evalWire (fun _ => false)
        (lookupPairEmpty.wires 1) = false := by
  constructor
  · simpa [lookupPairEmpty, circuitBuilderLiterals] using
      oneHotPairMap_gate_delta circuitBuilderLiterals lookupLeftTwo
        lookupPairRightEmpty lookupPairEmptyFunction lookupLeftTwoValid
        lookupPairRightEmptyValid
  · constructor
    · simpa [lookupPairEmpty, oneHotPairPreimage, oneHotPreimage] using
        oneHotPairMap_eval circuitBuilderLiterals lookupLeftTwo
          lookupPairRightEmpty lookupPairEmptyFunction lookupLeftTwoValid
          lookupPairRightEmptyValid (fun _ => false) (0 : Fin 2)
    · simpa [lookupPairEmpty, oneHotPairPreimage, oneHotPreimage] using
        oneHotPairMap_eval circuitBuilderLiterals lookupLeftTwo
          lookupPairRightEmpty lookupPairEmptyFunction lookupLeftTwoValid
          lookupPairRightEmptyValid (fun _ => false) (1 : Fin 2)

private def lookupPairZeroByThreeFunction : Fin 0 → Fin 3 → Fin 2 :=
  fun i _ => Fin.elim0 i

private noncomputable def lookupPairZeroByThree :=
  oneHotPairMap circuitBuilderLiterals lookupEmptySource finiteFamilyLastTrue
    lookupPairZeroByThreeFunction lookupEmptySourceValid
    finiteFamilyLastTrueValid

-- At `n = 0` and positive `p,m`, no pair AND exists and the two target
-- coordinates each execute exactly one false seed: actual delta `m = 2`.
example : lookupPairZeroByThree.builder.gates.length = 4 ∧
    lookupPairZeroByThree.builder.evalWire (fun _ => false)
        (lookupPairZeroByThree.wires 0) = false ∧
    lookupPairZeroByThree.builder.evalWire (fun _ => false)
        (lookupPairZeroByThree.wires 1) = false := by
  constructor
  · simpa [lookupPairZeroByThree, circuitBuilderLiterals] using
      oneHotPairMap_gate_delta circuitBuilderLiterals lookupEmptySource
        finiteFamilyLastTrue lookupPairZeroByThreeFunction
        lookupEmptySourceValid finiteFamilyLastTrueValid
  · constructor
    · simpa [lookupPairZeroByThree, oneHotPairPreimage, oneHotPreimage] using
        oneHotPairMap_eval circuitBuilderLiterals lookupEmptySource
          finiteFamilyLastTrue lookupPairZeroByThreeFunction
          lookupEmptySourceValid finiteFamilyLastTrueValid
          (fun _ => false) (0 : Fin 2)
    · simpa [lookupPairZeroByThree, oneHotPairPreimage, oneHotPreimage] using
        oneHotPairMap_eval circuitBuilderLiterals lookupEmptySource
          finiteFamilyLastTrue lookupPairZeroByThreeFunction
          lookupEmptySourceValid finiteFamilyLastTrueValid
          (fun _ => false) (1 : Fin 2)

private def lookupPairZeroByThreeToZeroFunction : Fin 0 → Fin 3 → Fin 0 :=
  fun i _ => Fin.elim0 i

private noncomputable def lookupPairZeroByThreeToZero :=
  oneHotPairMap circuitBuilderLiterals lookupEmptySource finiteFamilyLastTrue
    lookupPairZeroByThreeToZeroFunction lookupEmptySourceValid
    finiteFamilyLastTrueValid

-- The constructible `m = 0` boundary has neither pair coordinates nor target
-- coordinates: exact delta zero, the builder is definitionally unchanged,
-- and output validity/evaluation obligations are vacuous.
example : lookupPairZeroByThreeToZero.builder = circuitBuilderLiterals ∧
    lookupPairZeroByThreeToZero.builder.gates.length = 2 ∧
    (∀ target : Fin 0,
      lookupPairZeroByThreeToZero.builder.WireValid
        (lookupPairZeroByThreeToZero.wires target)) ∧
    (∀ inputs target,
      lookupPairZeroByThreeToZero.builder.evalWire inputs
        (lookupPairZeroByThreeToZero.wires target) = false) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simpa [lookupPairZeroByThreeToZero, circuitBuilderLiterals] using
      oneHotPairMap_gate_delta circuitBuilderLiterals lookupEmptySource
        finiteFamilyLastTrue lookupPairZeroByThreeToZeroFunction
        lookupEmptySourceValid finiteFamilyLastTrueValid
  · intro target
    exact Fin.elim0 target
  · intro _ target
    exact Fin.elim0 target

private noncomputable def lookupPredicateFalse :=
  oneHotPredicate circuitBuilderLiterals finiteFamilyLastTrue (fun _ => false)
    finiteFamilyLastTrueValid

private noncomputable def lookupPredicateTrue :=
  oneHotPredicate circuitBuilderLiterals finiteFamilyLastTrue (fun _ => true)
    finiteFamilyLastTrueValid

private noncomputable def lookupPredicateEmpty :=
  oneHotPredicate circuitBuilderLiterals lookupEmptySource
    (fun i => Fin.elim0 i) lookupEmptySourceValid

-- All-false predicates execute just the seed; all-true predicates execute all
-- three source OR steps; the empty predicate is again exactly one false seed.
example : lookupPredicateFalse.builder.gates.length = 3 ∧
    lookupPredicateFalse.builder.evalWire (fun _ => false)
        lookupPredicateFalse.wire = false ∧
    lookupPredicateTrue.builder.gates.length = 6 ∧
    lookupPredicateTrue.builder.evalWire (fun _ => false)
        lookupPredicateTrue.wire = true ∧
    lookupPredicateEmpty.builder.gates.length = 3 ∧
    lookupPredicateEmpty.builder.evalWire (fun _ => false)
        lookupPredicateEmpty.wire = false := by
  have hfalse := oneHotPredicate_eval_encodeOneHot circuitBuilderLiterals
    finiteFamilyLastTrue (fun _ => false) finiteFamilyLastTrueValid
    (fun _ => false) (2 : Fin 3) finiteFamilyLastTrueEncoded
  have htrue := oneHotPredicate_eval_encodeOneHot circuitBuilderLiterals
    finiteFamilyLastTrue (fun _ => true) finiteFamilyLastTrueValid
    (fun _ => false) (2 : Fin 3) finiteFamilyLastTrueEncoded
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [lookupPredicateFalse, circuitBuilderLiterals, oneHotTruePreimage] using
      oneHotPredicate_gate_delta circuitBuilderLiterals finiteFamilyLastTrue
        (fun _ => false) finiteFamilyLastTrueValid
  · simpa only [lookupPredicateFalse] using hfalse
  · simpa [lookupPredicateTrue, circuitBuilderLiterals, oneHotTruePreimage] using
      oneHotPredicate_gate_delta circuitBuilderLiterals finiteFamilyLastTrue
        (fun _ => true) finiteFamilyLastTrueValid
  · simpa only [lookupPredicateTrue] using htrue
  · simpa [lookupPredicateEmpty, circuitBuilderLiterals, oneHotTruePreimage] using
      oneHotPredicate_gate_delta circuitBuilderLiterals lookupEmptySource
        (fun i => Fin.elim0 i) lookupEmptySourceValid
  · simpa [lookupPredicateEmpty, oneHotTruePreimage] using
      oneHotPredicate_eval circuitBuilderLiterals lookupEmptySource
        (fun i => Fin.elim0 i) lookupEmptySourceValid (fun _ => false)

-- Finite families retain their exact uniform costs at n = 0.
example :
    (CircuitBuilder.muxFin circuitBuilderLiterals (n := 0) 0
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (circuitBuilderLiteralValid 0 (by omega)) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i)).builder.gates.length = 3 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.muxFin_gate_delta circuitBuilderLiterals (n := 0) 0
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (circuitBuilderLiteralValid 0 (by omega)) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i)

example :
    (CircuitBuilder.eqFin circuitBuilderLiterals (n := 0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).builder.evalWire
        (fun _ => false)
        (CircuitBuilder.eqFin circuitBuilderLiterals (n := 0)
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
          (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).wire = true := by
  rw [CircuitBuilder.eqFin_eval_iff]
  exact fun i => Fin.elim0 i

example :
    (CircuitBuilder.eqFin circuitBuilderLiterals (n := 0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)).builder.gates.length = 3 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.eqFin_gate_delta circuitBuilderLiterals (n := 0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

-- These construction-level regressions execute the generated circuits
-- directly, independently of the public semantic and gate-count theorems.
example :
    let result := CircuitBuilder.eqFin circuitBuilderLiterals (n := 0)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    result.builder.gates.length = 3 ∧
      result.builder.evalWire (fun _ => false) result.wire = true := by
  native_decide

example :
    let result := CircuitBuilder.muxFin circuitBuilderLiterals 0
      finiteFamilyLastTrue finiteFamilyFalse
      (circuitBuilderLiteralValid 0 (by omega)) finiteFamilyLastTrueValid
      finiteFamilyFalseValid
    result.builder.evalWire (fun _ => false) (result.wires ⟨2, by omega⟩) = true := by
  native_decide

example :
    let result := CircuitBuilder.muxFin circuitBuilderLiterals 1
      finiteFamilyFalse finiteFamilyLastTrue
      (circuitBuilderLiteralValid 1 (by omega)) finiteFamilyFalseValid
      finiteFamilyLastTrueValid
    result.builder.evalWire (fun _ => false) (result.wires ⟨2, by omega⟩) = true := by
  native_decide

example :
    let result := CircuitBuilder.eqFin circuitBuilderLiterals
      finiteFamilyFalse finiteFamilyLastTrue finiteFamilyFalseValid
      finiteFamilyLastTrueValid
    result.builder.evalWire (fun _ => false) result.wire = false := by
  native_decide

-- The n = 3 family mux follows both selector polarities.
example (i : Fin 3) :
    (CircuitBuilder.muxFin circuitBuilderLiterals 0 finiteFamilyTrue
      finiteFamilyFalse (circuitBuilderLiteralValid 0 (by omega))
      finiteFamilyTrueValid finiteFamilyFalseValid).builder.evalWire
        (fun _ => false)
        ((CircuitBuilder.muxFin circuitBuilderLiterals 0 finiteFamilyTrue
          finiteFamilyFalse (circuitBuilderLiteralValid 0 (by omega))
          finiteFamilyTrueValid finiteFamilyFalseValid).wires i) = true := by
  rw [CircuitBuilder.muxFin_eval]
  simp [finiteFamilyTrue, circuitBuilderLiteralZero_eval]

example (i : Fin 3) :
    (CircuitBuilder.muxFin circuitBuilderLiterals 1 finiteFamilyTrue
      finiteFamilyFalse (circuitBuilderLiteralValid 1 (by omega))
      finiteFamilyTrueValid finiteFamilyFalseValid).builder.evalWire
        (fun _ => false)
        ((CircuitBuilder.muxFin circuitBuilderLiterals 1 finiteFamilyTrue
          finiteFamilyFalse (circuitBuilderLiteralValid 1 (by omega))
          finiteFamilyTrueValid finiteFamilyFalseValid).wires i) = false := by
  rw [CircuitBuilder.muxFin_eval]
  simp [finiteFamilyFalse, circuitBuilderLiteralOne_eval]

example :
    (CircuitBuilder.muxFin circuitBuilderLiterals 0 finiteFamilyTrue
      finiteFamilyFalse (circuitBuilderLiteralValid 0 (by omega))
      finiteFamilyTrueValid finiteFamilyFalseValid).builder.gates.length = 12 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.muxFin_gate_delta circuitBuilderLiterals 0 finiteFamilyTrue
      finiteFamilyFalse (circuitBuilderLiteralValid 0 (by omega))
      finiteFamilyTrueValid finiteFamilyFalseValid

-- Streaming equality accepts equal families and rejects a differing family.
example :
    (CircuitBuilder.eqFin circuitBuilderLiterals finiteFamilyTrue finiteFamilyTrue
      finiteFamilyTrueValid finiteFamilyTrueValid).builder.evalWire (fun _ => false)
        (CircuitBuilder.eqFin circuitBuilderLiterals finiteFamilyTrue finiteFamilyTrue
          finiteFamilyTrueValid finiteFamilyTrueValid).wire = true := by
  rw [CircuitBuilder.eqFin_eval_iff]
  intro i
  rfl

example :
    (CircuitBuilder.eqFin circuitBuilderLiterals finiteFamilyTrue finiteFamilyFalse
      finiteFamilyTrueValid finiteFamilyFalseValid).builder.evalWire (fun _ => false)
        (CircuitBuilder.eqFin circuitBuilderLiterals finiteFamilyTrue finiteFamilyFalse
          finiteFamilyTrueValid finiteFamilyFalseValid).wire = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [CircuitBuilder.eqFin_eval_iff]
  native_decide

example :
    (CircuitBuilder.eqFin circuitBuilderLiterals finiteFamilyTrue finiteFamilyFalse
      finiteFamilyTrueValid finiteFamilyFalseValid).builder.gates.length = 21 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.eqFin_gate_delta circuitBuilderLiterals finiteFamilyTrue
      finiteFamilyFalse finiteFamilyTrueValid finiteFamilyFalseValid

-- Empty and nonempty Boolean folds have the advertised semantics and deltas.
example :
    (circuitBuilderLiterals.conjunction [] (by simp)).1.evalWire (fun _ => false)
      (circuitBuilderLiterals.conjunction [] (by simp)).2 = true := by
  rw [CircuitBuilder.conjunction_eval]
  rfl

example :
    (circuitBuilderLiterals.disjunction [] (by simp)).1.evalWire (fun _ => false)
      (circuitBuilderLiterals.disjunction [] (by simp)).2 = false := by
  rw [CircuitBuilder.disjunction_eval]
  rfl

example :
    (circuitBuilderLiterals.conjunction [0, 1] circuitBuilderPairValid).1.evalWire
      (fun _ => false) (circuitBuilderLiterals.conjunction [0, 1]
        circuitBuilderPairValid).2 = false := by
  rw [CircuitBuilder.conjunction_eval]
  native_decide

example :
    (circuitBuilderLiterals.disjunction [0, 1] circuitBuilderPairValid).1.evalWire
      (fun _ => false) (circuitBuilderLiterals.disjunction [0, 1]
        circuitBuilderPairValid).2 = true := by
  rw [CircuitBuilder.disjunction_eval]
  native_decide

example :
    (circuitBuilderLiterals.conjunction [0, 1]
      circuitBuilderPairValid).1.gates.length = 5 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.conjunction_gate_delta circuitBuilderLiterals [0, 1]
      circuitBuilderPairValid

-- XNOR covers equal and unequal literal pairs; mux covers both polarities.
example :
    (circuitBuilderLiterals.eq 0 0
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 0 (by omega))).1.evalWire (fun _ => false)
        (circuitBuilderLiterals.eq 0 0
          (circuitBuilderLiteralValid 0 (by omega))
          (circuitBuilderLiteralValid 0 (by omega))).2 = true := by
  rw [CircuitBuilder.eq_eval]
  native_decide

example :
    (circuitBuilderLiterals.eq 0 1
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))).1.evalWire (fun _ => false)
        (circuitBuilderLiterals.eq 0 1
          (circuitBuilderLiteralValid 0 (by omega))
          (circuitBuilderLiteralValid 1 (by omega))).2 = false := by
  rw [CircuitBuilder.eq_eval]
  native_decide

example :
    (circuitBuilderLiterals.mux 0 0 1
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))).1.evalWire (fun _ => false)
        (circuitBuilderLiterals.mux 0 0 1
          (circuitBuilderLiteralValid 0 (by omega))
          (circuitBuilderLiteralValid 0 (by omega))
          (circuitBuilderLiteralValid 1 (by omega))).2 = true := by
  rw [CircuitBuilder.mux_eval]
  native_decide

example :
    (circuitBuilderLiterals.mux 1 0 1
      (circuitBuilderLiteralValid 1 (by omega))
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))).1.evalWire (fun _ => false)
        (circuitBuilderLiterals.mux 1 0 1
          (circuitBuilderLiteralValid 1 (by omega))
          (circuitBuilderLiteralValid 0 (by omega))
          (circuitBuilderLiteralValid 1 (by omega))).2 = false := by
  rw [CircuitBuilder.mux_eval]
  native_decide

example :
    (circuitBuilderLiterals.eq 0 1
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))).1.gates.length = 7 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.eq_gate_delta circuitBuilderLiterals 0 1
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))

example :
    (circuitBuilderLiterals.mux 0 0 1
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))).1.gates.length = 6 := by
  simpa [circuitBuilderLiterals] using
    CircuitBuilder.mux_gate_delta circuitBuilderLiterals 0 0 1
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 0 (by omega))
      (circuitBuilderLiteralValid 1 (by omega))

-- Exactly-one is position-sensitive, including repeated aliases.
example :
    (exactlyOne circuitBuilderLiterals [] (by simp)).builder.evalWire
      (fun _ => false) (exactlyOne circuitBuilderLiterals [] (by simp)).wire = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [exactlyOne_eval_iff]
  native_decide

example :
    (exactlyOne circuitBuilderLiterals [0] (by
      intro wire hwire
      simp at hwire
      subst wire
      exact circuitBuilderLiteralValid 0 (by omega))).builder.evalWire
        (fun _ => false) (exactlyOne circuitBuilderLiterals [0] (by
          intro wire hwire
          simp at hwire
          subst wire
          exact circuitBuilderLiteralValid 0 (by omega))).wire = true := by
  rw [exactlyOne_eval_iff]
  native_decide

example :
    (exactlyOne circuitBuilderLiterals [0, 1] circuitBuilderPairValid).builder.evalWire
      (fun _ => false) (exactlyOne circuitBuilderLiterals [0, 1]
        circuitBuilderPairValid).wire = true := by
  rw [exactlyOne_eval_iff]
  native_decide

private def circuitBuilderTruePair : CircuitBuilder where
  inputCount := 0
  gates := [.const true, .const true]
  valid := by
    intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> trivial

private theorem circuitBuilderTruePairValid :
    ∀ wire ∈ ([0, 1] : List Nat), circuitBuilderTruePair.WireValid wire := by
  intro wire hwire
  simp at hwire
  rcases hwire with rfl | rfl <;>
    simp [CircuitBuilder.WireValid, circuitBuilderTruePair]

example :
    (exactlyOne circuitBuilderTruePair [0, 1]
      circuitBuilderTruePairValid).builder.evalWire (fun _ => false)
        (exactlyOne circuitBuilderTruePair [0, 1]
          circuitBuilderTruePairValid).wire = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [exactlyOne_eval_iff]
  native_decide

example :
    (exactlyOne circuitBuilderLiterals [0, 0] (by
      intro wire hwire
      simp at hwire
      subst wire
      exact circuitBuilderLiteralValid 0 (by omega))).builder.evalWire
        (fun _ => false) (exactlyOne circuitBuilderLiterals [0, 0] (by
          intro wire hwire
          simp at hwire
          subst wire
          exact circuitBuilderLiteralValid 0 (by omega))).wire = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [exactlyOne_eval_iff]
  native_decide

example : (exactlyOne circuitBuilderLiterals [] (by simp)).builder.gates.length = 6 := by
  simpa [circuitBuilderLiterals] using
    exactlyOne_gate_delta circuitBuilderLiterals [] (by simp)

example : (exactlyOne circuitBuilderLiterals [0] (by
    intro wire hwire
    simp at hwire
    subst wire
    exact circuitBuilderLiteralValid 0 (by omega))).builder.gates.length = 9 := by
  simpa [circuitBuilderLiterals] using exactlyOne_gate_delta circuitBuilderLiterals [0]
    (by
      intro wire hwire
      simp at hwire
      subst wire
      exact circuitBuilderLiteralValid 0 (by omega))

example : (exactlyOne circuitBuilderLiterals [0, 1]
    circuitBuilderPairValid).builder.gates.length = 12 := by
  simpa [circuitBuilderLiterals] using exactlyOne_gate_delta circuitBuilderLiterals [0, 1]
    circuitBuilderPairValid

private inductive TestK
  | input | output | work
deriving DecidableEq, Fintype

private inductive TestLabel
  | main | loop
deriving DecidableEq, Fintype

private abbrev TestΓ : TestK → Type
  | .input | .output | .work => Bool

/-- A test machine whose main label performs three pushes in one bundled step
and whose second label is a nonhalting self-loop. -/
private abbrev testMachine : _root_.Turing.FinTM2 where
  K := TestK
  k₀ := .input
  k₁ := .output
  Γ := TestΓ
  Λ := TestLabel
  main := .main
  σ := Unit
  initialState := ()
  m
    | .main => push .work (fun _ => true)
        (push .work (fun _ => false)
          (push .work (fun _ => true) halt))
    | .loop => goto fun _ => .loop

private def immediateHaltCfg : testMachine.Cfg where
  l := none
  var := ()
  stk := fun _ => []

private def selfLoopCfg : testMachine.Cfg where
  l := some .loop
  var := ()
  stk := fun _ => []

private theorem immediateHalt_stutters (n : Nat) :
    (stutterStep testMachine)^[n] immediateHaltCfg = immediateHaltCfg := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, stutterStep_halted testMachine (by rfl), ih]

-- A halted row can be padded to any larger exact stuttering horizon.
example : (stutterStep testMachine)^[7] immediateHaltCfg = immediateHaltCfg := by
  exact immediateHalt_stutters 7

example : Nonempty (EvalsToInTime testMachine.step immediateHaltCfg
    (some immediateHaltCfg) 7) :=
  (evalsToInTime_iff_stutter_accepts testMachine rfl 7).mpr (by
    exact immediateHalt_stutters 7)

-- Fixed points need not be halted: the loop label genuinely remains present.
example : selfLoopCfg.l = some .loop := rfl
example : stutterStep testMachine selfLoopCfg = selfLoopCfg := rfl

-- One bundled statement can execute several pushes before reaching halt.
example : stmtMaxPushes testMachine .work (testMachine.m .main) = 3 := rfl
example :
    ((_root_.Turing.TM2.stepAux (testMachine.m .main) ()
      (fun _ => [])).stk .work).length = 3 := rfl

example : 1 < maxPushesPerStep testMachine := by
  have h := stmtMaxPushes_le_maxPushesPerStep testMachine .main .work
  norm_num [testMachine, stmtMaxPushes] at h ⊢
  omega

-- Exact output recognition distinguishes the complete `haltList`, not only
-- its halted label.
example : _root_.Turing.haltList testMachine [true] ≠
    _root_.Turing.haltList testMachine [false] := by
  intro h
  have hout := congrArg (fun c => c.stk testMachine.k₁) h
  simp [_root_.Turing.haltList] at hout

private abbrev EmptyΓ : Unit → Type
  | () => Empty

/-- Empty reachable alphabets and zero tableau height still support a valid
empty configuration code. -/
private abbrev emptyMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := EmptyΓ
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := halt

/-! Actual finite-control circuit regressions use two states and two labels,
while keeping the stack alphabet empty so the control update is isolated. -/

private abbrev controlTestMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := EmptyΓ
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m _ := halt

private def controlCfg : controlTestMachine.Cfg where
  l := some false
  var := false
  stk := fun _ => []

private theorem controlCfgAlphabet :
    CfgAlphabetBounded controlTestMachine controlCfg := by
  intro k a ha
  simp [controlCfg] at ha

private theorem controlCfgHeight :
    ∀ k, (controlCfg.stk k).length ≤ 0 := by
  intro k
  simp [controlCfg]

private def controlLayout : CfgInputLayout controlTestMachine 0 := ⟨0⟩

private noncomputable def controlBase : CircuitBuilder :=
  CircuitBuilder.empty controlLayout.finish

private noncomputable def controlAllocation :
    CfgInputAllocation controlBase controlLayout :=
  allocateCfgInputs controlBase controlLayout (Nat.le_refl _)

private noncomputable def controlPool :
    CircuitBuilder.BoolWirePoolAllocation controlAllocation.builder :=
  CircuitBuilder.allocateBoolWirePool controlAllocation.builder

private def controlAssignment : Nat → Bool := fun _ => false

private noncomputable def controlInputs : Nat → Bool :=
  controlLayout.writeCfgBits controlAssignment
    (encodeRawCfgBits
      (encodeCfg controlTestMachine controlCfgAlphabet controlCfgHeight))

private theorem controlSourceDecoded :
    evalBundle controlPool.builder controlInputs controlAllocation.wires
      (controlAllocation.valid.mono controlPool.extension) = some controlCfg := by
  rw [evalBundle_extends controlPool.extension controlInputs
    controlAllocation.wires controlAllocation.valid]
  exact controlAllocation.evalBundle_write_encodeCfg controlAssignment
    controlCfgAlphabet controlCfgHeight

-- Static encodings exercise actual pool wires for a nonhalting label, the
-- reserved halted label, and a changed state.
example :
    evalStateBits controlPool.builder controlInputs
      (encodeStateWires (tm := controlTestMachine) controlPool.pool true) =
        encodeOneHot (stateEquivFin controlTestMachine true) :=
  encodeStateWires_eval (tm := controlTestMachine) controlPool.pool
    controlInputs true

example :
    evalLabelBits controlPool.builder controlInputs
      (encodeLabelWires (tm := controlTestMachine) controlPool.pool (some true)) =
        encodeOneHot (encodeLabel controlTestMachine (some true)) ∧
      controlPool.builder.evalWire controlInputs
        (encodeLabelHaltedWire (tm := controlTestMachine)
          controlPool.pool (some true)) = false := by
  exact ⟨encodeLabelWires_eval (tm := controlTestMachine) controlPool.pool
      controlInputs (some true),
    encodeLabelHaltedWire_eval (tm := controlTestMachine) controlPool.pool
      controlInputs (some true)⟩

example :
    evalLabelBits controlPool.builder controlInputs
      (encodeLabelWires (tm := controlTestMachine) controlPool.pool none) =
        encodeOneHot (encodeLabel controlTestMachine none) ∧
      controlPool.builder.evalWire controlInputs
        (encodeLabelHaltedWire (tm := controlTestMachine)
          controlPool.pool none) = true := by
  exact ⟨encodeLabelWires_eval (tm := controlTestMachine) controlPool.pool
      controlInputs none,
    encodeLabelHaltedWire_eval (tm := controlTestMachine) controlPool.pool
      controlInputs none⟩

-- Complete-row updates decode through the real allocated row and transported
-- pool, rather than testing only the pure replacement helper.
example :
    evalBundle controlPool.builder controlInputs
      (controlAllocation.wires.replaceState
        (encodeStateWires (tm := controlTestMachine) controlPool.pool true))
      ((controlAllocation.valid.mono controlPool.extension).replaceState
        (encodeStateWires_valid (tm := controlTestMachine)
          controlPool.pool true)) =
        some { controlCfg with var := true } := by
  apply evalBundle_replaceState controlPool.builder controlInputs
    controlAllocation.wires
    (controlAllocation.valid.mono controlPool.extension) controlCfg
    controlSourceDecoded
    (encodeStateWires (tm := controlTestMachine) controlPool.pool true)
    (encodeStateWires_valid (tm := controlTestMachine)
      controlPool.pool true) true
  exact encodeStateWires_eval (tm := controlTestMachine) controlPool.pool
    controlInputs true

example :
    evalBundle controlPool.builder controlInputs
      (controlAllocation.wires.replaceStatus
        (encodeLabelHaltedWire (tm := controlTestMachine)
          controlPool.pool none)
        (encodeLabelWires (tm := controlTestMachine) controlPool.pool none))
      ((controlAllocation.valid.mono controlPool.extension).replaceStatus
        (encodeLabelHaltedWire_valid (tm := controlTestMachine)
          controlPool.pool none)
        (encodeLabelWires_valid (tm := controlTestMachine)
          controlPool.pool none)) =
        some { controlCfg with l := none } := by
  apply evalBundle_replaceStatus controlPool.builder controlInputs
    controlAllocation.wires
    (controlAllocation.valid.mono controlPool.extension) controlCfg
    controlSourceDecoded
    (encodeLabelHaltedWire (tm := controlTestMachine) controlPool.pool none)
    (encodeLabelHaltedWire_valid (tm := controlTestMachine)
      controlPool.pool none)
    (encodeLabelWires (tm := controlTestMachine) controlPool.pool none)
    (encodeLabelWires_valid (tm := controlTestMachine)
      controlPool.pool none) none
  · exact encodeLabelHaltedWire_eval (tm := controlTestMachine)
      controlPool.pool controlInputs none
  · exact encodeLabelWires_eval (tm := controlTestMachine)
      controlPool.pool controlInputs none

private abbrev StackTestΓ : Unit → Type
  | () => Bool

/-- A single-stack test machine whose reachable support contains both Boolean
symbols, avoiding unrelated dependent stack kinds in primitive regressions. -/
private abbrev stackTestMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := StackTestΓ
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := push () (fun _ => true) (push () (fun _ => false) halt)

/-! Pure stack primitives cover every zero/positive alphabet and width corner. -/

private def emptyA0W0 : StackBits emptyMachine 0 () where
  height := fun _ => true
  cell := fun i => Fin.elim0 i

private def emptySymbolBits : SymbolBits emptyMachine () :=
  fun i => Fin.elim0 i

private def emptyMalformedHead : HeadBits emptyMachine () := fun _ => false

-- A=0/W=0 keeps malformed symbol data distinct from the legal empty head.
example : decodeSymbolBits? emptySymbolBits = none := by
  apply decodeSymbolBits_of_card_eq_zero
  simp [reachableAlphabet, stmtPushSet, emptyMachine]

example : decodeHeadBits? (peekStackBits 0 emptyA0W0) = some none := by
  simp

example : decodeHeadBits? emptyMalformedHead = none := by
  unfold decodeHeadBits?
  have hnone : decodeOneHot emptyMalformedHead = none := by
    rw [decodeOneHot_eq_none_iff]
    rintro ⟨chosen, htrue, _⟩
    simp [emptyMalformedHead] at htrue
  simp [hnone]

-- W=0 pop preserves its sole height coordinate and returns the valid empty
-- head rather than malformed head data.
example : (popStackBits 0 emptyA0W0).stack.height 0 =
    emptyA0W0.height 0 := by
  simp

example : decodeHeadBits? (popStackBits 0 emptyA0W0).head = some none := by
  simp

-- A>0/W=0 still has no cells and always peeks the legal empty head.
private def workW0 : StackBits stackTestMachine 0 () where
  height := fun _ => true
  cell := fun i => Fin.elim0 i

example : decodeHeadBits? (peekStackBits 0 workW0) = some none := by
  simp

example : OneHot (peekStackBits 0 workW0) := peekStackBits_zero_oneHot workW0

-- A=0 admits no nonblank one-hot symbol bundle.
example (bits : SymbolBits emptyMachine ()) : ¬ OneHot bits := by
  rintro ⟨chosen, _⟩
  exact Fin.elim0 chosen

private noncomputable def emptyA0W1 : StackBits emptyMachine 1 () where
  height := encodeOneHot (1 : Fin 2)
  cell := fun _ => encodeHeadBits none

private theorem emptyA0W1_raw : emptyA0W1.RawDecodable := by
  refine ⟨oneHot_encodeOneHot 1, ?_⟩
  intro _
  exact oneHot_encodeOneHot _

-- A=0/W=1 is a genuinely full raw stack; overflow fails raw decodability
-- without assuming a symbol one-hot family.
example : ¬ (pushStackBits emptySymbolBits 1 emptyA0W1).RawDecodable := by
  apply pushStackBits_not_rawDecodable_of_full emptySymbolBits emptyA0W1
    emptyA0W1_raw.height
  simp [emptyA0W1, encodeOneHot]

private noncomputable def stackSymbolTrue : SupportedSymbol stackTestMachine () :=
  ⟨true, by simp [reachableAlphabet, stmtPushSet, stackTestMachine]⟩

private noncomputable def stackSymbolFalse : SupportedSymbol stackTestMachine () :=
  ⟨false, by simp [reachableAlphabet, stmtPushSet, stackTestMachine]⟩

example : 0 < (reachableAlphabet stackTestMachine ()).card := by
  apply Finset.card_pos.mpr
  exact ⟨true, stackSymbolTrue.property⟩

private noncomputable def workSymbol0 : SymbolBits stackTestMachine () :=
  encodeSymbolBits stackSymbolTrue

private theorem workSymbol0_oneHot : OneHot workSymbol0 :=
  oneHot_encodeOneHot _

private noncomputable def workW1Empty : StackBits stackTestMachine 1 () where
  height := encodeOneHot (0 : Fin 2)
  cell := fun _ => encodeHeadBits none

private theorem workW1Empty_raw : workW1Empty.RawDecodable := by
  refine ⟨oneHot_encodeOneHot 0, ?_⟩
  intro _
  exact oneHot_encodeOneHot _

private theorem workW1Empty_capacity : workW1Empty.HasCapacity := by
  simp [StackBits.HasCapacity, workW1Empty, encodeOneHot]

-- A>0/W=1: pushing into the singleton capacity produces a full raw stack.
example : (pushStackBits workSymbol0 1 workW1Empty).RawDecodable :=
  pushStackBits_rawDecodable workSymbol0 workW1Empty workSymbol0_oneHot
    workW1Empty_raw workW1Empty_capacity

private theorem workW1Pushed_full :
    (pushStackBits workSymbol0 1 workW1Empty).height 1 = true := by
  simpa [workW1Empty, encodeOneHot] using
    pushStackBits_height_succ workSymbol0 workW1Empty (0 : Fin 1)

private noncomputable def workW1Pushed : StackBits stackTestMachine 1 () :=
  pushStackBits workSymbol0 1 workW1Empty

private theorem workW1Pushed_cell : workW1Pushed.cell 0 =
    encodeHeadBits (some stackSymbolTrue) :=
  pushStackBits_cell_zero_encodeSymbol stackSymbolTrue workW1Empty

example : (pushStackBits workSymbol0 1 workW1Empty).cell 0
    (Fin.last (reachableAlphabet stackTestMachine ()).card) = false :=
  pushStackBits_cell_zero_blank workSymbol0 workW1Empty

-- Popping the pushed singleton returns that symbol and resets every stack
-- coordinate to the canonical empty singleton representation.
example : decodeHeadBits? (popStackBits 1 workW1Pushed).head =
    some (some stackSymbolTrue) := by
  rw [popStackBits_head, peekStackBits_of_pos, workW1Pushed_cell]
  simp

example : (popStackBits 1 workW1Pushed).stack.height 0 = true := by
  change ((pushStackBits workSymbol0 1 workW1Empty).height 0 ||
    (pushStackBits workSymbol0 1 workW1Empty).height 1) = true
  rw [pushStackBits_height_zero, workW1Pushed_full]
  rfl

example : (popStackBits 1 workW1Pushed).stack.height 1 = false := by
  simpa using popStackBits_height_succ (W := 0) workW1Pushed (0 : Fin 1)

example : (popStackBits 1 workW1Pushed).stack.cell 0 =
    encodeHeadBits none := by
  simpa using popStackBits_cell_last (W := 0) workW1Pushed

example : decodeHeadBits? ((popStackBits 1 workW1Pushed).stack.cell 0) =
    some none := by
  rw [show (popStackBits 1 workW1Pushed).stack.cell 0 =
      encodeHeadBits none by
    simpa using popStackBits_cell_last (W := 0) workW1Pushed]
  simp

-- Repeating push on that full singleton exposes overflow, independently of
-- any semantic decoding of the head.
example : ¬ (pushStackBits workSymbol0 1
    (pushStackBits workSymbol0 1 workW1Empty)).RawDecodable := by
  apply pushStackBits_not_rawDecodable_of_full workSymbol0
    (pushStackBits workSymbol0 1 workW1Empty)
    (pushStackBits_rawDecodable workSymbol0 workW1Empty workSymbol0_oneHot
      workW1Empty_raw workW1Empty_capacity).height
  exact workW1Pushed_full

private noncomputable def workW2Two : StackBits stackTestMachine 2 () where
  height := encodeOneHot (2 : Fin 3)
  cell := fun i =>
    if i = 0 then encodeHeadBits (some stackSymbolTrue)
    else encodeHeadBits (some stackSymbolFalse)

private theorem workW2Two_raw : workW2Two.RawDecodable := by
  refine ⟨oneHot_encodeOneHot 2, ?_⟩
  intro i
  by_cases hi : i = 0 <;>
    simp [workW2Two, hi, encodeHeadBits, oneHot_encodeOneHot]

-- W=2 nonuniform cells verify old head return, left shift, and final blank.
example : (popStackBits 2 workW2Two).head = workW2Two.cell 0 := rfl

example : decodeHeadBits? (workW2Two.cell 0) =
    some (some stackSymbolTrue) := by
  simp [workW2Two]

example : decodeHeadBits? (workW2Two.cell 1) =
    some (some stackSymbolFalse) := by
  simp [workW2Two]

example : (popStackBits 2 workW2Two).stack.cell 0 = workW2Two.cell 1 := by
  exact popStackBits_cell_of_next (W := 1) workW2Two (0 : Fin 2) (by decide)

example : (popStackBits 2 workW2Two).stack.cell 1 = encodeHeadBits none := by
  exact popStackBits_cell_last workW2Two

example : (popStackBits 2 workW2Two).stack.RawDecodable :=
  popStackBits_rawDecodable workW2Two workW2Two_raw

/-! Canonical list semantics cover the same exact stack boundaries. -/

private noncomputable def semanticA0W0 : StackBits emptyMachine 0 () :=
  encodeBoundedStackBits
    (encodeBoundedStack emptyMachine () [] (by simp) (by simp))

private theorem semanticA0W0_represents : semanticA0W0.Represents [] :=
  StackBits.Represents.of_encode [] (by simp) (by simp)

-- A=0/W=0 represents only the empty list, remains stable under pop, and has
-- no push capacity despite its well-formed one-hot height coordinate.
example : semanticA0W0.RawDecodable := semanticA0W0_represents.rawDecodable

example : ¬ semanticA0W0.HasCapacity := by
  intro hcapacity
  have hlength :=
    (represents_hasCapacity_iff semanticA0W0_represents).mp hcapacity
  omega

example : decodeHeadValue? (peekStackBits 0 semanticA0W0) = some none := by
  exact peekStackBits_represents semanticA0W0_represents

example :
    (popStackBits 0 semanticA0W0).stack.Represents [] ∧
      decodeHeadValue? (popStackBits 0 semanticA0W0).head = some none := by
  simpa using popStackBits_represents semanticA0W0_represents

-- The wire-level zero-width pop boundary allocates no gate.
example : popStackWireGateCost 0 = 0 := by simp

-- Every positive-width wire-level pop allocates exactly its height-zero OR.
example : popStackWireGateCost 3 = 1 := by simp

/-! The actual A=0/W=0 wire path reuses one shared constant pool.  Peek is a
pure wire selection in the original builder; pop returns that same builder;
capacity alone appends one NOT gate. -/

private def emptyA0W0Wires : StackWires emptyMachine 0 () where
  height := fun _ => literalBoolWirePool.pool.trueWire
  cell := fun i => Fin.elim0 i

private theorem emptyA0W0Wires_valid :
    emptyA0W0Wires.ValidIn literalBoolWirePool.builder := by
  constructor
  · intro _
    exact literalBoolWirePool.pool.trueValid
  · intro i
    exact Fin.elim0 i

private noncomputable def emptyA0W0Peek : HeadWires emptyMachine () :=
  peekStackWires literalBoolWirePool.pool 0 emptyA0W0Wires

example : emptyA0W0Peek.ValidIn literalBoolWirePool.builder :=
  peekStackWires_valid literalBoolWirePool.pool emptyA0W0Wires
    emptyA0W0Wires_valid

example :
    decodeHeadValue?
      (evalHeadBits literalBoolWirePool.builder (fun _ => false)
        emptyA0W0Peek) = some none := by
  rw [emptyA0W0Peek, peekStackWires_eval]
  simp

private noncomputable def emptyA0W0Pop :=
  popStackWires literalBoolWirePool.builder literalBoolWirePool.pool
    emptyA0W0Wires emptyA0W0Wires_valid

-- Width-zero pop is a genuine builder identity and returns the pool-backed
-- legal empty-head bundle, not malformed all-false head data.
example : emptyA0W0Pop.builder = literalBoolWirePool.builder ∧
    emptyA0W0Pop.stack = emptyA0W0Wires ∧
    emptyA0W0Pop.head = encodeHeadWires literalBoolWirePool.pool none := by
  simp [emptyA0W0Pop, popStackWires]

example :
    decodeHeadValue?
      (evalHeadBits emptyA0W0Pop.builder (fun _ => false)
        emptyA0W0Pop.head) = some none := by
  rw [emptyA0W0Pop.head_eval]
  simp

private noncomputable def emptyA0W0Capacity :=
  stackCapacity literalBoolWirePool.builder emptyA0W0Wires
    emptyA0W0Wires_valid

example : emptyA0W0Capacity.builder.gates.length =
    literalBoolWirePool.builder.gates.length + 1 :=
  emptyA0W0Capacity.gate_delta

-- The canonical empty width-zero stack is already full, so NOT full-height
-- evaluates to false even though its height family is well formed.
example : emptyA0W0Capacity.builder.evalWire (fun _ => false)
    emptyA0W0Capacity.wire = false := by
  rw [emptyA0W0Capacity.eval]
  simp [emptyA0W0Wires, literalBoolWirePool.pool.true_eval]

private noncomputable def semanticW1Empty : StackBits stackTestMachine 1 () :=
  encodeBoundedStackBits
    (encodeBoundedStack stackTestMachine () [] (by simp) (by simp))

private theorem semanticW1Empty_represents : semanticW1Empty.Represents [] :=
  StackBits.Represents.of_encode [] (by simp) (by simp)

private theorem semanticW1Empty_capacity : semanticW1Empty.HasCapacity :=
  (represents_hasCapacity_iff semanticW1Empty_represents).mpr (by simp)

private theorem semanticW1Pushed_represents :
    (pushStackBits (encodeSymbolBits stackSymbolTrue) 1
      semanticW1Empty).Represents [stackSymbolTrue.val] :=
  pushStackBits_represents semanticW1Empty_represents stackSymbolTrue
    semanticW1Empty_capacity

-- A>0/W=1 exercises the complete semantic push/peek/pop round trip.
example : decodeHeadValue?
    (peekStackBits 1
      (pushStackBits (encodeSymbolBits stackSymbolTrue) 1 semanticW1Empty)) =
      some (some true) := by
  simpa [stackSymbolTrue] using
    peekStackBits_represents semanticW1Pushed_represents

example :
    (popStackBits 1
        (pushStackBits (encodeSymbolBits stackSymbolTrue) 1 semanticW1Empty)).stack
        |>.Represents [] := by
  exact (popStackBits_represents semanticW1Pushed_represents).1

example : decodeHeadValue?
    (popStackBits 1
      (pushStackBits (encodeSymbolBits stackSymbolTrue) 1 semanticW1Empty)).head =
      some (some true) := by
  simpa [stackSymbolTrue] using
    (popStackBits_represents semanticW1Pushed_represents).2

private theorem semanticW2Alphabet :
    ∀ a, a ∈ ([true, false] : List Bool) →
      a ∈ reachableAlphabet stackTestMachine () := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact stackSymbolTrue.property
  · exact stackSymbolFalse.property

private noncomputable def semanticW2Full : StackBits stackTestMachine 2 () :=
  encodeBoundedStackBits
    (encodeBoundedStack stackTestMachine () [true, false]
      semanticW2Alphabet (by simp))

private theorem semanticW2Full_represents :
    semanticW2Full.Represents [true, false] :=
  StackBits.Represents.of_encode (tm := stackTestMachine) (W := 2) (k := ())
    [true, false] semanticW2Alphabet (by simp)

-- W=2 full and nonuniform: capacity is false, pop returns true, and the
-- remaining canonical stack represents exactly [false].
example : ¬ semanticW2Full.HasCapacity := by
  rw [represents_hasCapacity_iff semanticW2Full_represents]
  simp

example :
    (popStackBits 2 semanticW2Full).stack.Represents [false] := by
  simpa using (popStackBits_represents semanticW2Full_represents).1

example : decodeHeadValue? (popStackBits 2 semanticW2Full).head =
    some (some true) := by
  simpa using (popStackBits_represents semanticW2Full_represents).2

private def emptyRowTrue : CfgWires emptyMachine 0 := fun _ => 0

private def emptyRowFalse : CfgWires emptyMachine 0 := fun _ => 1

private noncomputable def emptyRowHaltedTrue : CfgWires emptyMachine 0 :=
  fun slot => if slot = CfgSlot.halted emptyMachine 0 then 0 else 1

private theorem emptyRowTrueValid :
    emptyRowTrue.ValidIn circuitBuilderLiterals := by
  intro slot
  exact circuitBuilderLiteralValid 0 (by omega)

private theorem emptyRowFalseValid :
    emptyRowFalse.ValidIn circuitBuilderLiterals := by
  intro slot
  exact circuitBuilderLiteralValid 1 (by omega)

private theorem emptyRowHaltedTrueValid :
    emptyRowHaltedTrue.ValidIn circuitBuilderLiterals := by
  intro slot
  simp only [emptyRowHaltedTrue]
  split <;> exact circuitBuilderLiteralValid _ (by omega)

private noncomputable def emptyNamedMuxTrue :=
  cfgMux circuitBuilderLiterals 0 emptyRowHaltedTrue emptyRowFalse
    (circuitBuilderLiteralValid 0 (by omega)) emptyRowHaltedTrueValid
    emptyRowFalseValid

private noncomputable def emptyNamedMuxFalse :=
  cfgMux circuitBuilderLiterals 1 emptyRowHaltedTrue emptyRowFalse
    (circuitBuilderLiteralValid 1 (by omega)) emptyRowHaltedTrueValid
    emptyRowFalseValid

-- Whole-row selection directly evaluates both selector polarities.
example :
    evalCfgBits
        (cfgMux circuitBuilderLiterals 0 emptyRowTrue emptyRowFalse
          (circuitBuilderLiteralValid 0 (by omega)) emptyRowTrueValid
          emptyRowFalseValid).builder
        (fun _ => false)
        (cfgMux circuitBuilderLiterals 0 emptyRowTrue emptyRowFalse
          (circuitBuilderLiteralValid 0 (by omega)) emptyRowTrueValid
          emptyRowFalseValid).wires = fun _ => true := by
  rw [cfgMux_eval]
  funext slot
  simp [evalCfgBits, emptyRowTrue, circuitBuilderLiteralZero_eval]

example :
    evalCfgBits
        (cfgMux circuitBuilderLiterals 1 emptyRowTrue emptyRowFalse
          (circuitBuilderLiteralValid 1 (by omega)) emptyRowTrueValid
          emptyRowFalseValid).builder
        (fun _ => false)
        (cfgMux circuitBuilderLiterals 1 emptyRowTrue emptyRowFalse
          (circuitBuilderLiteralValid 1 (by omega)) emptyRowTrueValid
          emptyRowFalseValid).wires = fun _ => false := by
  rw [cfgMux_eval]
  funext slot
  simp [evalCfgBits, emptyRowFalse, circuitBuilderLiteralOne_eval]

-- A nonuniform row binds flatten/unflatten to named coordinates: only the
-- halted bit is true, while label, state, and height coordinates remain false.
example :
    let bits := evalCfgBits emptyNamedMuxTrue.builder (fun _ => false)
      emptyNamedMuxTrue.wires
    bits.halted = true ∧
      bits.label ⟨0, by simp [labelCount, emptyMachine]⟩ = false ∧
      bits.state ⟨0, by simp [stateCount, emptyMachine]⟩ = false ∧
      bits.stackHeight () ⟨0, by omega⟩ = false := by
  dsimp only
  rw [emptyNamedMuxTrue.eval]
  simp [evalCfgBits, emptyRowHaltedTrue, CfgBundle.halted,
    CfgBundle.label, CfgBundle.state, CfgBundle.stackHeight,
    CfgSlot.halted, CfgSlot.label, CfgSlot.state, CfgSlot.stackHeight,
    circuitBuilderLiteralZero_eval, circuitBuilderLiteralOne_eval]

-- The false selector chooses the uniform-false arm at those same named slots.
example :
    let bits := evalCfgBits emptyNamedMuxFalse.builder (fun _ => false)
      emptyNamedMuxFalse.wires
    bits.halted = false ∧
      bits.label ⟨0, by simp [labelCount, emptyMachine]⟩ = false ∧
      bits.state ⟨0, by simp [stateCount, emptyMachine]⟩ = false ∧
      bits.stackHeight () ⟨0, by omega⟩ = false := by
  dsimp only
  rw [emptyNamedMuxFalse.eval]
  simp [evalCfgBits, emptyRowFalse, CfgBundle.halted, CfgBundle.label,
    CfgBundle.state, CfgBundle.stackHeight, circuitBuilderLiteralOne_eval]

-- The actual empty-machine H = 0 row has five bits, so the generated mux has
-- the two pre-existing literal gates plus 3 * 5 + 1 new gates.
example :
    (cfgMux circuitBuilderLiterals 0 emptyRowTrue emptyRowFalse
      (circuitBuilderLiteralValid 0 (by omega)) emptyRowTrueValid
      emptyRowFalseValid).builder.gates.length = 18 := by
  rw [cfgMux_gate_delta]
  simp [circuitBuilderLiterals, cfgBitCount, emptyMachine, labelCount,
    stateCount, reachableAlphabet, stmtPushSet]

-- Whole-row equality accepts identical rows and rejects a row differing only
-- at the halted coordinate.
example :
    (cfgEq circuitBuilderLiterals emptyRowFalse emptyRowFalse
      emptyRowFalseValid emptyRowFalseValid).builder.evalWire (fun _ => false)
        (cfgEq circuitBuilderLiterals emptyRowFalse emptyRowFalse
          emptyRowFalseValid emptyRowFalseValid).wire = true := by
  rw [cfgEq_eval_iff]

example :
    (cfgEq circuitBuilderLiterals emptyRowFalse emptyRowHaltedTrue
      emptyRowFalseValid emptyRowHaltedTrueValid).builder.evalWire (fun _ => false)
        (cfgEq circuitBuilderLiterals emptyRowFalse emptyRowHaltedTrue
          emptyRowFalseValid emptyRowHaltedTrueValid).wire = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [cfgEq_eval_iff]
  intro heq
  have hhalted := congrFun heq (CfgSlot.halted emptyMachine 0)
  simp [evalCfgBits, emptyRowFalse, emptyRowHaltedTrue,
    circuitBuilderLiteralZero_eval, circuitBuilderLiteralOne_eval] at hhalted

-- The actual equality circuit has the two old gates plus 6 * 5 + 1 new gates.
example :
    (cfgEq circuitBuilderLiterals emptyRowFalse emptyRowHaltedTrue
      emptyRowFalseValid emptyRowHaltedTrueValid).builder.gates.length = 33 := by
  rw [cfgEq_gate_delta]
  simp [circuitBuilderLiterals, cfgBitCount, emptyMachine, labelCount,
    stateCount, reachableAlphabet, stmtPushSet]

private def testStackReplacement : StackBits testMachine 1 TestK.input where
  height := fun _ => true
  cell := fun _ _ => false

private def testRowBits : CfgBits testMachine 1 := fun _ => false

-- Replacement returns the selected dependent stack exactly, leaves a distinct
-- stack unchanged, and preserves non-stack fields.
example :
    (testRowBits.replaceStack TestK.input testStackReplacement).stack TestK.input =
      testStackReplacement := by
  exact CfgBundle.replaceStack_stack_same _ _ _

example :
    (testRowBits.replaceStack TestK.input testStackReplacement).stack TestK.output =
      testRowBits.stack TestK.output := by
  apply CfgBundle.replaceStack_stack_other
  decide

example :
    (testRowBits.replaceStack TestK.input testStackReplacement).halted =
      testRowBits.halted := by
  exact CfgBundle.replaceStack_halted _ _ _

private def emptyStackReplacement : StackBits emptyMachine 0 () where
  height := fun _ => true
  cell := fun i => Fin.elim0 i

private def emptyRowBits : CfgBits emptyMachine 0 := fun _ => false

-- The dependent view/replacement laws also cover H = 0 and an empty machine
-- alphabet, where there are no physical cell coordinates.
example :
    (emptyRowBits.replaceStack () emptyStackReplacement).stack () =
      emptyStackReplacement := by
  exact CfgBundle.replaceStack_stack_same _ _ _

private def emptyCfg : emptyMachine.Cfg :=
  _root_.Turing.initList emptyMachine []

private theorem emptyCfgAlphabet : CfgAlphabetBounded emptyMachine emptyCfg :=
  initList_alphabetBounded emptyMachine []

private theorem emptyCfgHeight : ∀ k, (emptyCfg.stk k).length ≤ 0 := by
  intro k
  cases k
  rfl

example : decodeCfg emptyMachine
    (encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight)
    (encodeCfg_valid emptyMachine emptyCfgAlphabet emptyCfgHeight) = emptyCfg :=
  decodeCfg_encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight

private noncomputable def emptyPositiveRaw : BoundedCfg emptyMachine 1 where
  halted := false
  label := encodeLabel emptyMachine (some ())
  state := stateEquivFin emptyMachine ()
  stack _ :=
    { height := ⟨1, by omega⟩
      cells := fun _ => ⟨0, by simp [reachableAlphabet, emptyMachine]⟩ }

-- An empty support cannot validate a raw stack claiming positive height.
example : ¬ emptyPositiveRaw.Valid := by
  intro h
  have hactive := (h.2 () ⟨0, by omega⟩).mpr (by
    simp [emptyPositiveRaw])
  simp [emptyPositiveRaw, reachableAlphabet, stmtPushSet, emptyMachine] at hactive

example : decodeCfg? emptyMachine emptyPositiveRaw = none := by
  simp [decodeCfg?, show ¬ emptyPositiveRaw.Valid from by
    intro h
    have hactive := (h.2 () ⟨0, by omega⟩).mpr (by
      simp [emptyPositiveRaw])
    simp [emptyPositiveRaw, reachableAlphabet, stmtPushSet, emptyMachine] at hactive]

private def malformedActiveBlank : BoundedStack 1 1 where
  height := ⟨1, by omega⟩
  cells := fun _ => ⟨1, by omega⟩

private def malformedInactiveNonblank : BoundedStack 1 1 where
  height := ⟨0, by omega⟩
  cells := fun _ => ⟨0, by omega⟩

example : ¬ malformedActiveBlank.Valid := by
  intro h
  have := (h ⟨0, by omega⟩).mpr (by simp [malformedActiveBlank])
  simp [malformedActiveBlank] at this

example : ¬ malformedInactiveNonblank.Valid := by
  intro h
  have := (h ⟨0, by omega⟩).mp (by simp [malformedInactiveNonblank])
  simp [malformedInactiveNonblank] at this

private noncomputable def haltedLabelMismatch : BoundedCfg emptyMachine 0 where
  halted := true
  label := encodeLabel emptyMachine (some ())
  state := stateEquivFin emptyMachine ()
  stack _ := { height := ⟨0, by omega⟩, cells := fun i => Fin.elim0 i }

example : ¬ haltedLabelMismatch.Valid := by
  intro h
  have heq := h.1.mp rfl
  simp [haltedLabelMismatch, encodeLabel, labelCount] at heq

-- A valid raw code is accepted and enjoys the public canonical roundtrip.
private noncomputable def validEmptyCode : BoundedCfg emptyMachine 0 :=
  encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight

private theorem validEmptyCode_valid : validEmptyCode.Valid :=
  encodeCfg_valid emptyMachine emptyCfgAlphabet emptyCfgHeight

noncomputable example : Fintype (BoundedCfg emptyMachine 0) := inferInstance

example : decodeCfg? emptyMachine validEmptyCode = some emptyCfg := by
  rw [decodeCfg?]
  split_ifs with h
  · simpa [validEmptyCode] using
      decodeCfg_encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight
  · exact False.elim (h validEmptyCode_valid)

example : encodeCfg emptyMachine
    (decoded_alphabetBounded emptyMachine validEmptyCode validEmptyCode_valid)
    (decoded_stack_length_le emptyMachine validEmptyCode validEmptyCode_valid) =
    validEmptyCode :=
  encodeCfg_decodeCfg emptyMachine validEmptyCode validEmptyCode_valid

-- One-hot decoding is total on every finite coordinate type, including Fin 0.
example : decodeOneHot (fun i : Fin 0 => Fin.elim0 i) = none :=
  decodeOneHot_fin_zero _

example : decodeOneHot (fun _ : Fin 2 => true) = none := by
  rw [decodeOneHot_eq_none_iff]
  rintro ⟨chosen, _, unique⟩
  have hzero := unique 0 rfl
  have hone := unique 1 rfl
  omega

-- Every bounded raw code, including H = 0, round-trips through one-hot bits.
example : decodeRawCfg? (encodeRawCfgBits validEmptyCode) = some validEmptyCode :=
  decodeRawCfg_encode validEmptyCode

private noncomputable def emptyHeightZeroRaw : BoundedCfg emptyMachine 1 where
  halted := false
  label := encodeLabel emptyMachine (some ())
  state := stateEquivFin emptyMachine ()
  stack _ :=
    { height := ⟨0, by omega⟩
      cells := fun _ => ⟨0, by simp [reachableAlphabet, emptyMachine]⟩ }

private theorem emptyHeightZeroRaw_eq_encoded :
    emptyHeightZeroRaw =
      encodeCfg emptyMachine emptyCfgAlphabet (H := 1)
        (fun k => Nat.le_trans (emptyCfgHeight k) (by omega)) := by
  rfl

-- Empty support with height zero and a blank physical cell passes both codec
-- layers; claiming height one still passes the raw codec but fails canonical
-- machine decoding because the blank would be active.
example : decodeRawCfg? (encodeRawCfgBits emptyHeightZeroRaw) =
    some emptyHeightZeroRaw := decodeRawCfg_encode emptyHeightZeroRaw

example : (decodeRawCfg? (encodeRawCfgBits emptyHeightZeroRaw)).bind
    (decodeCfg? emptyMachine) = some emptyCfg := by
  rw [decodeRawCfg_encode]
  simp only [Option.bind_some]
  rw [emptyHeightZeroRaw_eq_encoded]
  unfold decodeCfg?
  rw [dif_pos (encodeCfg_valid emptyMachine emptyCfgAlphabet (H := 1)
    (fun k => Nat.le_trans (emptyCfgHeight k) (by omega)))]
  congr 1
  exact decodeCfg_encodeCfg emptyMachine emptyCfgAlphabet (H := 1)
    (fun k => Nat.le_trans (emptyCfgHeight k) (by omega))

example : decodeRawCfg? (encodeRawCfgBits emptyPositiveRaw) =
    some emptyPositiveRaw := decodeRawCfg_encode emptyPositiveRaw

example : (decodeRawCfg? (encodeRawCfgBits emptyPositiveRaw)).bind
    (decodeCfg? emptyMachine) = none := by
  rw [decodeRawCfg_encode]
  simpa using (show decodeCfg? emptyMachine emptyPositiveRaw = none from by
    simp [decodeCfg?, show ¬ emptyPositiveRaw.Valid from by
      intro h
      have hactive := (h.2 () ⟨0, by omega⟩).mpr (by
        simp [emptyPositiveRaw])
      simp [emptyPositiveRaw, reachableAlphabet, stmtPushSet, emptyMachine] at hactive])

private def firstLayout : CfgInputLayout emptyMachine 0 := ⟨5⟩
private noncomputable def secondLayout : CfgInputLayout emptyMachine 0 := firstLayout.next

private noncomputable def allocationBase : CircuitBuilder :=
  CircuitBuilder.empty secondLayout.finish

private theorem firstLayoutFits : firstLayout.Fits allocationBase.inputCount := by
  change firstLayout.finish ≤ secondLayout.finish
  simp [secondLayout, CfgInputLayout.next, CfgInputLayout.finish]

private theorem secondLayoutFits : secondLayout.Fits allocationBase.inputCount := by
  change secondLayout.finish ≤ secondLayout.finish
  exact Nat.le_refl _

private noncomputable def firstAllocation :
    CfgInputAllocation allocationBase firstLayout :=
  allocateCfgInputs allocationBase firstLayout firstLayoutFits

private noncomputable def firstPool :
    CircuitBuilder.BoolWirePoolAllocation firstAllocation.builder :=
  CircuitBuilder.allocateBoolWirePool firstAllocation.builder

private noncomputable def firstInputs : Nat → Bool :=
  firstLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits
      (encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight))

private theorem firstAllocationValidInPool :
    firstAllocation.wires.ValidIn firstPool.builder :=
  firstAllocation.valid.mono firstPool.extension

private theorem firstPoolDecoded :
    evalBundle firstPool.builder firstInputs firstAllocation.wires
      firstAllocationValidInPool = some emptyCfg := by
  rw [evalBundle_extends firstPool.extension firstInputs firstAllocation.wires
    firstAllocation.valid]
  exact firstAllocation.evalBundle_write_encodeCfg (fun _ => false)
    emptyCfgAlphabet emptyCfgHeight

private noncomputable def firstPop :=
  popCfgWires firstPool.builder firstPool.pool firstAllocation.wires
    firstAllocationValidInPool ()

-- At physical height zero, the complete-row theorem still returns the exact
-- legal empty-head one-hot family, not merely a value that happens to decode.
example :
    evalBundle firstPop.builder firstInputs firstPop.wires firstPop.valid =
        some (cfgPopStack emptyCfg ()) ∧
      decodeHeadValue? (evalHeadBits firstPop.builder firstInputs firstPop.head) =
        some (emptyCfg.stk ()).head? := by
  simpa [firstPop] using
    (popCfgWires_evalBundle firstPool.builder firstPool.pool firstInputs
      firstAllocation.wires firstAllocationValidInPool firstPoolDecoded ())

example :
    evalHeadBits firstPop.builder firstInputs firstPop.head =
      encodeHeadBits (tm := emptyMachine) (k := ()) none := by
  rw [firstPop.head_eval]
  exact popStackBits_zero_head _

private noncomputable def secondAfterFirst :
    CfgInputAllocation firstAllocation.builder secondLayout :=
  allocateCfgInputs firstAllocation.builder secondLayout (by
    rw [firstAllocation.extension.1]
    exact secondLayoutFits)

private noncomputable def secondAllocation :
    CfgInputAllocation allocationBase secondLayout :=
  allocateCfgInputs allocationBase secondLayout secondLayoutFits

private noncomputable def firstAfterSecond :
    CfgInputAllocation secondAllocation.builder firstLayout :=
  allocateCfgInputs secondAllocation.builder firstLayout (by
    rw [secondAllocation.extension.1]
    exact firstLayoutFits)

-- Fresh row allocation has the exact gate count and external-input behavior.
example : firstAllocation.builder.gates.length =
    allocationBase.gates.length + cfgBitCount emptyMachine 0 :=
  firstAllocation.gate_delta

example (inputs : Nat → Bool) (slot : CfgSlot emptyMachine 0) :
    firstAllocation.builder.evalWire inputs (firstAllocation.wires slot) =
      inputs (firstLayout.index slot).val :=
  firstAllocation.eval_slot inputs slot

-- Both decoder layers round-trip through allocated input wires; the validity
-- witness is carried by the allocation rather than inferred from evaluation.
example (assignment : Nat → Bool) :
    evalRawBundle firstAllocation.builder
        (firstLayout.writeCfgBits assignment (encodeRawCfgBits validEmptyCode))
        firstAllocation.wires firstAllocation.valid = some validEmptyCode :=
  firstAllocation.evalRawBundle_write_encode assignment validEmptyCode

example (assignment : Nat → Bool) :
    evalBundle firstAllocation.builder
        (firstLayout.writeCfgBits assignment
          (encodeRawCfgBits (encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight)))
        firstAllocation.wires firstAllocation.valid = some emptyCfg :=
  firstAllocation.evalBundle_write_encodeCfg assignment emptyCfgAlphabet emptyCfgHeight

-- Allocating left then right preserves the old left row and reads the new right
-- row from its own disjoint patch.
example (assignment : Nat → Bool) (firstBits secondBits : CfgBits emptyMachine 0) :
    evalCfgBits secondAfterFirst.builder
        (secondLayout.writeCfgBits
          (firstLayout.writeCfgBits assignment firstBits) secondBits)
        firstAllocation.wires = firstBits := by
  rw [firstAllocation.evalCfgBits_extends secondAfterFirst.extension]
  funext slot
  rw [evalCfgBits, firstAllocation.eval_slot]
  exact CfgInputLayout.writeCfgBits_index_of_disjoint
    (CfgInputLayout.next_disjoint firstLayout) assignment firstBits secondBits slot

example (assignment : Nat → Bool) (firstBits secondBits : CfgBits emptyMachine 0) :
    evalCfgBits secondAfterFirst.builder
        (secondLayout.writeCfgBits
          (firstLayout.writeCfgBits assignment firstBits) secondBits)
        secondAfterFirst.wires = secondBits :=
  secondAfterFirst.evalCfgBits_write
    (firstLayout.writeCfgBits assignment firstBits) secondBits

-- Reversing both construction and patch order has the same noninterference
-- guarantee.
example (assignment : Nat → Bool) (firstBits secondBits : CfgBits emptyMachine 0) :
    evalCfgBits firstAfterSecond.builder
        (firstLayout.writeCfgBits
          (secondLayout.writeCfgBits assignment secondBits) firstBits)
        secondAllocation.wires = secondBits := by
  rw [secondAllocation.evalCfgBits_extends firstAfterSecond.extension]
  funext slot
  rw [evalCfgBits, secondAllocation.eval_slot]
  exact CfgInputLayout.writeCfgBits_index_of_disjoint (by
    rw [CfgInputLayout.Disjoint]
    right
    simp [secondLayout, CfgInputLayout.next])
    assignment secondBits firstBits slot

example (assignment : Nat → Bool) (firstBits secondBits : CfgBits emptyMachine 0) :
    evalCfgBits firstAfterSecond.builder
        (firstLayout.writeCfgBits
          (secondLayout.writeCfgBits assignment secondBits) firstBits)
        firstAfterSecond.wires = firstBits :=
  firstAfterSecond.evalCfgBits_write
    (secondLayout.writeCfgBits assignment secondBits) firstBits

-- Patching one fresh row does not disturb a disjoint earlier row.
example (assignment : Nat → Bool) (firstBits secondBits : CfgBits emptyMachine 0)
    (slot : CfgSlot emptyMachine 0) :
    secondLayout.writeCfgBits (firstLayout.writeCfgBits assignment firstBits)
        secondBits (firstLayout.index slot).val = firstBits slot := by
  exact CfgInputLayout.writeCfgBits_index_of_disjoint
    (CfgInputLayout.next_disjoint firstLayout) assignment firstBits secondBits slot

-- A malformed row with no selected label is rejected before machine validity
-- is even considered.
private noncomputable def missingLabelBits : CfgBits emptyMachine 0 :=
  fun slot => match slot with
    | .inr (.inl _) => false
    | other => encodeRawCfgBits validEmptyCode other

example : decodeRawCfg? missingLabelBits = none := by
  rw [decodeRawCfg_eq_none_iff]
  intro h
  rcases h.1 with ⟨label, hlabel, _⟩
  simp [missingLabelBits] at hlabel

/-! Canonical row-validity circuit regressions. -/

private theorem validCfgCircuit_rejects_invalidCode
    {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {layout : CfgInputLayout tm H}
    (allocation : CfgInputAllocation start layout)
    (assignment : Nat → Bool) (code : BoundedCfg tm H)
    (hinvalid : ¬ code.Valid) :
    (validCfgCircuit allocation.builder allocation.wires allocation.valid).builder.evalWire
        (layout.writeCfgBits assignment (encodeRawCfgBits code))
        (validCfgCircuit allocation.builder allocation.wires allocation.valid).wire =
      false := by
  apply Bool.eq_false_of_not_eq_true
  intro haccepted
  have hsome := (validCfgCircuit_eval_iff allocation.builder
    (layout.writeCfgBits assignment (encodeRawCfgBits code))
    allocation.wires allocation.valid).mp haccepted
  unfold evalBundle evalRawBundle at hsome
  rw [allocation.evalCfgBits_write, decodeRawCfg_encode] at hsome
  simp only [Option.bind_some] at hsome
  unfold decodeCfg? at hsome
  rw [dif_neg hinvalid] at hsome
  contradiction

-- H = 0 with an empty reachable alphabet accepts the canonical empty row.
example (assignment : Nat → Bool) :
    (validCfgCircuit firstAllocation.builder firstAllocation.wires
      firstAllocation.valid).builder.evalWire
        (firstLayout.writeCfgBits assignment
          (encodeRawCfgBits
            (encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight)))
        (validCfgCircuit firstAllocation.builder firstAllocation.wires
          firstAllocation.valid).wire = true := by
  apply validCfgCircuit_accepts_encodeCfg firstAllocation.builder _
    firstAllocation.wires firstAllocation.valid emptyCfgAlphabet emptyCfgHeight
  exact firstAllocation.evalCfgBits_write assignment _

-- The halted bit must agree with the reserved none-label coordinate.
example (assignment : Nat → Bool) :
    (validCfgCircuit firstAllocation.builder firstAllocation.wires
      firstAllocation.valid).builder.evalWire
        (firstLayout.writeCfgBits assignment
          (encodeRawCfgBits haltedLabelMismatch))
        (validCfgCircuit firstAllocation.builder firstAllocation.wires
          firstAllocation.valid).wire = false :=
  validCfgCircuit_rejects_invalidCode firstAllocation assignment
    haltedLabelMismatch (by
      intro h
      have heq := h.1.mp rfl
      simp [haltedLabelMismatch, encodeLabel, labelCount] at heq)

private def emptyHeightOneLayout : CfgInputLayout emptyMachine 1 := ⟨0⟩

private noncomputable def emptyHeightOneBase : CircuitBuilder :=
  CircuitBuilder.empty emptyHeightOneLayout.finish

private noncomputable def emptyHeightOneAllocation :
    CfgInputAllocation emptyHeightOneBase emptyHeightOneLayout :=
  allocateCfgInputs emptyHeightOneBase emptyHeightOneLayout (Nat.le_refl _)

-- H = 1, empty alphabet: height one makes the sole blank cell active, so the
-- row is rejected; height zero leaves that blank inactive and is accepted.
example (assignment : Nat → Bool) :
    (validCfgCircuit emptyHeightOneAllocation.builder
      emptyHeightOneAllocation.wires emptyHeightOneAllocation.valid).builder.evalWire
        (emptyHeightOneLayout.writeCfgBits assignment
          (encodeRawCfgBits emptyPositiveRaw))
        (validCfgCircuit emptyHeightOneAllocation.builder
          emptyHeightOneAllocation.wires emptyHeightOneAllocation.valid).wire = false :=
  validCfgCircuit_rejects_invalidCode emptyHeightOneAllocation assignment
    emptyPositiveRaw (by
      intro h
      have hactive := (h.2 () ⟨0, by omega⟩).mpr (by simp [emptyPositiveRaw])
      simp [emptyPositiveRaw, reachableAlphabet, stmtPushSet, emptyMachine] at hactive)

example (assignment : Nat → Bool) :
    (validCfgCircuit emptyHeightOneAllocation.builder
      emptyHeightOneAllocation.wires emptyHeightOneAllocation.valid).builder.evalWire
        (emptyHeightOneLayout.writeCfgBits assignment
          (encodeRawCfgBits emptyHeightZeroRaw))
        (validCfgCircuit emptyHeightOneAllocation.builder
          emptyHeightOneAllocation.wires emptyHeightOneAllocation.valid).wire = true := by
  rw [emptyHeightZeroRaw_eq_encoded]
  apply validCfgCircuit_accepts_encodeCfg emptyHeightOneAllocation.builder _
    emptyHeightOneAllocation.wires emptyHeightOneAllocation.valid
    emptyCfgAlphabet
    (fun k => Nat.le_trans (emptyCfgHeight k) (by omega))
  exact emptyHeightOneAllocation.evalCfgBits_write assignment _

private abbrev OneStackΓ : Unit → Type
  | () => Bool

private abbrev oneStackMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := OneStackΓ
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _ := push () (fun _ => true) halt

private noncomputable def inactiveNonblankRaw : BoundedCfg oneStackMachine 1 where
  halted := false
  label := encodeLabel oneStackMachine (some ())
  state := stateEquivFin oneStackMachine ()
  stack _ :=
    { height := ⟨0, by omega⟩
      cells := fun _ => ⟨0, by
        simp [reachableAlphabet, stmtPushSet, oneStackMachine]⟩ }

private theorem inactiveNonblankRaw_invalid : ¬ inactiveNonblankRaw.Valid := by
  intro h
  have hinactive := (h.2 () ⟨0, by omega⟩).mp (by
    simp [inactiveNonblankRaw, reachableAlphabet, stmtPushSet, oneStackMachine])
  simp [inactiveNonblankRaw] at hinactive

private def oneStackLayout : CfgInputLayout oneStackMachine 1 := ⟨0⟩

private noncomputable def oneStackBase : CircuitBuilder :=
  CircuitBuilder.empty oneStackLayout.finish

private noncomputable def oneStackAllocation :
    CfgInputAllocation oneStackBase oneStackLayout :=
  allocateCfgInputs oneStackBase oneStackLayout (Nat.le_refl _)

private def oneStackCfg : oneStackMachine.Cfg where
  l := some ()
  var := ()
  stk := fun _ => [true]

private theorem oneStackCfgAlphabet :
    CfgAlphabetBounded oneStackMachine oneStackCfg := by
  intro k a ha
  cases k
  simp only [oneStackCfg, List.mem_singleton] at ha
  subst a
  simp [reachableAlphabet, stmtPushSet, oneStackMachine]

private theorem oneStackCfgHeight :
    ∀ k, (oneStackCfg.stk k).length ≤ 1 := by
  intro k
  cases k
  simp [oneStackCfg]

-- An actual allocated row, written with canonical bits and decoded through
-- evalBundle, exposes the corresponding list-level stack representation.
example (assignment : Nat → Bool) :
    StackBits.Represents
      ((evalCfgBits oneStackAllocation.builder
        (oneStackLayout.writeCfgBits assignment
          (encodeRawCfgBits
            (encodeCfg oneStackMachine oneStackCfgAlphabet oneStackCfgHeight)))
        oneStackAllocation.wires).stack ()) [true] := by
  have hdecoded := oneStackAllocation.evalBundle_write_encodeCfg assignment
    oneStackCfgAlphabet oneStackCfgHeight
  simpa [oneStackCfg] using
    evalBundle_stack_represents oneStackAllocation.builder
      (oneStackLayout.writeCfgBits assignment
        (encodeRawCfgBits
          (encodeCfg oneStackMachine oneStackCfgAlphabet oneStackCfgHeight)))
      oneStackAllocation.wires oneStackAllocation.valid
      (c := oneStackCfg) hdecoded ()

-- H = 1 with a nonempty alphabet: a nonblank cell outside height zero is
-- rejected by the inactive-blank half of the linear active-mask invariant.
example (assignment : Nat → Bool) :
    (validCfgCircuit oneStackAllocation.builder oneStackAllocation.wires
      oneStackAllocation.valid).builder.evalWire
        (oneStackLayout.writeCfgBits assignment
          (encodeRawCfgBits inactiveNonblankRaw))
        (validCfgCircuit oneStackAllocation.builder oneStackAllocation.wires
          oneStackAllocation.valid).wire = false :=
  validCfgCircuit_rejects_invalidCode oneStackAllocation assignment
    inactiveNonblankRaw inactiveNonblankRaw_invalid

-- Exact closed costs cover both zero and positive height boundaries.
example : validCfgGateCost emptyMachine 0 = 35 := by
  simp [validCfgGateCost, emptyMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

example : validCfgGateCost emptyMachine 1 = 54 := by
  simp [validCfgGateCost, emptyMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

example :
    (validCfgCircuit firstAllocation.builder firstAllocation.wires
      firstAllocation.valid).builder.gates.length =
      firstAllocation.builder.gates.length + 35 := by
  rw [validCfgCircuit_gate_delta]
  simp [validCfgGateCost, emptyMachine, labelCount, stateCount,
    reachableAlphabet, stmtPushSet]

/-! One-step workspace bridge regressions. -/

example : maxPushesPerStep emptyMachine = 0 := by
  simp [maxPushesPerStep, emptyMachine, stmtMaxPushes]

private noncomputable def emptyWorkspaceWiden :=
  widenCfg firstAllocation.builder firstAllocation.wires firstAllocation.valid

private noncomputable def emptyWorkspaceNarrow :=
  narrowCfg emptyWorkspaceWiden.builder emptyWorkspaceWiden.wires
    emptyWorkspaceWiden.valid

-- H = 0 and an empty reachable alphabet still follow the fixed two-gate
-- widening path; the machine also exercises the M = 0 narrowing path.
example : emptyWorkspaceWiden.builder.gates.length =
    firstAllocation.builder.gates.length + 2 :=
  widenCfg_gate_delta firstAllocation.builder firstAllocation.wires
    firstAllocation.valid

-- The M = 0 widening result exposes its shared constants to downstream code.
example (inputs : Nat → Bool) :
    emptyWorkspaceWiden.builder.evalWire inputs
        emptyWorkspaceWiden.constants.falseWire = false ∧
      emptyWorkspaceWiden.builder.evalWire inputs
        emptyWorkspaceWiden.constants.trueWire = true :=
  ⟨emptyWorkspaceWiden.constants.false_eval inputs,
    emptyWorkspaceWiden.constants.true_eval inputs⟩

private theorem emptyWorkspaceWiden_fits (inputs : Nat → Bool) :
    (evalCfgBits emptyWorkspaceWiden.builder inputs
      emptyWorkspaceWiden.wires).FitsHeight := by
  rw [show evalCfgBits emptyWorkspaceWiden.builder inputs
      emptyWorkspaceWiden.wires =
        widenCfgBits (evalCfgBits firstAllocation.builder inputs
          firstAllocation.wires) from by
    simpa only [emptyWorkspaceWiden] using
      widenCfg_eval firstAllocation.builder firstAllocation.wires
        firstAllocation.valid inputs]
  exact widenCfgBits_fitsHeight _

example : emptyWorkspaceNarrow.builder.gates.length =
    emptyWorkspaceWiden.builder.gates.length + 2 := by
  rw [emptyWorkspaceNarrow.gate_delta]
  simp [maxPushesPerStep, emptyMachine, stmtMaxPushes]

example (inputs : Nat → Bool) :
    emptyWorkspaceNarrow.builder.evalWire inputs emptyWorkspaceNarrow.fit = true := by
  exact (emptyWorkspaceNarrow.fit_eval inputs).mpr
    (emptyWorkspaceWiden_fits inputs)

example (assignment : Nat → Bool) :
    evalBundle emptyWorkspaceNarrow.builder
        (firstLayout.writeCfgBits assignment
          (encodeRawCfgBits
            (encodeCfg emptyMachine emptyCfgAlphabet emptyCfgHeight)))
        emptyWorkspaceNarrow.wires emptyWorkspaceNarrow.valid = some emptyCfg := by
  apply narrowCfg_decode_preserved _ _ _ _ emptyCfg
  · apply widenCfg_decode_preserved _ _ _ _ emptyCfg
    exact firstAllocation.evalBundle_write_encodeCfg assignment
      emptyCfgAlphabet emptyCfgHeight
  · exact (emptyWorkspaceNarrow.fit_eval _).mpr
      (emptyWorkspaceWiden_fits _)

example (bits : CfgBits emptyMachine 0) :
    narrowCfgBits (widenCfgBits bits) = bits :=
  narrowCfgBits_widenCfgBits bits

private def testHeightZeroLayout : CfgInputLayout testMachine 0 := ⟨0⟩

private noncomputable def testHeightZeroBase : CircuitBuilder :=
  CircuitBuilder.empty testHeightZeroLayout.finish

private noncomputable def testHeightZeroAllocation :
    CfgInputAllocation testHeightZeroBase testHeightZeroLayout :=
  allocateCfgInputs testHeightZeroBase testHeightZeroLayout (Nat.le_refl _)

private noncomputable def testWorkspaceWiden :=
  widenCfg testHeightZeroAllocation.builder testHeightZeroAllocation.wires
    testHeightZeroAllocation.valid

private noncomputable def testWorkspaceNarrow :=
  narrowCfg testWorkspaceWiden.builder testWorkspaceWiden.wires
    testWorkspaceWiden.valid

-- The multi-push regression computes the complete bundled path, not merely
-- one syntactic push node.
private theorem testMachine_maxPushes_eq : maxPushesPerStep testMachine = 3 := by
  classical
  apply Nat.le_antisymm
  · unfold maxPushesPerStep
    apply Finset.sup_le
    intro label _
    apply Finset.sup_le
    intro k _
    cases label <;> cases k <;> simp [testMachine, stmtMaxPushes]
  · have h := stmtMaxPushes_le_maxPushesPerStep testMachine .main .work
    norm_num [testMachine, stmtMaxPushes] at h ⊢
    exact h

example : maxPushesPerStep testMachine = 3 := testMachine_maxPushes_eq

example : workHeight testMachine 0 = 3 := by
  simp [workHeight, testMachine_maxPushes_eq]

-- The M = 3 widening path publishes the same exact constant-pool interface.
example (inputs : Nat → Bool) :
    testWorkspaceWiden.builder.evalWire inputs
        testWorkspaceWiden.constants.falseWire = false ∧
      testWorkspaceWiden.builder.evalWire inputs
        testWorkspaceWiden.constants.trueWire = true :=
  ⟨testWorkspaceWiden.constants.false_eval inputs,
    testWorkspaceWiden.constants.true_eval inputs⟩

/-! The M=3 regression threads an actual builder, one shared pool, complete
rows, and extension proofs through three sequential capacity/push rounds and
three pops. -/

private noncomputable def testWorkTrue : SupportedSymbol testMachine .work :=
  ⟨true, stmtPushSet_program_subset testMachine .main .work (by
    simp [testMachine, stmtPushSet])⟩

private noncomputable def testWorkFalse : SupportedSymbol testMachine .work :=
  ⟨false, stmtPushSet_program_subset testMachine .main .work (by
    simp [testMachine, stmtPushSet])⟩

private noncomputable def testCapacity0 :=
  cfgStackCapacity testWorkspaceWiden.builder testWorkspaceWiden.wires
    testWorkspaceWiden.valid TestK.work

private noncomputable def testPoolAfterCapacity0 :
    CircuitBuilder.BoolWirePool testCapacity0.builder :=
  testWorkspaceWiden.constants.mono testCapacity0.extension

private theorem testWiden_valid_after_capacity0 :
    testWorkspaceWiden.wires.ValidIn testCapacity0.builder :=
  testWorkspaceWiden.valid.mono testCapacity0.extension

private noncomputable def testWorkTrueWires1 : SymbolWires testMachine .work :=
  encodeSymbolWires testPoolAfterCapacity0 testWorkTrue

private noncomputable def testPush1 :=
  pushCfgWires testPoolAfterCapacity0 testWorkTrueWires1
    testWorkspaceWiden.wires

private theorem testPush1_valid :
    testPush1.ValidIn testCapacity0.builder :=
  pushCfgWires_valid testPoolAfterCapacity0 testWorkTrueWires1
    testWorkspaceWiden.wires
    (encodeSymbolWires_valid testPoolAfterCapacity0 testWorkTrue)
    testWiden_valid_after_capacity0

private noncomputable def testCapacity1 :=
  cfgStackCapacity testCapacity0.builder testPush1 testPush1_valid TestK.work

private noncomputable def testPoolAfterCapacity1 :
    CircuitBuilder.BoolWirePool testCapacity1.builder :=
  testPoolAfterCapacity0.mono testCapacity1.extension

private theorem testPush1_valid_after_capacity1 :
    testPush1.ValidIn testCapacity1.builder :=
  testPush1_valid.mono testCapacity1.extension

private noncomputable def testWorkFalseWires2 : SymbolWires testMachine .work :=
  encodeSymbolWires testPoolAfterCapacity1 testWorkFalse

private noncomputable def testPush2 :=
  pushCfgWires testPoolAfterCapacity1 testWorkFalseWires2 testPush1

private theorem testPush2_valid :
    testPush2.ValidIn testCapacity1.builder :=
  pushCfgWires_valid testPoolAfterCapacity1 testWorkFalseWires2 testPush1
    (encodeSymbolWires_valid testPoolAfterCapacity1 testWorkFalse)
    testPush1_valid_after_capacity1

private noncomputable def testCapacity2 :=
  cfgStackCapacity testCapacity1.builder testPush2 testPush2_valid TestK.work

private noncomputable def testPoolAfterCapacity2 :
    CircuitBuilder.BoolWirePool testCapacity2.builder :=
  testPoolAfterCapacity1.mono testCapacity2.extension

private theorem testPush2_valid_after_capacity2 :
    testPush2.ValidIn testCapacity2.builder :=
  testPush2_valid.mono testCapacity2.extension

private noncomputable def testWorkTrueWires3 : SymbolWires testMachine .work :=
  encodeSymbolWires testPoolAfterCapacity2 testWorkTrue

private noncomputable def testPush3 :=
  pushCfgWires testPoolAfterCapacity2 testWorkTrueWires3 testPush2

private theorem testPush3_valid :
    testPush3.ValidIn testCapacity2.builder :=
  pushCfgWires_valid testPoolAfterCapacity2 testWorkTrueWires3 testPush2
    (encodeSymbolWires_valid testPoolAfterCapacity2 testWorkTrue)
    testPush2_valid_after_capacity2

private noncomputable def testPop1 :=
  popCfgWires testCapacity2.builder testPoolAfterCapacity2
    testPush3 testPush3_valid .work

private noncomputable def testPopPool1 :
    CircuitBuilder.BoolWirePool testPop1.builder :=
  testPoolAfterCapacity2.mono testPop1.extension

private noncomputable def testPop2 :=
  popCfgWires testPop1.builder testPopPool1 testPop1.wires testPop1.valid .work

private noncomputable def testPopPool2 :
    CircuitBuilder.BoolWirePool testPop2.builder :=
  testPopPool1.mono testPop2.extension

private noncomputable def testPop3 :=
  popCfgWires testPop2.builder testPopPool2 testPop2.wires testPop2.valid .work

private theorem immediateHaltCfgAlphabet :
    CfgAlphabetBounded testMachine immediateHaltCfg := by
  intro k a ha
  simp [immediateHaltCfg] at ha

private theorem immediateHaltCfgHeight :
    ∀ k, (immediateHaltCfg.stk k).length ≤ 0 := by
  intro k
  cases k <;> rfl

private noncomputable def testStackInputs : Nat → Bool :=
  testHeightZeroLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits
      (encodeCfg testMachine immediateHaltCfgAlphabet immediateHaltCfgHeight))

private theorem testWorkspaceWiden_decoded :
    evalBundle testWorkspaceWiden.builder testStackInputs
      testWorkspaceWiden.wires testWorkspaceWiden.valid = some immediateHaltCfg := by
  apply widenCfg_decode_preserved _ _ _ _ immediateHaltCfg
  exact testHeightZeroAllocation.evalBundle_write_encodeCfg (fun _ => false)
    immediateHaltCfgAlphabet immediateHaltCfgHeight

private theorem testWorkspaceWiden_decoded_after_capacity0 :
    evalBundle testCapacity0.builder testStackInputs testWorkspaceWiden.wires
      testWiden_valid_after_capacity0 = some immediateHaltCfg := by
  rw [evalBundle_extends testCapacity0.extension testStackInputs
    testWorkspaceWiden.wires testWorkspaceWiden.valid]
  exact testWorkspaceWiden_decoded

private noncomputable def testCfg1 : testMachine.Cfg :=
  cfgPushStack immediateHaltCfg .work testWorkTrue.val

private noncomputable def testCfg2 : testMachine.Cfg :=
  cfgPushStack testCfg1 .work testWorkFalse.val

private noncomputable def testCfg3 : testMachine.Cfg :=
  cfgPushStack testCfg2 .work testWorkTrue.val

-- The actual M = 3 builder pipeline now checks complete decoded rows after
-- every push, not only the selected stack's representation predicate.
private theorem testPush1_decoded :
    evalBundle testCapacity0.builder testStackInputs testPush1 testPush1_valid =
      some testCfg1 := by
  simpa [testPush1, testCfg1] using
    (pushCfgWires_evalBundle testCapacity0.builder testPoolAfterCapacity0
      testStackInputs testWorkTrueWires1 testWorkspaceWiden.wires
      testWiden_valid_after_capacity0
      (encodeSymbolWires_valid testPoolAfterCapacity0 testWorkTrue)
      testWorkspaceWiden_decoded_after_capacity0 testWorkTrue
      (encodeSymbolWires_eval testPoolAfterCapacity0 testStackInputs
        testWorkTrue)
      (by simp [immediateHaltCfg, workHeight, testMachine_maxPushes_eq]))

private theorem testPush1_decoded_after_capacity1 :
    evalBundle testCapacity1.builder testStackInputs testPush1
      testPush1_valid_after_capacity1 = some testCfg1 := by
  rw [evalBundle_extends testCapacity1.extension testStackInputs testPush1
    testPush1_valid]
  exact testPush1_decoded

private theorem testPush2_decoded :
    evalBundle testCapacity1.builder testStackInputs testPush2 testPush2_valid =
      some testCfg2 := by
  simpa [testPush2, testCfg2] using
    (pushCfgWires_evalBundle testCapacity1.builder testPoolAfterCapacity1
      testStackInputs testWorkFalseWires2 testPush1
      testPush1_valid_after_capacity1
      (encodeSymbolWires_valid testPoolAfterCapacity1 testWorkFalse)
      testPush1_decoded_after_capacity1 testWorkFalse
      (encodeSymbolWires_eval testPoolAfterCapacity1 testStackInputs
        testWorkFalse)
      (by simp [testCfg1, immediateHaltCfg, workHeight,
        testMachine_maxPushes_eq]))

private theorem testPush2_decoded_after_capacity2 :
    evalBundle testCapacity2.builder testStackInputs testPush2
      testPush2_valid_after_capacity2 = some testCfg2 := by
  rw [evalBundle_extends testCapacity2.extension testStackInputs testPush2
    testPush2_valid]
  exact testPush2_decoded

private theorem testPush3_decoded :
    evalBundle testCapacity2.builder testStackInputs testPush3 testPush3_valid =
      some testCfg3 := by
  simpa [testPush3, testCfg3] using
    (pushCfgWires_evalBundle testCapacity2.builder testPoolAfterCapacity2
      testStackInputs testWorkTrueWires3 testPush2
      testPush2_valid_after_capacity2
      (encodeSymbolWires_valid testPoolAfterCapacity2 testWorkTrue)
      testPush2_decoded_after_capacity2 testWorkTrue
      (encodeSymbolWires_eval testPoolAfterCapacity2 testStackInputs
        testWorkTrue)
      (by simp [testCfg2, testCfg1, immediateHaltCfg, workHeight,
        testMachine_maxPushes_eq]))

-- Zero-gate peek exposes the same exact canonical head on the real nonempty
-- workspace row, before any pop builder extends it.
example :
    ∃ head : SupportedHead testMachine .work,
      (testCfg3.stk .work).head? = head.map Subtype.val ∧
        evalHeadBits testCapacity2.builder testStackInputs
            (peekCfgWires TestK.work testPoolAfterCapacity2 testPush3) =
          encodeHeadBits head :=
  peekCfgWires_head_eq_encode_of_evalBundle testCapacity2.builder
    testPoolAfterCapacity2 testStackInputs testPush3 testPush3_valid
    testPush3_decoded .work

private theorem testPop1_decoded :
    evalBundle testPop1.builder testStackInputs testPop1.wires testPop1.valid =
        some (cfgPopStack testCfg3 .work) ∧
      decodeHeadValue?
          (evalHeadBits testPop1.builder testStackInputs testPop1.head) =
        some (testCfg3.stk .work).head? := by
  simpa [testPop1] using
    (popCfgWires_evalBundle testCapacity2.builder testPoolAfterCapacity2
      testStackInputs testPush3 testPush3_valid testPush3_decoded .work)

private theorem testPop2_decoded :
    evalBundle testPop2.builder testStackInputs testPop2.wires testPop2.valid =
        some (cfgPopStack (cfgPopStack testCfg3 .work) .work) ∧
      decodeHeadValue?
          (evalHeadBits testPop2.builder testStackInputs testPop2.head) =
        some ((cfgPopStack testCfg3 .work).stk .work).head? := by
  simpa [testPop2] using
    (popCfgWires_evalBundle testPop1.builder testPopPool1 testStackInputs
      testPop1.wires testPop1.valid testPop1_decoded.1 .work)

private theorem testPop3_decoded :
    evalBundle testPop3.builder testStackInputs testPop3.wires testPop3.valid =
        some
          (cfgPopStack (cfgPopStack (cfgPopStack testCfg3 .work) .work) .work) ∧
      decodeHeadValue?
          (evalHeadBits testPop3.builder testStackInputs testPop3.head) =
        some
          ((cfgPopStack (cfgPopStack testCfg3 .work) .work).stk .work).head? := by
  simpa [testPop3] using
    (popCfgWires_evalBundle testPop2.builder testPopPool2 testStackInputs
      testPop2.wires testPop2.valid testPop2_decoded.1 .work)

-- Downstream finite-control lookup receives an exact canonical old-head row
-- from the real nonempty builder pipeline.
example :
    ∃ head : SupportedHead testMachine .work,
      (testCfg3.stk .work).head? = head.map Subtype.val ∧
        evalHeadBits testPop1.builder testStackInputs testPop1.head =
          encodeHeadBits head := by
  simpa [testPop1] using
    (popCfgWires_head_eq_encode_of_evalBundle testCapacity2.builder
      testPoolAfterCapacity2 testStackInputs testPush3 testPush3_valid
      testPush3_decoded .work)

private theorem testPush1_represents :
    StackBits.Represents
      ((evalCfgBits testCapacity0.builder testStackInputs testPush1).stack
        .work) [true] := by
  apply pushCfgWires_represents_of_evalBundle testCapacity0.builder
    testPoolAfterCapacity0 testStackInputs testWorkTrueWires1
    testWorkspaceWiden.wires testWiden_valid_after_capacity0
    testWorkspaceWiden_decoded_after_capacity0 testWorkTrue
  · exact encodeSymbolWires_eval testPoolAfterCapacity0 testStackInputs testWorkTrue
  · simp [immediateHaltCfg, workHeight, testMachine_maxPushes_eq]

private theorem testPush1_represents_after_capacity1 :
    StackBits.Represents
      ((evalCfgBits testCapacity1.builder testStackInputs testPush1).stack .work)
      [true] := by
  rw [evalCfgBits_extends testCapacity1.extension testStackInputs testPush1
    testPush1_valid]
  exact testPush1_represents

private theorem testPush2_represents :
    StackBits.Represents
      ((evalCfgBits testCapacity1.builder testStackInputs testPush2).stack
        .work) [false, true] := by
  rw [testPush2, pushCfgWires_eval]
  simp only [CfgBundle.replaceStack_stack_same]
  rw [testWorkFalseWires2, encodeSymbolWires_eval]
  apply pushStackBits_represents testPush1_represents_after_capacity1
    testWorkFalse
  rw [represents_hasCapacity_iff testPush1_represents_after_capacity1]
  simp [workHeight, testMachine_maxPushes_eq]

private theorem testPush2_represents_after_capacity2 :
    StackBits.Represents
      ((evalCfgBits testCapacity2.builder testStackInputs testPush2).stack .work)
      [false, true] := by
  rw [evalCfgBits_extends testCapacity2.extension testStackInputs testPush2
    testPush2_valid]
  exact testPush2_represents

private theorem testPush3_represents :
    StackBits.Represents
      ((evalCfgBits testCapacity2.builder testStackInputs testPush3).stack
        .work) [true, false, true] := by
  rw [testPush3, pushCfgWires_eval]
  simp only [CfgBundle.replaceStack_stack_same]
  rw [testWorkTrueWires3, encodeSymbolWires_eval]
  apply pushStackBits_represents testPush2_represents_after_capacity2 testWorkTrue
  rw [represents_hasCapacity_iff testPush2_represents_after_capacity2]
  simp [workHeight, testMachine_maxPushes_eq]

private theorem testPop1_represents :
    StackBits.Represents
      ((evalCfgBits testPop1.builder testStackInputs testPop1.wires).stack .work)
      [false, true] := by
  have heval := congrArg (fun bits => bits.stack TestK.work)
    (testPop1.eval testStackInputs)
  simp only [CfgBundle.replaceStack_stack_same] at heval
  rw [heval]
  exact (popStackBits_represents testPush3_represents).1

private theorem testPop2_represents :
    StackBits.Represents
      ((evalCfgBits testPop2.builder testStackInputs testPop2.wires).stack .work)
      [true] := by
  have heval := congrArg (fun bits => bits.stack TestK.work)
    (testPop2.eval testStackInputs)
  simp only [CfgBundle.replaceStack_stack_same] at heval
  rw [heval]
  exact (popStackBits_represents testPop1_represents).1

private theorem testPop3_represents :
    StackBits.Represents
      ((evalCfgBits testPop3.builder testStackInputs testPop3.wires).stack .work)
      [] := by
  have heval := congrArg (fun bits => bits.stack TestK.work)
    (testPop3.eval testStackInputs)
  simp only [CfgBundle.replaceStack_stack_same] at heval
  rw [heval]
  exact (popStackBits_represents testPop2_represents).1

-- The three old heads return in stack order and the final stack is empty.
example :
    decodeHeadValue? (evalHeadBits testPop1.builder testStackInputs testPop1.head) =
        some (some true) ∧
      decodeHeadValue? (evalHeadBits testPop2.builder testStackInputs testPop2.head) =
        some (some false) ∧
      decodeHeadValue? (evalHeadBits testPop3.builder testStackInputs testPop3.head) =
        some (some true) := by
  constructor
  · rw [testPop1.head_eval]
    simpa using (popStackBits_represents testPush3_represents).2
  · constructor
    · rw [testPop2.head_eval]
      simpa using (popStackBits_represents testPop1_represents).2
    · rw [testPop3.head_eval]
      simpa using (popStackBits_represents testPop2_represents).2

example :
    StackBits.Represents
      ((evalCfgBits testPop3.builder testStackInputs testPop3.wires).stack .work)
      [] := testPop3_represents

-- Each positive-width pop adds one gate; capacity remains a separate one-NOT
-- query and does not change the zero-gate push cost.
example : testPop1.builder.gates.length =
      testCapacity2.builder.gates.length + 1 ∧
    testPop2.builder.gates.length = testPop1.builder.gates.length + 1 ∧
    testPop3.builder.gates.length = testPop2.builder.gates.length + 1 := by
  simpa [workHeight, testMachine_maxPushes_eq] using
    And.intro testPop1.gate_delta (And.intro testPop2.gate_delta testPop3.gate_delta)

private theorem testCapacity0_eval :
    testCapacity0.builder.evalWire testStackInputs testCapacity0.wire = true := by
  change (stackCapacity testWorkspaceWiden.builder
    (testWorkspaceWiden.wires.stack .work)
    (testWorkspaceWiden.valid.stack .work)).builder.evalWire testStackInputs
      (stackCapacity testWorkspaceWiden.builder
        (testWorkspaceWiden.wires.stack .work)
        (testWorkspaceWiden.valid.stack .work)).wire = true
  rw [stackCapacity_eval_iff, evalStackBits_cfgStack]
  rw [represents_hasCapacity_iff
    (evalBundle_stack_represents testWorkspaceWiden.builder testStackInputs
      testWorkspaceWiden.wires testWorkspaceWiden.valid
      testWorkspaceWiden_decoded .work)]
  simp [immediateHaltCfg, workHeight, testMachine_maxPushes_eq]

private theorem testCapacity1_eval :
    testCapacity1.builder.evalWire testStackInputs testCapacity1.wire = true := by
  change (stackCapacity testCapacity0.builder (testPush1.stack .work)
    (testPush1_valid.stack .work)).builder.evalWire testStackInputs
      (stackCapacity testCapacity0.builder (testPush1.stack .work)
        (testPush1_valid.stack .work)).wire = true
  rw [stackCapacity_eval_iff, evalStackBits_cfgStack]
  rw [represents_hasCapacity_iff testPush1_represents]
  simp [workHeight, testMachine_maxPushes_eq]

private theorem testCapacity2_eval :
    testCapacity2.builder.evalWire testStackInputs testCapacity2.wire = true := by
  change (stackCapacity testCapacity1.builder (testPush2.stack .work)
    (testPush2_valid.stack .work)).builder.evalWire testStackInputs
      (stackCapacity testCapacity1.builder (testPush2.stack .work)
        (testPush2_valid.stack .work)).wire = true
  rw [stackCapacity_eval_iff, evalStackBits_cfgStack]
  rw [represents_hasCapacity_iff testPush2_represents]
  simp [workHeight, testMachine_maxPushes_eq]

-- The three capacity queries are one real sequential builder pipeline.  Each
-- evaluates to true before its corresponding push and appends exactly one NOT.
example :
    testCapacity0.builder.gates.length =
        testWorkspaceWiden.builder.gates.length + 1 ∧
      testCapacity1.builder.gates.length =
        testCapacity0.builder.gates.length + 1 ∧
      testCapacity2.builder.gates.length =
        testCapacity1.builder.gates.length + 1 ∧
      testCapacity0.builder.evalWire testStackInputs testCapacity0.wire = true ∧
      testCapacity1.builder.evalWire testStackInputs testCapacity1.wire = true ∧
      testCapacity2.builder.evalWire testStackInputs testCapacity2.wire = true := by
  exact ⟨testCapacity0.gate_delta, testCapacity1.gate_delta,
    testCapacity2.gate_delta, testCapacity0_eval, testCapacity1_eval,
    testCapacity2_eval⟩

-- The concrete sequential builder contains the three capacity NOTs followed
-- by the three positive-width pop ORs: six gates over the widened-row prefix.
example : testPop3.builder.gates.length =
    testWorkspaceWiden.builder.gates.length + 6 := by
  have hc₀ := testCapacity0.gate_delta
  have hc₁ := testCapacity1.gate_delta
  have hc₂ := testCapacity2.gate_delta
  have hp₁ := testPop1.gate_delta
  have hp₂ := testPop2.gate_delta
  have hp₃ := testPop3.gate_delta
  simp [workHeight, testMachine_maxPushes_eq] at hp₁ hp₂ hp₃
  omega

-- Full row frames survive all three pushes and three pops, including different
-- stacks; the capacity stages extend only the builder and leave the row intact.
private theorem testSixSteps_halted_frame :
    testPop3.wires.halted = testWorkspaceWiden.wires.halted := by
  calc
    testPop3.wires.halted = testPop2.wires.halted := by
      change (popCfgWires testPop2.builder testPopPool2 testPop2.wires
        testPop2.valid .work).wires.halted = testPop2.wires.halted
      exact popCfgWires_halted _ _ _ _ _
    _ = testPop1.wires.halted := by
      change (popCfgWires testPop1.builder testPopPool1 testPop1.wires
        testPop1.valid .work).wires.halted = testPop1.wires.halted
      exact popCfgWires_halted _ _ _ _ _
    _ = testPush3.halted := by
      change (popCfgWires testCapacity2.builder
        testPoolAfterCapacity2 testPush3 testPush3_valid
        .work).wires.halted = testPush3.halted
      exact popCfgWires_halted _ _ _ _ _
    _ = testPush2.halted := pushCfgWires_halted _ _ _
    _ = testPush1.halted := pushCfgWires_halted _ _ _
    _ = testWorkspaceWiden.wires.halted := pushCfgWires_halted _ _ _

private theorem testSixSteps_label_frame :
    testPop3.wires.label = testWorkspaceWiden.wires.label := by
  funext i
  calc
    testPop3.wires.label i = testPop2.wires.label i := by
      change (popCfgWires testPop2.builder testPopPool2 testPop2.wires
        testPop2.valid .work).wires.label i = testPop2.wires.label i
      exact popCfgWires_label _ _ _ _ _ i
    _ = testPop1.wires.label i := by
      change (popCfgWires testPop1.builder testPopPool1 testPop1.wires
        testPop1.valid .work).wires.label i = testPop1.wires.label i
      exact popCfgWires_label _ _ _ _ _ i
    _ = testPush3.label i := by
      change (popCfgWires testCapacity2.builder
        testPoolAfterCapacity2 testPush3 testPush3_valid
        .work).wires.label i = testPush3.label i
      exact popCfgWires_label _ _ _ _ _ i
    _ = testPush2.label i := pushCfgWires_label _ _ _ i
    _ = testPush1.label i := pushCfgWires_label _ _ _ i
    _ = testWorkspaceWiden.wires.label i := pushCfgWires_label _ _ _ i

private theorem testSixSteps_state_frame :
    testPop3.wires.state = testWorkspaceWiden.wires.state := by
  funext i
  calc
    testPop3.wires.state i = testPop2.wires.state i := by
      change (popCfgWires testPop2.builder testPopPool2 testPop2.wires
        testPop2.valid .work).wires.state i = testPop2.wires.state i
      exact popCfgWires_state _ _ _ _ _ i
    _ = testPop1.wires.state i := by
      change (popCfgWires testPop1.builder testPopPool1 testPop1.wires
        testPop1.valid .work).wires.state i = testPop1.wires.state i
      exact popCfgWires_state _ _ _ _ _ i
    _ = testPush3.state i := by
      change (popCfgWires testCapacity2.builder
        testPoolAfterCapacity2 testPush3 testPush3_valid
        .work).wires.state i = testPush3.state i
      exact popCfgWires_state _ _ _ _ _ i
    _ = testPush2.state i := pushCfgWires_state _ _ _ i
    _ = testPush1.state i := pushCfgWires_state _ _ _ i
    _ = testWorkspaceWiden.wires.state i := pushCfgWires_state _ _ _ i

private theorem testSixSteps_stack_other_frame (other : TestK)
    (hother : other ≠ .work) :
    testPop3.wires.stack other = testWorkspaceWiden.wires.stack other := by
  calc
    testPop3.wires.stack other = testPop2.wires.stack other := by
      change (popCfgWires testPop2.builder testPopPool2 testPop2.wires
        testPop2.valid .work).wires.stack other = testPop2.wires.stack other
      exact popCfgWires_stack_other testPop2.builder testPopPool2 testPop2.wires
        testPop2.valid .work other hother
    _ = testPop1.wires.stack other := by
      change (popCfgWires testPop1.builder testPopPool1 testPop1.wires
        testPop1.valid .work).wires.stack other = testPop1.wires.stack other
      exact popCfgWires_stack_other testPop1.builder testPopPool1 testPop1.wires
        testPop1.valid .work other hother
    _ = testPush3.stack other := by
      change (popCfgWires testCapacity2.builder
        testPoolAfterCapacity2 testPush3 testPush3_valid
        .work).wires.stack other = testPush3.stack other
      exact popCfgWires_stack_other testCapacity2.builder
        testPoolAfterCapacity2 testPush3 testPush3_valid .work other hother
    _ = testPush2.stack other := by
      change (pushCfgWires testPoolAfterCapacity2 testWorkTrueWires3
        testPush2).stack other = testPush2.stack other
      exact pushCfgWires_stack_other testPoolAfterCapacity2
        testWorkTrueWires3 testPush2 other hother
    _ = testPush1.stack other := by
      change (pushCfgWires testPoolAfterCapacity1 testWorkFalseWires2
        testPush1).stack other = testPush1.stack other
      exact pushCfgWires_stack_other testPoolAfterCapacity1
        testWorkFalseWires2 testPush1 other hother
    _ = testWorkspaceWiden.wires.stack other := by
      change (pushCfgWires testPoolAfterCapacity0 testWorkTrueWires1
        testWorkspaceWiden.wires).stack other =
          testWorkspaceWiden.wires.stack other
      exact pushCfgWires_stack_other testPoolAfterCapacity0
        testWorkTrueWires1 testWorkspaceWiden.wires other hother

example : testPop3.wires.halted = testWorkspaceWiden.wires.halted ∧
    testPop3.wires.label = testWorkspaceWiden.wires.label ∧
    testPop3.wires.state = testWorkspaceWiden.wires.state ∧
    testPop3.wires.stack .input = testWorkspaceWiden.wires.stack .input ∧
    testPop3.wires.stack .output = testWorkspaceWiden.wires.stack .output := by
  exact ⟨testSixSteps_halted_frame, testSixSteps_label_frame,
    testSixSteps_state_frame,
    testSixSteps_stack_other_frame .input (by decide),
    testSixSteps_stack_other_frame .output (by decide)⟩

-- The input stack has an empty reachable alphabet even though another stack
-- makes M = 3; its first extra physical cell is therefore the sole blank bit.
example (inputs : Nat → Bool) :
    let cell : Fin (workHeight testMachine 0) :=
      ⟨0, by simp [workHeight, testMachine_maxPushes_eq]⟩
    let blank := Fin.last (reachableAlphabet testMachine TestK.input).card
    testWorkspaceWiden.builder.evalWire inputs
      (testWorkspaceWiden.wires.stackCell TestK.input cell blank) = true := by
  dsimp only
  change evalCfgBits testWorkspaceWiden.builder inputs testWorkspaceWiden.wires
      (CfgSlot.stackCell TestK.input
        ⟨0, by simp [workHeight, testMachine_maxPushes_eq]⟩
        (Fin.last (reachableAlphabet testMachine TestK.input).card)) = true
  rw [testWorkspaceWiden.eval]
  simp [CfgSlot.stackCell, widenCfgBits]

example : testWorkspaceNarrow.builder.gates.length =
    testWorkspaceWiden.builder.gates.length + 11 := by
  rw [testWorkspaceNarrow.gate_delta, testMachine_maxPushes_eq]
  have hcard : Fintype.card TestK = 3 := by native_decide
  rw [hcard]

private theorem testWorkspaceWiden_fits (inputs : Nat → Bool) :
    (evalCfgBits testWorkspaceWiden.builder inputs
      testWorkspaceWiden.wires).FitsHeight := by
  rw [show evalCfgBits testWorkspaceWiden.builder inputs
      testWorkspaceWiden.wires =
        widenCfgBits (evalCfgBits testHeightZeroAllocation.builder inputs
          testHeightZeroAllocation.wires) from by
    simpa only [testWorkspaceWiden] using
      widenCfg_eval testHeightZeroAllocation.builder testHeightZeroAllocation.wires
        testHeightZeroAllocation.valid inputs]
  exact widenCfgBits_fitsHeight _

example (inputs : Nat → Bool) :
    testWorkspaceNarrow.builder.evalWire inputs testWorkspaceNarrow.fit = true := by
  exact (testWorkspaceNarrow.fit_eval inputs).mpr
    (testWorkspaceWiden_fits inputs)

private def testWorkspaceLayout :
    CfgInputLayout testMachine (workHeight testMachine 0) := ⟨0⟩

private noncomputable def testWorkspaceBase : CircuitBuilder :=
  CircuitBuilder.empty testWorkspaceLayout.finish

private noncomputable def testWorkspaceAllocation :
    CfgInputAllocation testWorkspaceBase testWorkspaceLayout :=
  allocateCfgInputs testWorkspaceBase testWorkspaceLayout (Nat.le_refl _)

private def selectedOverflowBits :
    CfgBits testMachine (workHeight testMachine 0) :=
  fun slot => match slot with
    | .inr (.inr (.inr ⟨.work, .inl height⟩)) => decide (height.val = 1)
    | _ => false

private theorem selectedOverflowBits_not_fits :
    ¬ selectedOverflowBits.FitsHeight := by
  intro hfit
  have h := hfit TestK.work
    (⟨0, by rw [testMachine_maxPushes_eq]; omega⟩)
  norm_num [selectedOverflowBits] at h

-- The actual fit circuit rejects a row selecting the first overflow height.
example (assignment : Nat → Bool) :
    let narrowed := narrowCfg testWorkspaceAllocation.builder
      testWorkspaceAllocation.wires testWorkspaceAllocation.valid
    narrowed.builder.evalWire
        (testWorkspaceLayout.writeCfgBits assignment selectedOverflowBits)
        narrowed.fit = false := by
  dsimp only
  apply Bool.eq_false_of_not_eq_true
  intro htrue
  have hfits := (narrowCfg_fit_iff testWorkspaceAllocation.builder
    testWorkspaceAllocation.wires testWorkspaceAllocation.valid
    (testWorkspaceLayout.writeCfgBits assignment selectedOverflowBits)).mp htrue
  rw [testWorkspaceAllocation.evalCfgBits_write] at hfits
  exact selectedOverflowBits_not_fits hfits

/- Recursive statement compiler regressions -/

private theorem testMachineMainSupport :
    ∀ k, stmtPushSet testMachine (testMachine.m .main) k ⊆
      reachableAlphabet testMachine k :=
  fun k => stmtPushSet_program_subset testMachine .main k

private noncomputable def testCompiledMain :=
  compileStmt testMachine (workHeight testMachine 0) testWorkspaceWiden.builder
    testWorkspaceWiden.constants testWorkspaceWiden.wires
    testWorkspaceWiden.valid (testMachine.m .main) testMachineMainSupport

-- The existing M=3 actual allocated row now runs through the complete
-- recursive statement compiler and reaches the exact three-push halt row.
example :
    evalBundle testCompiledMain.builder testStackInputs testCompiledMain.wires
      testCompiledMain.valid =
        some (_root_.Turing.TM2.stepAux (testMachine.m .main)
          immediateHaltCfg.var immediateHaltCfg.stk) := by
  apply compileStmt_evalBundle testMachine (workHeight testMachine 0)
    testWorkspaceWiden.builder testWorkspaceWiden.constants testStackInputs
    testWorkspaceWiden.wires testWorkspaceWiden.valid (testMachine.m .main)
    testMachineMainSupport testWorkspaceWiden_decoded
  intro k
  cases k <;>
    simp [immediateHaltCfg, testMachine, stmtMaxPushes, workHeight,
      testMachine_maxPushes_eq]

-- A nontrivial statement has the exact structural gate count advertised by
-- the proof-carrying compiler result.
example : testCompiledMain.builder.gates.length =
    testWorkspaceWiden.builder.gates.length +
      compileStmtGateCost testMachine (workHeight testMachine 0)
        (testMachine.m .main) :=
  testCompiledMain.gate_delta

private abbrev StatementTestMachine : _root_.Turing.FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ => Bool
  Λ := Bool
  main := false
  σ := Bool
  initialState := false
  m := fun _ => halt

private def statementCfg (state : Bool) (stack : List Bool) :
    StatementTestMachine.Cfg where
  l := some false
  var := state
  stk := fun _ => stack

private theorem statementCfgAlphabet (state : Bool) (stack : List Bool) :
    CfgAlphabetBounded StatementTestMachine (statementCfg state stack) := by
  intro k a ha
  cases k
  cases a <;> simp [reachableAlphabet, StatementTestMachine]

private theorem statementSupport
    (q : _root_.Turing.TM2.Stmt StatementTestMachine.Γ
      StatementTestMachine.Λ StatementTestMachine.σ) :
    ∀ k, stmtPushSet StatementTestMachine q k ⊆
      reachableAlphabet StatementTestMachine k := by
  intro k a ha
  cases k
  cases a <;> simp [reachableAlphabet, StatementTestMachine]

private def statementLayout : CfgInputLayout StatementTestMachine 1 := ⟨0⟩

private noncomputable def statementBase : CircuitBuilder :=
  CircuitBuilder.empty statementLayout.finish

private noncomputable def statementAllocation :
    CfgInputAllocation statementBase statementLayout :=
  allocateCfgInputs statementBase statementLayout (Nat.le_refl _)

private noncomputable def statementPool :=
  CircuitBuilder.allocateBoolWirePool statementAllocation.builder

private theorem statementSourceValid :
    statementAllocation.wires.ValidIn statementPool.builder :=
  statementAllocation.valid.mono statementPool.extension

private noncomputable def statementInputs (state : Bool) (stack : List Bool)
    (hstack : stack.length ≤ 1) : Nat → Bool :=
  statementLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits (encodeCfg StatementTestMachine
      (statementCfgAlphabet state stack) (fun k => by cases k; exact hstack)))

private theorem statementDecoded (state : Bool) (stack : List Bool)
    (hstack : stack.length ≤ 1) :
    evalBundle statementPool.builder (statementInputs state stack hstack)
      statementAllocation.wires statementSourceValid =
        some (statementCfg state stack) := by
  rw [evalBundle_extends statementPool.extension
    (statementInputs state stack hstack) statementAllocation.wires
    statementAllocation.valid]
  exact statementAllocation.evalBundle_write_encodeCfg (fun _ => false)
    (statementCfgAlphabet state stack) (fun k => by cases k; exact hstack)

private def statementBranch : _root_.Turing.TM2.Stmt
    StatementTestMachine.Γ StatementTestMachine.Λ StatementTestMachine.σ :=
  branch id
    (load (fun state => !state) (push () (fun state => state) halt))
    (pop () (fun state head => state || head.isNone) halt)

private noncomputable def compiledStatementBranch :=
  compileStmt StatementTestMachine 1 statementPool.builder statementPool.pool
    statementAllocation.wires statementSourceValid statementBranch
    (statementSupport statementBranch)

-- The structurally different arms are emitted serially from the same actual
-- source row: the true arm maps state and pushes, while the false arm pops.
-- Both selectors below validate the final complete-row mux output.
example : statementPool.builder.Extends compiledStatementBranch.builder :=
  compiledStatementBranch.extension

example :
    evalBundle compiledStatementBranch.builder
      (statementInputs true [] (by simp)) compiledStatementBranch.wires
      compiledStatementBranch.valid =
        some { statementCfg false [false] with l := none } := by
  have h := compileStmt_evalBundle StatementTestMachine 1 statementPool.builder
      statementPool.pool (statementInputs true [] (by simp))
      statementAllocation.wires statementSourceValid statementBranch
      (statementSupport statementBranch) (statementDecoded true [] (by simp))
      (by intro k; cases k; simp [statementBranch, statementCfg,
        stmtMaxPushes])
  unfold compiledStatementBranch
  exact h.trans (by
    congr 1)

example :
    evalBundle compiledStatementBranch.builder
      (statementInputs false [] (by simp)) compiledStatementBranch.wires
      compiledStatementBranch.valid =
        some { statementCfg true [] with l := none } := by
  have h := compileStmt_evalBundle StatementTestMachine 1 statementPool.builder
      statementPool.pool (statementInputs false [] (by simp))
      statementAllocation.wires statementSourceValid statementBranch
      (statementSupport statementBranch) (statementDecoded false [] (by simp))
      (by intro k; cases k; simp [statementBranch, statementCfg,
        stmtMaxPushes])
  unfold compiledStatementBranch
  exact h.trans (by
    congr 1)

private def statementPeek : _root_.Turing.TM2.Stmt
    StatementTestMachine.Γ StatementTestMachine.Λ StatementTestMachine.σ :=
  peek () (fun _ head => head.getD false) halt

private def statementPop : _root_.Turing.TM2.Stmt
    StatementTestMachine.Γ StatementTestMachine.Λ StatementTestMachine.σ :=
  pop () (fun _ head => head.getD false) halt

-- Peek and pop both update state from the exact old head; pop alone removes it.
example :
    let compiled := compileStmt StatementTestMachine 1 statementPool.builder
      statementPool.pool statementAllocation.wires statementSourceValid
      statementPeek (statementSupport statementPeek)
    evalBundle compiled.builder (statementInputs false [true] (by simp))
      compiled.wires compiled.valid =
        some { statementCfg false [true] with l := none, var := true } := by
  dsimp only
  have h := compileStmt_evalBundle StatementTestMachine 1 statementPool.builder
      statementPool.pool (statementInputs false [true] (by simp))
      statementAllocation.wires statementSourceValid statementPeek
      (statementSupport statementPeek)
      (statementDecoded false [true] (by simp))
      (by intro k; cases k; simp [statementPeek, statementCfg,
        stmtMaxPushes])
  exact h.trans (by
    congr 1)

example :
    let compiled := compileStmt StatementTestMachine 1 statementPool.builder
      statementPool.pool statementAllocation.wires statementSourceValid
      statementPop (statementSupport statementPop)
    evalBundle compiled.builder (statementInputs false [true] (by simp))
      compiled.wires compiled.valid =
        some { statementCfg false [] with l := none, var := true } := by
  dsimp only
  have h := compileStmt_evalBundle StatementTestMachine 1 statementPool.builder
      statementPool.pool (statementInputs false [true] (by simp))
      statementAllocation.wires statementSourceValid statementPop
      (statementSupport statementPop)
      (statementDecoded false [true] (by simp))
      (by intro k; cases k; simp [statementPop, statementCfg,
        stmtMaxPushes])
  exact h.trans (by
    congr 1)

private def statementZeroLayout : CfgInputLayout StatementTestMachine 0 := ⟨0⟩

private noncomputable def statementZeroBase : CircuitBuilder :=
  CircuitBuilder.empty statementZeroLayout.finish

private noncomputable def statementZeroAllocation :
    CfgInputAllocation statementZeroBase statementZeroLayout :=
  allocateCfgInputs statementZeroBase statementZeroLayout (Nat.le_refl _)

private noncomputable def statementZeroPool :=
  CircuitBuilder.allocateBoolWirePool statementZeroAllocation.builder

private theorem statementZeroValid :
    statementZeroAllocation.wires.ValidIn statementZeroPool.builder :=
  statementZeroAllocation.valid.mono statementZeroPool.extension

private noncomputable def statementZeroInputs (state : Bool) : Nat → Bool :=
  statementZeroLayout.writeCfgBits (fun _ => false)
    (encodeRawCfgBits (encodeCfg StatementTestMachine
      (statementCfgAlphabet state []) (fun k => by cases k; simp [statementCfg])))

private theorem statementZeroDecoded (state : Bool) :
    evalBundle statementZeroPool.builder (statementZeroInputs state)
      statementZeroAllocation.wires statementZeroValid =
        some (statementCfg state []) := by
  rw [evalBundle_extends statementZeroPool.extension
    (statementZeroInputs state) statementZeroAllocation.wires
    statementZeroAllocation.valid]
  exact statementZeroAllocation.evalBundle_write_encodeCfg (fun _ => false)
    (statementCfgAlphabet state []) (fun k => by cases k; simp [statementCfg])

-- At height zero the same bridge identifies the pool-backed `none` head,
-- with no synthetic wires or hand-written evaluation function.
example :
    ∃ head : SupportedHead StatementTestMachine (),
      ((statementCfg false []).stk ()).head? = head.map Subtype.val ∧
        evalHeadBits statementZeroPool.builder (statementZeroInputs false)
            (peekCfgWires () statementZeroPool.pool
              statementZeroAllocation.wires) =
          encodeHeadBits head :=
  peekCfgWires_head_eq_encode_of_evalBundle statementZeroPool.builder
    statementZeroPool.pool (statementZeroInputs false)
    statementZeroAllocation.wires statementZeroValid
    (statementZeroDecoded false) ()

private def statementEmptyPeek : _root_.Turing.TM2.Stmt
    StatementTestMachine.Γ StatementTestMachine.Λ StatementTestMachine.σ :=
  peek () (fun _ head => head.isNone) halt

private def statementLoad : _root_.Turing.TM2.Stmt
    StatementTestMachine.Γ StatementTestMachine.Λ StatementTestMachine.σ :=
  load (!·) halt

-- Height zero peeks the pool-backed empty head and updates state from `none`.
example :
    let compiled := compileStmt StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool statementZeroAllocation.wires statementZeroValid
      statementEmptyPeek (statementSupport statementEmptyPeek)
    evalBundle compiled.builder (statementZeroInputs false) compiled.wires
      compiled.valid = some { statementCfg false [] with l := none, var := true } := by
  dsimp only
  have h := compileStmt_evalBundle StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool (statementZeroInputs false)
      statementZeroAllocation.wires statementZeroValid statementEmptyPeek
      (statementSupport statementEmptyPeek) (statementZeroDecoded false)
      (by intro k; cases k; simp [statementEmptyPeek, statementCfg,
        stmtMaxPushes])
  exact h.trans (by
    congr 1)

-- Load is a finite state-map followed by recursive continuation compilation.
example :
    let compiled := compileStmt StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool statementZeroAllocation.wires statementZeroValid
      statementLoad (statementSupport statementLoad)
    evalBundle compiled.builder (statementZeroInputs false) compiled.wires
      compiled.valid = some { statementCfg false [] with l := none, var := true } := by
  dsimp only
  have h := compileStmt_evalBundle StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool (statementZeroInputs false)
      statementZeroAllocation.wires statementZeroValid statementLoad
      (statementSupport statementLoad) (statementZeroDecoded false)
      (by intro k; cases k; simp [statementLoad, statementCfg,
        stmtMaxPushes])
  exact h.trans (by
    congr 1)

-- Static halt and state-dependent goto both synchronize label and halted status
-- on actual allocated height-zero rows.
example :
    let q := goto (fun _ : Bool => true)
    let compiled := compileStmt StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool statementZeroAllocation.wires statementZeroValid q
      (statementSupport q)
    evalBundle compiled.builder (statementZeroInputs false) compiled.wires
      compiled.valid = some { statementCfg false [] with l := some true } := by
  dsimp only
  have h := compileStmt_evalBundle StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool (statementZeroInputs false)
      statementZeroAllocation.wires statementZeroValid
      (goto (fun _ : Bool => true)) (statementSupport _)
      (statementZeroDecoded false)
      (by intro k; cases k; simp [statementCfg, stmtMaxPushes])
  exact h.trans (by
    congr 1)

example :
    let compiled := compileStmt StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool statementZeroAllocation.wires statementZeroValid halt
      (statementSupport halt)
    evalBundle compiled.builder (statementZeroInputs false) compiled.wires
      compiled.valid = some { statementCfg false [] with l := none } := by
  dsimp only
  have h := compileStmt_evalBundle StatementTestMachine 0 statementZeroPool.builder
      statementZeroPool.pool (statementZeroInputs false)
      statementZeroAllocation.wires statementZeroValid halt
      (statementSupport halt) (statementZeroDecoded false)
      (by intro k; cases k; simp [statementCfg, stmtMaxPushes])
  exact h.trans (by
    congr 1)

#print axioms decodeCfg_encodeCfg
#print axioms encodeCfg_decodeCfg
#print axioms evalsToInTime_iff_stutter_accepts
#print axioms stack_length_iterate_le
#print axioms CircuitBuilder.muxFin_gate_delta
#print axioms CircuitBuilder.muxFin_eval
#print axioms CircuitBuilder.eqFin_gate_delta
#print axioms CircuitBuilder.eqFin_eval_iff
#print axioms CircuitBuilder.allocateBoolWirePool_gate_delta
#print axioms CircuitBuilder.allocateBoolWirePool_false_eval
#print axioms CircuitBuilder.allocateBoolWirePool_true_eval
#print axioms cfgMux_gate_delta
#print axioms cfgMux_eval
#print axioms cfgEq_gate_delta
#print axioms cfgEq_eval_iff
#print axioms evalBundle_eq_some_canonical
#print axioms evalBundle_replaceState
#print axioms evalBundle_replaceStatus
#print axioms validCfgCircuit_gate_delta
#print axioms validCfgCircuit_eval_iff
#print axioms validCfgCircuit_accepts_encodeCfg
#print axioms validCfgGateCost_le
#print axioms validCfgCircuit_gate_count_le
#print axioms validCfgCircuit_finish_wellFormed
#print axioms widenCfg_gate_delta
#print axioms widenCfg_decode_preserved
#print axioms narrowCfg_gate_delta
#print axioms narrowCfg_fit_iff
#print axioms narrowCfg_decode_preserved
#print axioms peekCfgWires_head_eq_encode_of_evalBundle
#print axioms compileStmt_gate_delta
#print axioms compileStmt_evalBundle
#print axioms compileStmt_gate_count_le
#print axioms compileStmt_proof_irrel
#print axioms dispatchLabels_gate_delta
#print axioms dispatchLabels_evalBundle
#print axioms dispatchGateCost_le
#print axioms dispatchLabels_gate_count_le
#print axioms transitionCircuit_gate_delta
#print axioms transitionCircuit_eval_iff
#print axioms transitionCircuit_sound
#print axioms transitionCircuitGateCost_le
#print axioms transitionCircuit_gate_count_le
#print axioms transitionCircuit_finish_wellFormed
#print axioms freshTransitionCircuitAt_complete_nat
#print axioms freshTransitionCircuit_complete
#print axioms freshTransitionCircuit_sound
#print axioms staticCfgWires_eval
#print axioms initialCfgCircuit_gate_delta
#print axioms initialCfgCircuit_eval_iff
#print axioms acceptingOutputCircuit_gate_delta
#print axioms acceptingOutputCircuit_eval_iff
#print axioms symbolicInitialCfgCircuit_gate_delta
#print axioms symbolicInitialCfgCircuit_eval_iff

end CLRS.Chapter34.Turing.CookLevin
