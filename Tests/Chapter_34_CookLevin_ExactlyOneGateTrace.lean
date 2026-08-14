import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau

open CLRS Chapter34
open CLRS.Chapter34.Turing
open CLRS.Chapter34.Turing.CookLevin

#check CircuitBuilder.input_gates
#check CircuitBuilder.not_gates
#check CircuitBuilder.and_gates
#check CircuitBuilder.or_gates
#check CircuitBuilder.BoolEqGateTrace
#check CircuitBuilder.boolEqGateTrace
#check CircuitBuilder.boolEqGateTrace_length
#check CircuitBuilder.eq_gates_eq
#check CircuitBuilder.eq_wire_eq_trace
#check CircuitBuilder.ConjunctionGateTrace
#check CircuitBuilder.conjunctionGateTrace
#check CircuitBuilder.conjunctionGateTrace_length
#check CircuitBuilder.conjunction_gates_eq
#check CircuitBuilder.conjunction_wire_eq_trace
#check ExactlyOneGateTrace
#check exactlyOneGateTrace
#check exactlyOneGateTrace_length
#check exactlyOne_gates_eq
#check exactlyOne_wire_eq_trace
#check SuffixOrGateTrace
#check suffixOrGateTrace
#check suffixOrGateTrace_length
#check activeMask_gates_eq
#check activeMask_carry_eq_trace
#check activeMask_output_eq_trace

example :
    (exactlyOneGateTrace 7 []).gates =
      [.const false, .const false, .not 8, .and 7 9] := by
  native_decide

example :
    CircuitBuilder.conjunctionGateTrace 7 [2, 3] =
      { gates := [.const true, .and 3 7, .and 2 8]
        wire := 9 } := by
  native_decide

example :
    CircuitBuilder.boolEqGateTrace 7 2 4 =
      { gates := [.not 2, .not 4, .and 2 4, .and 7 8, .or 9 10]
        wire := 11 } := by
  native_decide

example :
    (suffixOrGateTrace 7 [2, 3]).gates =
      [.const false, .or 7 3, .or 8 2] ∧
    (suffixOrGateTrace 7 [2, 3]).carry = 9 ∧
    (suffixOrGateTrace 7 [2, 3]).outputs 0 = 9 ∧
    (suffixOrGateTrace 7 [2, 3]).outputs 1 = 8 := by
  native_decide

example :
    (exactlyOneGateTrace 7 [2]).gates =
      [.const false, .const false,
       .and 7 2, .or 8 9, .or 7 2,
       .not 10, .and 11 12] := by
  native_decide

#print axioms exactlyOne_gates_eq
#print axioms exactlyOne_wire_eq_trace
#print axioms CircuitBuilder.eq_gates_eq
#print axioms CircuitBuilder.conjunction_gates_eq
#print axioms activeMask_gates_eq
#print axioms activeMask_output_eq_trace
