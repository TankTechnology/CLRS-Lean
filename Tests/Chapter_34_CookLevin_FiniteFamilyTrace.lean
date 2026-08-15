import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BundleCombinators

open CLRS.Chapter34.Turing.CookLevin

namespace CLRS.Chapter34.Turing.CookLevin.FiniteFamilyTraceTest

open CircuitBuilder

#check muxFinBodyGateTrace
#check muxFinGateTrace
#check muxFinBodyGateTrace_length
#check muxFinGateTrace_length
#check muxFin_gates_eq

#check EqFinGateTrace
#check eqFinBodyGateTrace
#check eqFinGateTrace
#check eqFinBodyGateTrace_length
#check eqFinGateTrace_length
#check eqFin_gates_eq
#check eqFin_wire_eq_trace

#check cfgMux_gates_eq
#check cfgEq_gates_eq
#check cfgEq_wire_eq_trace

/-- The trace order is frozen on a two-coordinate multiplexer. -/
example : muxFinGateTrace 10 3 (n := 2)
    (fun i => if i.val = 0 then 4 else 5)
    (fun i => if i.val = 0 then 6 else 7) =
    [.not 3,
      .and 3 4, .and 10 6, .or 11 12,
      .and 3 5, .and 10 7, .or 14 15] := by
  decide

/-- Equality is deliberately interleaved: each XNOR is followed immediately
by the aggregate AND that consumes it. -/
example : (eqFinGateTrace 10 (n := 2)
    (fun i => if i.val = 0 then 1 else 2)
    (fun i => if i.val = 0 then 3 else 4)).gates =
    [.const true,
      .not 1, .not 3, .and 1 3, .and 11 12, .or 13 14, .and 10 15,
      .not 2, .not 4, .and 2 4, .and 17 18, .or 19 20, .and 16 21] := by
  decide

#print axioms muxFin_gates_eq
#print axioms eqFin_gates_eq
#print axioms eqFin_wire_eq_trace
#print axioms cfgMux_gates_eq
#print axioms cfgEq_gates_eq
#print axioms cfgEq_wire_eq_trace

end CLRS.Chapter34.Turing.CookLevin.FiniteFamilyTraceTest
