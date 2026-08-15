import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Core
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Trace

/-!
# Exact finite-control dispatch traces

The semantic dispatch builder compiles each fixed program label and then
multiplexes that arm into the accumulated fallback row.  This module exposes
that literal recursive gate order without suffix extraction.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Ordered statement-and-mux trace for a suffix of program labels. -/
def dispatchLabelsListGateTrace (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base) :
    List tm.Λ → List CircuitGate
  | [] => []
  | label :: labels =>
      let compiled := compileStmt tm (workHeight tm H) base pool source hsource
        (tm.m label) (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      let hselector : compiled.builder.WireValid selector :=
        compiled.extension.wireValid (hsource.label _)
      let selected := cfgMux compiled.builder selector compiled.wires fallback
        hselector compiled.valid (hfallback.mono compiled.extension)
      let stepExtension := compiled.extension.trans selected.extension
      compileStmtGateTrace tm (workHeight tm H) base pool source hsource
          (tm.m label) (stmtPushSet_program_subset tm label) ++
        CircuitBuilder.muxFinGateTrace compiled.builder.gates.length selector
          (fun i => compiled.wires
            ((cfgSlotEquivFin tm (workHeight tm H)).symm i))
          (fun i => fallback
            ((cfgSlotEquivFin tm (workHeight tm H)).symm i)) ++
        dispatchLabelsListGateTrace tm H selected.builder
          (pool.mono stepExtension) source selected.wires
          (hsource.mono stepExtension) selected.valid labels

/-- Serial label dispatch appends exactly its recursive structural trace. -/
theorem dispatchLabelsList_gates_eq (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (dispatchLabelsList tm H base pool source fallback hsource hfallback
      labels).builder.gates =
      base.gates ++ dispatchLabelsListGateTrace tm H base pool source fallback
        hsource hfallback labels := by
  induction labels generalizing base source fallback with
  | nil => simp [dispatchLabelsList, dispatchLabelsListGateTrace]
  | cons label labels ih =>
      simp only [dispatchLabelsList, dispatchLabelsListGateTrace]
      rw [ih]
      rw [cfgMux_gates_eq]
      rw [compileStmt_gates_eq]
      simp only [List.append_assoc]

/-- The recursive dispatch trace has the exact structural dispatch cost. -/
theorem dispatchLabelsListGateTrace_length
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    (dispatchLabelsListGateTrace tm H base pool source fallback hsource
      hfallback labels).length = dispatchListGateCost tm H labels := by
  have hgates := congrArg List.length
    (dispatchLabelsList_gates_eq tm H base pool source fallback hsource
      hfallback labels)
  rw [(dispatchLabelsList tm H base pool source fallback hsource hfallback
    labels).gate_delta, List.length_append] at hgates
  omega

/-- Exact complete canonical-label dispatch trace. -/
def dispatchLabelsGateTrace (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) : List CircuitGate :=
  dispatchLabelsListGateTrace tm H base pool source source hvalid hvalid
    (programLabels tm)

/-- Complete finite-control dispatch appends its exact canonical trace. -/
theorem dispatchLabels_gates_eq (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (dispatchLabels tm H base pool source hvalid).builder.gates =
      base.gates ++ dispatchLabelsGateTrace tm H base pool source hvalid := by
  exact dispatchLabelsList_gates_eq tm H base pool source source hvalid hvalid
    (programLabels tm)

/-- Complete dispatch-trace length is the advertised exact cost. -/
theorem dispatchLabelsGateTrace_length
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (dispatchLabelsGateTrace tm H base pool source hvalid).length =
      dispatchGateCost tm H := by
  exact dispatchLabelsListGateTrace_length tm H base pool source source hvalid
    hvalid (programLabels tm)

end

end CLRS.Chapter34.Turing.CookLevin
