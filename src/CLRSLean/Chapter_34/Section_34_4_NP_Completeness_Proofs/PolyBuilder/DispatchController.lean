import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatementController
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Trace

/-!
# Runtime controller for finite-label Cook--Levin dispatch

The recursive statement controller already supports the finite-family mux used
after each program label.  This module packages every label arm and mux into one
continuous runtime script and proves that its emitted bytes are exactly the
semantic dispatch trace.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

open CookLevin

/-- Runtime statement/mux script for a suffix of program labels.  The script
contains only phase tags and unary wire operands; it never stores target gate
bytes. -/
def compileDispatchLabelsListScript (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base) :
    List tm.Λ → List AffineStmtPhase
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
      compileStmtScript tm (workHeight tm H) base pool source hsource
          (tm.m label) (stmtPushSet_program_subset tm label) ++
        [.mux selector
          (affineMuxFinCanonicalFrames compiled.builder.gates.length selector _
            (fun i => compiled.wires
              ((cfgSlotEquivFin tm (workHeight tm H)).symm i))
            (fun i => fallback
              ((cfgSlotEquivFin tm (workHeight tm H)).symm i)))] ++
        compileDispatchLabelsListScript tm H selected.builder
          (pool.mono stepExtension) source selected.wires
          (hsource.mono stepExtension) selected.valid labels

/-- Interpreting the runtime script gives the exact recursive semantic dispatch
trace, byte for byte and in canonical label order. -/
theorem compileDispatchLabelsListScript_gateStream_eq_trace
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base)
    (labels : List tm.Λ) :
    affineStmtScriptGateStream
        (compileDispatchLabelsListScript tm H base pool source fallback hsource
          hfallback labels) =
      (dispatchLabelsListGateTrace tm H base pool source fallback hsource
        hfallback labels).flatMap encodeCircuitGate := by
  induction labels generalizing base source fallback with
  | nil => rfl
  | cons label labels ih =>
      simp only [compileDispatchLabelsListScript,
        CookLevin.dispatchLabelsListGateTrace,
        affineStmtScriptGateStream_append,
        affineStmtScriptGateStream_cons,
        affineStmtScriptGateStream_nil,
        affineStmtPhaseGateStream,
        List.append_nil,
        List.flatMap_append]
      rw [compileStmtScript_gateStream_eq_trace]
      rw [affineMuxFinCanonicalGateStream_eq_trace]
      rw [ih]

/-- Complete canonical-label dispatch script. -/
def compileDispatchScript (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) : List AffineStmtPhase :=
  compileDispatchLabelsListScript tm H base pool source source hvalid hvalid
    (programLabels tm)

/-- The complete script agrees exactly with the canonical-label dispatch trace. -/
theorem compileDispatchScript_gateStream_eq_trace
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    affineStmtScriptGateStream
        (compileDispatchScript tm H base pool source hvalid) =
      (dispatchLabelsGateTrace tm H base pool source hvalid).flatMap
        encodeCircuitGate := by
  exact compileDispatchLabelsListScript_gateStream_eq_trace tm H base pool
    source source hvalid hvalid (programLabels tm)

/-- One fixed controller executes the complete finite-label dispatch without an
intermediate halt and emits exactly the semantic dispatch bytes. -/
def compileDispatchScript_run
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) (output : List CircuitSym) :
    EvalsToInTime (step affineStmtRevProgram)
      (affineStmtLoopCfg
        (encodeAffineStmtControllerInput
          (compileDispatchScript tm H base pool source hvalid)) output)
      (some (haltCfg affineStmtRevProgram
        (((dispatchLabelsGateTrace tm H base pool source hvalid).flatMap
          encodeCircuitGate).reverse ++ output)))
      (affineStmtScriptRunSteps
        (compileDispatchScript tm H base pool source hvalid)) := by
  simpa [compileDispatchScript_gateStream_eq_trace] using
    affineStmt_run (compileDispatchScript tm H base pool source hvalid) output

/-- Dispatch inherits the controller's uniform linear runtime bound in its
exact unary encoding. -/
theorem compileDispatchScript_steps_le
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    affineStmtScriptRunSteps
        (compileDispatchScript tm H base pool source hvalid) ≤
      200 * (encodeAffineStmtControllerInput
        (compileDispatchScript tm H base pool source hvalid)).length + 4 :=
  affineStmtScriptRun_steps_le _

end CLRS.Chapter34.Turing.PolyBuilder
