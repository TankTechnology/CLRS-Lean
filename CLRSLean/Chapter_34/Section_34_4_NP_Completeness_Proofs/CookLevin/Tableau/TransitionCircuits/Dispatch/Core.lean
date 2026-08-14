import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Workspace
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.StatementCircuits.Core

/-!
# CLRS Section 34.4 - Finite-control transition dispatch

This module compiles every program label of one fixed bundled TM2 machine.
Each arm starts from the same workspace row, while builders and the shared
Boolean pool move monotonically through the finite label list.  A whole-row
multiplexer selects each compiled arm from the source label one-hot code.

Main results:

- Definition {lit}`dispatchLabels`: finite label dispatch without enumerating
  configurations or stacks.
- Definition {lit}`dispatchGateCost`: exact structural gate recurrence.
- Theorem {lit}`dispatchLabels_proof_irrel`: the emitted circuit is independent
  of validity-proof choices.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Canonical finite label order and cost -/

/-- Every machine label exactly once, in the canonical finite-code order. -/
def programLabels (tm : _root_.Turing.FinTM2) : List tm.Λ :=
  List.ofFn fun code : Fin (labelCount tm) => (labelEquivFin tm).symm code

/-- Exact gate cost of compiling and selecting a finite list of label arms. -/
def dispatchListGateCost (tm : _root_.Turing.FinTM2) (H : Nat) :
    List tm.Λ → Nat
  | [] => 0
  | label :: labels =>
      compileStmtGateCost tm (workHeight tm H) (tm.m label) +
        (3 * cfgBitCount tm (workHeight tm H) + 1) +
        dispatchListGateCost tm H labels

/-- Exact gate cost of complete finite-control dispatch. -/
def dispatchGateCost (tm : _root_.Turing.FinTM2) (H : Nat) : Nat :=
  dispatchListGateCost tm H (programLabels tm)

/-! ## Proof-carrying serial dispatch -/

/-- Proof-carrying result of compiling a finite suffix of label arms.

{lit}`source` is the unchanged workspace row read by every statement compiler;
{lit}`fallback` is the accumulated selected row from earlier labels. -/
structure DispatchListResult (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (source fallback : CfgWires tm (workHeight tm H))
    (labels : List tm.Λ) where
  /-- Builder after every listed statement compiler and whole-row mux. -/
  builder : CircuitBuilder
  /-- Accumulated complete workspace row. -/
  wires : CfgWires tm (workHeight tm H)
  /-- Dispatch preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every selected row wire belongs to the result builder. -/
  valid : wires.ValidIn builder
  /-- Dispatch emits exactly the structural list recurrence. -/
  gate_delta : builder.gates.length =
    base.gates.length + dispatchListGateCost tm H labels

/-- Compile and select a finite list of labels serially.

The recursive call receives the same {lit}`source` wires transported to the current
builder and the newly selected row as its fallback. -/
def dispatchLabelsList (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source fallback : CfgWires tm (workHeight tm H))
    (hsource : source.ValidIn base) (hfallback : fallback.ValidIn base) :
    (labels : List tm.Λ) → DispatchListResult tm H base source fallback labels
  | [] =>
      { builder := base
        wires := fallback
        extension := .refl base
        valid := hfallback
        gate_delta := by simp [dispatchListGateCost] }
  | label :: labels => by
      let compiled := compileStmt tm (workHeight tm H) base pool source hsource
        (tm.m label) (stmtPushSet_program_subset tm label)
      let selector := source.label (Fin.castSucc (labelEquivFin tm label))
      have hselector : compiled.builder.WireValid selector :=
        compiled.extension.wireValid (hsource.label _)
      let selected := cfgMux compiled.builder selector compiled.wires fallback
        hselector compiled.valid (hfallback.mono compiled.extension)
      let stepExtension := compiled.extension.trans selected.extension
      let rest := dispatchLabelsList tm H selected.builder
        (pool.mono stepExtension) source selected.wires
        (hsource.mono stepExtension) selected.valid labels
      refine
        { builder := rest.builder
          wires := rest.wires
          extension := stepExtension.trans rest.extension
          valid := rest.valid
          gate_delta := ?_ }
      rw [rest.gate_delta, selected.gate_delta, compiled.gate_delta]
      simp only [dispatchListGateCost]
      omega

/-- Complete finite-control dispatch result, starting from the source row as
the reserved-{lit}`none` fallback. -/
abbrev DispatchResult (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H)) :=
  DispatchListResult tm H base source source (programLabels tm)

/-- Compile every finite program label and select one complete workspace row.

The starting fallback is {lit}`source`, so the reserved halted label stutters
without a special selector arm. -/
def dispatchLabels (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) : DispatchResult tm H base source :=
  dispatchLabelsList tm H base pool source source hvalid hvalid
    (programLabels tm)

/-! ## Public structural wrappers -/

/-- Complete dispatch preserves the complete input builder prefix. -/
theorem dispatchLabels_extends (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    base.Extends (dispatchLabels tm H base pool source hvalid).builder :=
  (dispatchLabels tm H base pool source hvalid).extension

/-- Every complete dispatch output wire belongs to its result builder. -/
theorem dispatchLabels_valid (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (dispatchLabels tm H base pool source hvalid).wires.ValidIn
      (dispatchLabels tm H base pool source hvalid).builder :=
  (dispatchLabels tm H base pool source hvalid).valid

/-- Complete dispatch has the exact finite-label structural gate delta. -/
theorem dispatchLabels_gate_delta (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (dispatchLabels tm H base pool source hvalid).builder.gates.length =
      base.gates.length + dispatchGateCost tm H :=
  (dispatchLabels tm H base pool source hvalid).gate_delta

/-- Serial finite-label dispatch is independent of source-validity proofs. -/
theorem dispatchLabels_proof_irrel (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (source : CfgWires tm (workHeight tm H))
    (hvalid₁ hvalid₂ : source.ValidIn base) :
    dispatchLabels tm H base pool source hvalid₁ =
      dispatchLabels tm H base pool source hvalid₂ := by
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
