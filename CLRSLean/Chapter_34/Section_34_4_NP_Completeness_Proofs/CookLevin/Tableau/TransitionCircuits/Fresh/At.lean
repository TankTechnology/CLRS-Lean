import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Core

/-!
# CLRS Section 34.4 - Offset-parametric fresh transitions

This module is the reusable tableau-facing form of fresh local allocation.  It
starts from an arbitrary append-only builder and an arbitrary external-input
offset, allocates two consecutive rows, and appends their local transition
constraint.

Main results:

- Definition {lit}`freshTransitionCircuitAt`: the offset-parametric builder.
- Theorem {lit}`freshTransitionRowsAt_wire_ne`: fresh row gates never alias.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Sequential allocation at an arbitrary offset -/

/-- Allocate the first row of a consecutive pair.  Fitting the successor row
also guarantees that the first row fits. -/
def freshCurrentAllocationAt (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    CfgInputAllocation start layout :=
  allocateCfgInputs start layout (by
    apply le_trans ?_ hfit
    simp [CfgInputLayout.next, CfgInputLayout.finish])

/-- Allocate the successor row after the first row's input gates. -/
def freshNextAllocationAt (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    CfgInputAllocation
      (freshCurrentAllocationAt tm H start layout hfit).builder layout.next :=
  allocateCfgInputs (freshCurrentAllocationAt tm H start layout hfit).builder
    layout.next (by
      change layout.next.finish ≤
        (freshCurrentAllocationAt tm H start layout hfit).builder.inputCount
      rw [(freshCurrentAllocationAt tm H start layout hfit).extension.1]
      exact hfit)

/-- Common builder containing both rows allocated at the chosen offset. -/
abbrev freshTransitionBaseAt (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) : CircuitBuilder :=
  (freshNextAllocationAt tm H start layout hfit).builder

/-- The first row remains valid after allocating its successor. -/
theorem freshCurrentValidAt (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    (freshCurrentAllocationAt tm H start layout hfit).wires.ValidIn
      (freshTransitionBaseAt tm H start layout hfit) :=
  (freshCurrentAllocationAt tm H start layout hfit).valid.mono
    (freshNextAllocationAt tm H start layout hfit).extension

/-- The two sequentially allocated row bundles use distinct internal gates. -/
theorem freshTransitionRowsAt_wire_ne
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount)
    (currentSlot nextSlot : CfgSlot tm H) :
    (freshCurrentAllocationAt tm H start layout hfit).wires currentSlot ≠
      (freshNextAllocationAt tm H start layout hfit).wires nextSlot := by
  have hcurrent :=
    (freshCurrentAllocationAt tm H start layout hfit).valid currentSlot
  change (freshCurrentAllocationAt tm H start layout hfit).wires currentSlot <
    (freshCurrentAllocationAt tm H start layout hfit).builder.gates.length at hcurrent
  rw [(freshNextAllocationAt tm H start layout hfit).wire_eq nextSlot]
  change (freshCurrentAllocationAt tm H start layout hfit).wires currentSlot ≠
    (freshCurrentAllocationAt tm H start layout hfit).builder.gates.length +
      (cfgSlotEquivFin tm H nextSlot).val
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hcurrent
    (Nat.le_add_right _ _))

/-! ## Offset-parametric transition construction -/

/-- Proof-carrying result of a fresh two-row transition at an arbitrary
external-input offset. -/
structure FreshTransitionCircuitAtResult
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H) where
  /-- Final builder after both input rows and the local transition circuit. -/
  builder : CircuitBuilder
  /-- First newly allocated row bundle. -/
  current : CfgWires tm H
  /-- Consecutive second row bundle. -/
  next : CfgWires tm H
  /-- Final local-transition constraint wire. -/
  wire : CircuitBuilder.Wire
  /-- The result preserves every gate and the input arity of {lit}`start`. -/
  extension : start.Extends builder
  /-- First row validity in the final builder. -/
  currentValid : current.ValidIn builder
  /-- Second row validity in the final builder. -/
  nextValid : next.ValidIn builder
  /-- Transition-wire validity in the final builder. -/
  wireValid : builder.WireValid wire
  /-- Exact cost of both row allocations followed by one local transition. -/
  gate_delta : builder.gates.length = start.gates.length +
    2 * cfgBitCount tm H + transitionCircuitGateCost tm H

/-- Allocate two consecutive fresh rows at {lit}`layout.base`, then constrain their
complete decoded configurations by one stuttering machine step. -/
def freshTransitionCircuitAt
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    FreshTransitionCircuitAtResult tm H start layout := by
  let current := freshCurrentAllocationAt tm H start layout hfit
  let next := freshNextAllocationAt tm H start layout hfit
  have hcurrent : current.wires.ValidIn next.builder :=
    current.valid.mono next.extension
  let transition := transitionCircuit tm H next.builder current.wires
    next.wires hcurrent next.valid
  exact
    { builder := transition.builder
      current := current.wires
      next := next.wires
      wire := transition.wire
      extension := current.extension.trans
        (next.extension.trans transition.extension)
      currentValid := hcurrent.mono transition.extension
      nextValid := next.valid.mono transition.extension
      wireValid := transition.valid
      gate_delta := by
        rw [transition.gate_delta, next.gate_delta, current.gate_delta]
        omega }

/-- Offset-parametric construction preserves external-input arity. -/
theorem freshTransitionCircuitAt_inputCount
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    (freshTransitionCircuitAt tm H start layout hfit).builder.inputCount =
      start.inputCount :=
  (freshTransitionCircuitAt tm H start layout hfit).extension.1

/-- The offset-parametric fresh circuit has the exact two-row allocation plus
local-transition gate delta. -/
theorem freshTransitionCircuitAt_gate_delta
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    (freshTransitionCircuitAt tm H start layout hfit).builder.gates.length =
      start.gates.length + 2 * cfgBitCount tm H +
        transitionCircuitGateCost tm H :=
  (freshTransitionCircuitAt tm H start layout hfit).gate_delta

/-- The generic result exposes exactly the first sequential allocation. -/
theorem freshTransitionCircuitAt_current
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    (freshTransitionCircuitAt tm H start layout hfit).current =
      (freshCurrentAllocationAt tm H start layout hfit).wires := by
  rfl

/-- The generic result exposes exactly the second sequential allocation. -/
theorem freshTransitionCircuitAt_next
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.next.Fits start.inputCount) :
    (freshTransitionCircuitAt tm H start layout hfit).next =
      (freshNextAllocationAt tm H start layout hfit).wires := by
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
