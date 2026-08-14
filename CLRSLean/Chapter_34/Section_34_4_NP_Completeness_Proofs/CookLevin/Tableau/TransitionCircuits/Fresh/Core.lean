import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Fresh.At

/-!
# CLRS Section 34.4 - Fresh local-transition allocation

This module allocates two consecutive, disjoint external-input row layouts and
then appends the verified local transition circuit.  The construction is
proof-carrying: both row bundles and the final transition wire are valid in the
returned builder.

Main results:

- Type {lit}`FreshTransitionCircuitResult`: a fresh two-row local circuit.
- Definition {lit}`freshTransitionCircuit`: consecutive allocation followed by
  the complete local transition constraint.
- Theorem {lit}`freshTransitionRows_wire_ne`: the two public rows use distinct
  internal input gates at every pair of coordinates.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Consecutive public layouts -/

/-- The first fresh public row starts at external input zero. -/
def freshCurrentLayout (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputLayout tm H :=
  ⟨0⟩

/-- The second fresh public row begins exactly after the first row. -/
def freshNextLayout (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputLayout tm H :=
  (freshCurrentLayout tm H).next

/-- External-input arity of one fresh local-transition instance. -/
def freshTransitionInputCount (tm : _root_.Turing.FinTM2) (H : Nat) : Nat :=
  (freshNextLayout tm H).finish

/-- Empty builder with room for both fresh public rows. -/
def freshTransitionStart (tm : _root_.Turing.FinTM2) (H : Nat) :
    CircuitBuilder :=
  CircuitBuilder.empty (freshTransitionInputCount tm H)

/-- The fresh current and next row intervals are disjoint. -/
theorem freshTransitionLayouts_disjoint (tm : _root_.Turing.FinTM2)
    (H : Nat) :
    (freshCurrentLayout tm H).Disjoint (freshNextLayout tm H) :=
  CfgInputLayout.next_disjoint (freshCurrentLayout tm H)

/-- Both canonical rows fit the empty two-row builder. -/
theorem freshTransitionLayouts_fit (tm : _root_.Turing.FinTM2)
    (H : Nat) :
    (freshCurrentLayout tm H).next.Fits
      (freshTransitionStart tm H).inputCount := by
  exact Nat.le_refl _

/-! ## Proof-carrying row allocations -/

/-- Allocate one input gate per coordinate of the current row. -/
def freshCurrentAllocation (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputAllocation (freshTransitionStart tm H)
      (freshCurrentLayout tm H) :=
  freshCurrentAllocationAt tm H (freshTransitionStart tm H)
    (freshCurrentLayout tm H) (freshTransitionLayouts_fit tm H)

/-- Allocate the disjoint next row after the current row's input gates. -/
def freshNextAllocation (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgInputAllocation (freshCurrentAllocation tm H).builder
      (freshNextLayout tm H) :=
  freshNextAllocationAt tm H (freshTransitionStart tm H)
    (freshCurrentLayout tm H) (freshTransitionLayouts_fit tm H)

/-- Common builder containing both freshly allocated public rows. -/
abbrev freshTransitionBase (tm : _root_.Turing.FinTM2) (H : Nat) :
    CircuitBuilder :=
  (freshNextAllocation tm H).builder

/-- The current row remains valid after allocation of the next row. -/
theorem freshCurrentValid (tm : _root_.Turing.FinTM2) (H : Nat) :
    (freshCurrentAllocation tm H).wires.ValidIn
      (freshTransitionBase tm H) :=
  (freshCurrentAllocation tm H).valid.mono
    (freshNextAllocation tm H).extension

/-- The freshly allocated next row is valid in the common builder. -/
theorem freshNextValid (tm : _root_.Turing.FinTM2) (H : Nat) :
    (freshNextAllocation tm H).wires.ValidIn
      (freshTransitionBase tm H) :=
  (freshNextAllocation tm H).valid

/-- Every current-row internal input gate differs from every next-row gate. -/
theorem freshTransitionRows_wire_ne (tm : _root_.Turing.FinTM2) (H : Nat)
    (currentSlot nextSlot : CfgSlot tm H) :
    (freshCurrentAllocation tm H).wires currentSlot ≠
      (freshNextAllocation tm H).wires nextSlot := by
  have hcurrent := (freshCurrentAllocation tm H).valid currentSlot
  change (freshCurrentAllocation tm H).wires currentSlot <
    (freshCurrentAllocation tm H).builder.gates.length at hcurrent
  rw [(freshNextAllocation tm H).wire_eq nextSlot]
  change (freshCurrentAllocation tm H).wires currentSlot ≠
    (freshCurrentAllocation tm H).builder.gates.length +
      (cfgSlotEquivFin tm H nextSlot).val
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hcurrent
    (Nat.le_add_right _ _))

/-! ## Complete fresh local circuit -/

/-- Canonical zero-offset specialization of the reusable fresh transition
result. -/
abbrev FreshTransitionCircuitResult
    (tm : _root_.Turing.FinTM2) (H : Nat) :=
  FreshTransitionCircuitAtResult tm H (freshTransitionStart tm H)
    (freshCurrentLayout tm H)

/-- Allocate two consecutive rows and append their local transition circuit. -/
def freshTransitionCircuit (tm : _root_.Turing.FinTM2) (H : Nat) :
    FreshTransitionCircuitResult tm H :=
  freshTransitionCircuitAt tm H (freshTransitionStart tm H)
    (freshCurrentLayout tm H) (freshTransitionLayouts_fit tm H)

/-- The fresh result preserves the declared two-row external-input arity. -/
theorem freshTransitionCircuit_inputCount (tm : _root_.Turing.FinTM2)
    (H : Nat) :
    (freshTransitionCircuit tm H).builder.inputCount =
      freshTransitionInputCount tm H := by
  exact (freshTransitionCircuit tm H).extension.1

/-- The canonical fresh circuit has the exact two-row allocation plus local
transition gate delta. -/
theorem freshTransitionCircuit_gate_delta (tm : _root_.Turing.FinTM2)
    (H : Nat) :
    (freshTransitionCircuit tm H).builder.gates.length =
      2 * cfgBitCount tm H + transitionCircuitGateCost tm H := by
  simpa [freshTransitionStart, CircuitBuilder.empty] using
    (freshTransitionCircuit tm H).gate_delta

/-- The fresh result's current row is the first allocated bundle. -/
theorem freshTransitionCircuit_current (tm : _root_.Turing.FinTM2)
    (H : Nat) :
    (freshTransitionCircuit tm H).current =
      (freshCurrentAllocation tm H).wires := by
  rfl

/-- The fresh result's next row is the second allocated bundle. -/
theorem freshTransitionCircuit_next (tm : _root_.Turing.FinTM2) (H : Nat) :
    (freshTransitionCircuit tm H).next =
      (freshNextAllocation tm H).wires := by
  rfl

/-- The actual current and next bundles exposed by the canonical final result
use distinct internal input gates at every pair of coordinates. -/
theorem freshTransitionCircuit_rows_wire_ne
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (currentSlot nextSlot : CfgSlot tm H) :
    (freshTransitionCircuit tm H).current currentSlot ≠
      (freshTransitionCircuit tm H).next nextSlot := by
  exact freshTransitionRowsAt_wire_ne tm H (freshTransitionStart tm H)
    (freshCurrentLayout tm H) (freshTransitionLayouts_fit tm H)
    currentSlot nextSlot

end

end CLRS.Chapter34.Turing.CookLevin
