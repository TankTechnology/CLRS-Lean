import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.FiniteFamily

/-!
# CLRS Section 34.4 - Structured tableau bundle combinators

Cook--Levin transition circuits manipulate whole bounded configuration rows
and individual stacks within those rows.  This module exposes the corresponding
typed bundle operations before introducing any transition-specific workspace
or validity circuit.

Main results:

- Definitions {lit}`StackBundle`, {lit}`CfgBundle.stack`, and
  {lit}`CfgBundle.replaceStack`: a dependent stack view and a zero-gate,
  type-safe functional stack replacement with same-stack and frame laws.
- Definition {lit}`cfgMux`: whole-row selection through one canonical
  {lit}`cfgSlotEquivFin` flattening, with exact cost
  {lit}`3 * cfgBitCount tm H + 1`.
- Definition {lit}`cfgEq`: streaming whole-row equality through the same
  canonical flattening, with exact cost {lit}`6 * cfgBitCount tm H + 1`.

Layer boundary:

- Symbolic push, pop, and stack-top transformations belong to the downstream
  stack-primitive layer.
- Recursive statement compilation is supplied by downstream
  {lit}`StatementCircuits`, while {lit}`TransitionCircuits` supplies finite-label
  dispatch and one-step local correctness.  Fresh row allocation and exact
  boundary constraints, polynomial bounds, and verified whole-tableau assembly
  are supplied by downstream circuitization modules.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Typed stack views and replacement -/

/-- The row coordinates belonging to one selected stack.

The stack index remains in the type, so cell symbols use precisely the finite
reachable alphabet associated with that stack. -/
@[ext]
structure StackBundle (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K)
    (α : Type) where
  /-- The one-hot height coordinates of the selected stack. -/
  height : Fin (H + 1) → α
  /-- The one-hot symbol coordinates of each physical stack cell. -/
  cell : Fin H → Fin ((reachableAlphabet tm k).card + 1) → α

attribute [nolint docBlameThm] StackBundle.ext StackBundle.ext_iff

/-- Internal circuit wires belonging to one selected stack. -/
abbrev StackWires (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) :=
  StackBundle tm H k CircuitBuilder.Wire

/-- Evaluated Boolean values belonging to one selected stack. -/
abbrev StackBits (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) :=
  StackBundle tm H k Bool

namespace CfgBundle

/-- Project one dependently indexed stack from a complete row bundle. -/
def stack {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (k : tm.K) : StackBundle tm H k α where
  height := bundle.stackHeight k
  cell := bundle.stackCell k

/-- Functionally replace one stack in a row bundle.

This operation allocates no circuit gates.  Equality elimination is confined
to the branch proving that the encountered dependent stack index is the
selected index; no unchecked cast is used. -/
def replaceStack {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (k : tm.K)
    (replacement : StackBundle tm H k α) : CfgBundle tm H α := by
  classical
  intro slot
  rcases slot with (_ | label | state | ⟨other, coordinates⟩)
  · exact bundle (CfgSlot.halted tm H)
  · exact bundle (CfgSlot.label label)
  · exact bundle (CfgSlot.state state)
  · by_cases hindex : other = k
    · subst other
      rcases coordinates with height | cell
      · exact replacement.height height
      · exact replacement.cell cell.1 cell.2
    · exact bundle (.inr (.inr (.inr ⟨other, coordinates⟩)))

/-- Replacing a stack leaves the halted coordinate unchanged. -/
@[simp] theorem replaceStack_halted {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (k : tm.K)
    (replacement : StackBundle tm H k α) :
    (bundle.replaceStack k replacement).halted = bundle.halted := by
  simp [replaceStack, halted, CfgSlot.halted]

/-- Replacing a stack leaves every label coordinate unchanged. -/
@[simp] theorem replaceStack_label {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (k : tm.K)
    (replacement : StackBundle tm H k α) (i : Fin (labelCount tm + 1)) :
    (bundle.replaceStack k replacement).label i = bundle.label i := by
  simp [replaceStack, label, CfgSlot.label]

/-- Replacing a stack leaves every state coordinate unchanged. -/
@[simp] theorem replaceStack_state {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (k : tm.K)
    (replacement : StackBundle tm H k α) (i : Fin (stateCount tm)) :
    (bundle.replaceStack k replacement).state i = bundle.state i := by
  simp [replaceStack, state, CfgSlot.state]

/-- Projecting the replaced stack recovers the replacement exactly. -/
@[simp] theorem replaceStack_stack_same {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (k : tm.K)
    (replacement : StackBundle tm H k α) :
    (bundle.replaceStack k replacement).stack k = replacement := by
  ext
  · simp [stack, replaceStack, stackHeight, CfgSlot.stackHeight]
  · simp [stack, replaceStack, stackCell, CfgSlot.stackCell]

/-- Projecting any different stack after replacement recovers its old view. -/
theorem replaceStack_stack_other {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (k other : tm.K)
    (replacement : StackBundle tm H k α) (hother : other ≠ k) :
    (bundle.replaceStack k replacement).stack other = bundle.stack other := by
  ext
  · simp [stack, replaceStack, stackHeight, CfgSlot.stackHeight, hother]
  · simp [stack, replaceStack, stackCell, CfgSlot.stackCell, hother]

end CfgBundle

/-! ## Whole-row multiplexer -/

/-- Proof-carrying result of selecting one of two complete row bundles. -/
structure CfgMuxResult {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H) where
  /-- Builder after the whole-row multiplexer. -/
  builder : CircuitBuilder
  /-- Selected output wire at every named row coordinate. -/
  wires : CfgWires tm H
  /-- The result preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every output row wire belongs to the result builder. -/
  valid : wires.ValidIn builder
  /-- One shared selector negation and three gates per row bit are emitted. -/
  gate_delta : builder.gates.length =
    base.gates.length + (3 * cfgBitCount tm H + 1)
  /-- The complete evaluated row is selected by the original selector. -/
  eval : ∀ inputs, evalCfgBits builder inputs wires =
    if base.evalWire inputs selector then
      evalCfgBits base inputs whenTrue
    else
      evalCfgBits base inputs whenFalse

/-- Select one of two complete row bundles using the canonical finite
numbering of row slots and one shared selector negation. -/
def cfgMux {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base) :
    CfgMuxResult base selector whenTrue whenFalse := by
  let slots := cfgSlotEquivFin tm H
  let finite := CircuitBuilder.muxFin base selector
    (fun i => whenTrue (slots.symm i)) (fun i => whenFalse (slots.symm i))
    hselector (fun i => htrue (slots.symm i)) (fun i => hfalse (slots.symm i))
  let wires : CfgWires tm H := fun slot => finite.wires (slots slot)
  refine
    { builder := finite.builder
      wires := wires
      extension := finite.extension
      valid := fun slot => finite.valid (slots slot)
      gate_delta := finite.gate_delta
      eval := ?_ }
  intro inputs
  funext slot
  simp only [evalCfgBits, wires, ite_apply]
  rw [finite.eval]
  simp only [Equiv.symm_apply_apply]

/-- Whole-row selection preserves the complete input prefix. -/
theorem cfgMux_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base) :
    base.Extends (cfgMux base selector whenTrue whenFalse
      hselector htrue hfalse).builder :=
  (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).extension

/-- Every whole-row multiplexer output is valid in its result builder. -/
theorem cfgMux_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base) :
    (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).wires.ValidIn
      (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).builder :=
  (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).valid

/-- Whole-row selection emits exactly three gates per row bit plus one shared
selector negation. -/
theorem cfgMux_gate_delta {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base) :
    (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).builder.gates.length =
      base.gates.length + (3 * cfgBitCount tm H + 1) :=
  (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).gate_delta

/-- Exact global wire number of every whole-row multiplexer output. -/
theorem cfgMux_wire_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base)
    (slot : CfgSlot tm H) :
    (cfgMux base selector whenTrue whenFalse
      hselector htrue hfalse).wires slot =
      base.gates.length + 3 + 3 * (cfgSlotEquivFin tm H slot).val := by
  unfold cfgMux
  dsimp only
  rw [CircuitBuilder.muxFin_wire_eq]

/-- Whole-row selection appends the exact canonical finite-slot gate trace. -/
theorem cfgMux_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base) :
    (cfgMux base selector whenTrue whenFalse
      hselector htrue hfalse).builder.gates =
      base.gates ++ CircuitBuilder.muxFinGateTrace base.gates.length selector
        (fun i => whenTrue ((cfgSlotEquivFin tm H).symm i))
        (fun i => whenFalse ((cfgSlotEquivFin tm H).symm i)) := by
  simpa [cfgMux] using CircuitBuilder.muxFin_gates_eq base selector
    (fun i => whenTrue ((cfgSlotEquivFin tm H).symm i))
    (fun i => whenFalse ((cfgSlotEquivFin tm H).symm i)) hselector
    (fun i => htrue ((cfgSlotEquivFin tm H).symm i))
    (fun i => hfalse ((cfgSlotEquivFin tm H).symm i))

/-- The evaluated whole-row multiplexer returns exactly the selected arm. -/
theorem cfgMux_eval {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector : base.WireValid selector)
    (htrue : whenTrue.ValidIn base) (hfalse : whenFalse.ValidIn base)
    (inputs : Nat → Bool) :
    evalCfgBits (cfgMux base selector whenTrue whenFalse
        hselector htrue hfalse).builder inputs
        (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).wires =
      if base.evalWire inputs selector then
        evalCfgBits base inputs whenTrue
      else
        evalCfgBits base inputs whenFalse :=
  (cfgMux base selector whenTrue whenFalse hselector htrue hfalse).eval inputs

/-- Whole-row selection is independent of validity-proof choices. -/
theorem cfgMux_proof_irrel {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (selector : CircuitBuilder.Wire)
    (whenTrue whenFalse : CfgWires tm H)
    (hselector₁ hselector₂ : base.WireValid selector)
    (htrue₁ htrue₂ : whenTrue.ValidIn base)
    (hfalse₁ hfalse₂ : whenFalse.ValidIn base) :
    cfgMux base selector whenTrue whenFalse hselector₁ htrue₁ hfalse₁ =
      cfgMux base selector whenTrue whenFalse hselector₂ htrue₂ hfalse₂ := by
  rfl

/-! ## Whole-row equality -/

/-- Proof-carrying result of comparing two complete row bundles. -/
structure CfgEqResult {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H) where
  /-- Builder after the streaming row equality circuit. -/
  builder : CircuitBuilder
  /-- Output wire asserting equality of every row coordinate. -/
  wire : CircuitBuilder.Wire
  /-- The result preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- The equality output belongs to the result builder. -/
  valid : builder.WireValid wire
  /-- One true seed and six gates per row bit are emitted. -/
  gate_delta : builder.gates.length =
    base.gates.length + (6 * cfgBitCount tm H + 1)
  /-- The output is true exactly when both evaluated rows are equal. -/
  eval : ∀ inputs, builder.evalWire inputs wire = true ↔
    evalCfgBits base inputs left = evalCfgBits base inputs right

/-- Compare two complete row bundles using the canonical finite numbering of
row slots and the streaming finite-family equality kernel. -/
def cfgEq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    CfgEqResult base left right := by
  let slots := cfgSlotEquivFin tm H
  let finite := CircuitBuilder.eqFin base
    (fun i => left (slots.symm i)) (fun i => right (slots.symm i))
    (fun i => hleft (slots.symm i)) (fun i => hright (slots.symm i))
  refine
    { builder := finite.builder
      wire := finite.wire
      extension := finite.extension
      valid := finite.valid
      gate_delta := finite.gate_delta
      eval := ?_ }
  intro inputs
  rw [finite.eval]
  constructor
  · intro hall
    funext slot
    have hslot := hall (slots slot)
    simpa only [evalCfgBits, Equiv.symm_apply_apply] using hslot
  · intro heq i
    have hslot := congrFun heq (slots.symm i)
    simpa only [evalCfgBits, Equiv.apply_symm_apply] using hslot

/-- Whole-row equality preserves the complete input prefix. -/
theorem cfgEq_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    base.Extends (cfgEq base left right hleft hright).builder :=
  (cfgEq base left right hleft hright).extension

/-- The whole-row equality output is valid in its result builder. -/
theorem cfgEq_wireValid {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    (cfgEq base left right hleft hright).builder.WireValid
      (cfgEq base left right hleft hright).wire :=
  (cfgEq base left right hleft hright).valid

/-- Whole-row equality emits exactly six gates per row bit plus one true seed. -/
theorem cfgEq_gate_delta {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    (cfgEq base left right hleft hright).builder.gates.length =
      base.gates.length + (6 * cfgBitCount tm H + 1) :=
  (cfgEq base left right hleft hright).gate_delta

/-- Whole-row equality appends the exact canonical finite-slot gate trace. -/
theorem cfgEq_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    (cfgEq base left right hleft hright).builder.gates =
      base.gates ++ (CircuitBuilder.eqFinGateTrace base.gates.length
        (fun i => left ((cfgSlotEquivFin tm H).symm i))
        (fun i => right ((cfgSlotEquivFin tm H).symm i))).gates := by
  simpa [cfgEq] using CircuitBuilder.eqFin_gates_eq base
    (fun i => left ((cfgSlotEquivFin tm H).symm i))
    (fun i => right ((cfgSlotEquivFin tm H).symm i))
    (fun i => hleft ((cfgSlotEquivFin tm H).symm i))
    (fun i => hright ((cfgSlotEquivFin tm H).symm i))

/-- Whole-row equality returns the aggregate wire named by the exact trace. -/
theorem cfgEq_wire_eq_trace {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    (cfgEq base left right hleft hright).wire =
      (CircuitBuilder.eqFinGateTrace base.gates.length
        (fun i => left ((cfgSlotEquivFin tm H).symm i))
        (fun i => right ((cfgSlotEquivFin tm H).symm i))).wire := by
  simpa [cfgEq] using CircuitBuilder.eqFin_wire_eq_trace base
    (fun i => left ((cfgSlotEquivFin tm H).symm i))
    (fun i => right ((cfgSlotEquivFin tm H).symm i))
    (fun i => hleft ((cfgSlotEquivFin tm H).symm i))
    (fun i => hright ((cfgSlotEquivFin tm H).symm i))

/-- The whole-row equality output is true exactly when both evaluated row
functions are equal. -/
theorem cfgEq_eval_iff {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base)
    (inputs : Nat → Bool) :
    (cfgEq base left right hleft hright).builder.evalWire inputs
        (cfgEq base left right hleft hright).wire = true ↔
      evalCfgBits base inputs left = evalCfgBits base inputs right :=
  (cfgEq base left right hleft hright).eval inputs

/-- Whole-row equality is independent of validity-proof choices. -/
theorem cfgEq_proof_irrel {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft₁ hleft₂ : left.ValidIn base)
    (hright₁ hright₂ : right.ValidIn base) :
    cfgEq base left right hleft₁ hright₁ =
      cfgEq base left right hleft₂ hright₂ := by
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
