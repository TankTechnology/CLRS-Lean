import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.ConstantPool

/-!
# CLRS Section 34.4 - One-step Cook--Levin workspace bridges

A logical row of height {lit}`H` needs enough temporary room for every push in one
bundled TM2 statement.  This module bridges that row with height
{lit}`H + maxPushesPerStep tm`.  Widening appends two shared constants; narrowing
reuses the old prefix and builds a fit bit from the overflow height flags.

The fit bit alone is not a canonicality certificate: discarded workspace
cells may be malformed.  Decode-preservation theorems therefore state their
successful-decode premises explicitly.

Main results:

- Definition {lit}`workHeight`: the public row height plus the exact uniform
  per-step push headroom.
- Definitions {lit}`widenCfg` and {lit}`narrowCfg`: proof-carrying circuit
  bridges with exact gate deltas and evaluation theorems.
- Theorems {lit}`widenCfg_decode_preserved` and
  {lit}`narrowCfg_decode_preserved`: successful machine decoding is preserved
  across the public/workspace boundary, with an explicit fit premise when
  narrowing.

Current gaps:

- Symbolic push, pop, peek, equality, and mux operations are provided by the
  downstream stack-primitive layer.
- Recursive statement compilation is provided by downstream
  {lit}`StatementCircuits`, and {lit}`TransitionCircuits` now consumes this
  bridge in the complete local step check.  Non-aliasing row allocation and
  verified whole-tableau assembly remain milestone 8F.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Workspace height sufficient for every push in one bundled step. -/
def workHeight (tm : _root_.Turing.FinTM2) (H : Nat) : Nat :=
  H + maxPushesPerStep tm

/-! ## Pure bit bridges -/

/-- Preserve the logical row, reject extra heights, and fill extra cells with
the distinguished blank symbol. -/
def widenCfgBits {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) : CfgBits tm (workHeight tm H)
  | .inl _ => bits.halted
  | .inr (.inl label) => bits.label label
  | .inr (.inr (.inl state)) => bits.state state
  | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
      if h : height.val < H + 1 then
        bits.stackHeight k ⟨height.val, h⟩
      else false
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      if h : cell.val < H then
        bits.stackCell k ⟨cell.val, h⟩ symbol
      else if symbol.val = (reachableAlphabet tm k).card then true else false

/-- Project the logical prefix from a workspace row. -/
def narrowCfgBits {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm (workHeight tm H)) : CfgBits tm H
  | .inl _ => bits.halted
  | .inr (.inl label) => bits.label label
  | .inr (.inr (.inl state)) => bits.state state
  | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
      bits.stackHeight k ⟨height.val, by simp only [workHeight]; omega⟩
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      bits.stackCell k ⟨cell.val, by simp only [workHeight]; omega⟩ symbol

namespace CfgBits

/-- No stack selects one of the {lean}`maxPushesPerStep tm` height coordinates
strictly above the old bound {lit}`H`. -/
def FitsHeight {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm (workHeight tm H)) : Prop :=
  ∀ k (offset : Fin (maxPushesPerStep tm)),
    bits.stackHeight k
      ⟨H + 1 + offset.val, by simp only [workHeight]; omega⟩ = false

end CfgBits

/-- Narrowing a widened row recovers every original bit. -/
@[simp] theorem narrowCfgBits_widenCfgBits
    {tm : _root_.Turing.FinTM2} {H : Nat} (bits : CfgBits tm H) :
    narrowCfgBits (widenCfgBits bits) = bits := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · rfl
  · rfl
  · rfl
  · simp [narrowCfgBits, widenCfgBits]
    omega
  · rcases cell with ⟨cell, symbol⟩
    simp [narrowCfgBits, widenCfgBits]

/-- Widening never selects an overflow height. -/
theorem widenCfgBits_fitsHeight
    {tm : _root_.Turing.FinTM2} {H : Nat} (bits : CfgBits tm H) :
    (widenCfgBits bits).FitsHeight := by
  intro k offset
  simp only [CfgBundle.stackHeight_apply, widenCfgBits]
  rw [dif_neg]
  omega

/-! ## Constant-cost widening -/

/-- Proof-carrying widening result. -/
structure WidenCfgResult {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H) where
  /-- Builder after allocating the two shared Boolean constants. -/
  builder : CircuitBuilder
  /-- Shared false/true constants available to downstream row operations. -/
  constants : CircuitBuilder.BoolWirePool builder
  /-- Workspace-height row wires. -/
  wires : CfgWires tm (workHeight tm H)
  /-- The result builder preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every widened row wire belongs to the result builder. -/
  valid : wires.ValidIn builder
  /-- Widening always emits exactly one false and one true gate. -/
  gate_delta : builder.gates.length = base.gates.length + 2
  /-- Evaluation agrees exactly with the pure widening operation. -/
  eval : ∀ inputs,
    evalCfgBits builder inputs wires =
      widenCfgBits (evalCfgBits base inputs source)

/-- Widen using one shared false wire and one shared true wire.  The same two
gates are emitted when the machine's maximum push count is zero. -/
def widenCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) : WidenCfgResult base source := by
  let allocation := CircuitBuilder.allocateBoolWirePool base
  let wires : CfgWires tm (workHeight tm H) := fun slot =>
    match slot with
    | .inl _ => source.halted
    | .inr (.inl label) => source.label label
    | .inr (.inr (.inl state)) => source.state state
    | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
        if h : height.val < H + 1 then
          source.stackHeight k ⟨height.val, h⟩
        else allocation.pool.falseWire
    | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
        if h : cell.val < H then
          source.stackCell k ⟨cell.val, h⟩ symbol
        else if symbol.val = (reachableAlphabet tm k).card then
          allocation.pool.trueWire
        else allocation.pool.falseWire
  refine
    { builder := allocation.builder
      constants := allocation.pool
      wires := wires
      extension := allocation.extension
      valid := ?_
      gate_delta := ?_
      eval := ?_ }
  · intro slot
    rcases slot with (_ | label | state | ⟨k, height | cell⟩)
    · exact allocation.extension.wireValid (hvalid _)
    · exact allocation.extension.wireValid (hvalid _)
    · exact allocation.extension.wireValid (hvalid _)
    · simp only [wires]
      split
      next => exact allocation.extension.wireValid (hvalid _)
      next => exact allocation.pool.falseValid
    · rcases cell with ⟨cell, symbol⟩
      simp only [wires]
      split
      next => exact allocation.extension.wireValid (hvalid _)
      next =>
        split
        next => exact allocation.pool.trueValid
        next => exact allocation.pool.falseValid
  · exact allocation.gate_delta
  · intro inputs
    funext slot
    rcases slot with (_ | label | state | ⟨k, height | cell⟩)
    · exact allocation.extension.evalWire_eq inputs (hvalid _)
    · exact allocation.extension.evalWire_eq inputs (hvalid _)
    · exact allocation.extension.evalWire_eq inputs (hvalid _)
    · simp only [evalCfgBits, wires, widenCfgBits]
      split
      next => exact allocation.extension.evalWire_eq inputs (hvalid _)
      next => exact allocation.pool.false_eval inputs
    · rcases cell with ⟨cell, symbol⟩
      simp only [evalCfgBits, wires, widenCfgBits]
      split
      next => exact allocation.extension.evalWire_eq inputs (hvalid _)
      next =>
        split
        next => exact allocation.pool.true_eval inputs
        next => exact allocation.pool.false_eval inputs

/-- Widening preserves the complete input builder prefix. -/
theorem widenCfg_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) :
    base.Extends (widenCfg base source hvalid).builder :=
  (widenCfg base source hvalid).extension

/-- Every wire returned by widening belongs to its result builder. -/
theorem widenCfg_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) :
    (widenCfg base source hvalid).wires.ValidIn
      (widenCfg base source hvalid).builder :=
  (widenCfg base source hvalid).valid

/-- Widening emits exactly two shared constant gates. -/
theorem widenCfg_gate_delta {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) :
    (widenCfg base source hvalid).builder.gates.length =
      base.gates.length + 2 :=
  (widenCfg base source hvalid).gate_delta

/-- Circuit widening evaluates to the pure widened bit row. -/
theorem widenCfg_eval {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) (inputs : Nat → Bool) :
    evalCfgBits (widenCfg base source hvalid).builder inputs
        (widenCfg base source hvalid).wires =
      widenCfgBits (evalCfgBits base inputs source) :=
  (widenCfg base source hvalid).eval inputs

/-! ## Prefix narrowing with a fit output -/

/-- Public canonical order of every overflow-height wire inspected by
narrowing. -/
def narrowCfgOverflowWires {tm : _root_.Turing.FinTM2} {H : Nat}
    (source : CfgWires tm (workHeight tm H)) : List CircuitBuilder.Wire := by
  letI : Fintype tm.K := tm.kFin
  let M := maxPushesPerStep tm
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  exact List.ofFn fun p : Fin (Fintype.card tm.K * M) =>
    let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := M)).symm p
    source.stackHeight (keyEquiv.symm q.1)
      ⟨H + 1 + q.2.val, by simp only [M, workHeight]; omega⟩

/-- Pure false-seeded overflow disjunction followed by its fit negation. -/
structure NarrowCfgGateTrace where
  gates : List CircuitGate
  fit : CircuitBuilder.Wire

def narrowCfgGateTrace {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (source : CfgWires tm (workHeight tm H)) :
    NarrowCfgGateTrace :=
  let any := CircuitBuilder.disjunctionGateTrace start
    (narrowCfgOverflowWires source)
  { gates := any.gates ++ [.not any.wire]
    fit := start + any.gates.length }

/-- Proof-carrying narrowing result. -/
structure NarrowCfgResult {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H)) where
  /-- Builder after constructing the shared overflow-fit circuit. -/
  builder : CircuitBuilder
  /-- Public-height prefix wires reused from the workspace row. -/
  wires : CfgWires tm H
  /-- Boolean wire asserting that no overflow height is selected. -/
  fit : CircuitBuilder.Wire
  /-- The result builder preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every narrowed row wire belongs to the result builder. -/
  valid : wires.ValidIn builder
  /-- The fit output belongs to the result builder. -/
  fitValid : builder.WireValid fit
  /-- Exact cost of one flattened overflow disjunction and its negation. -/
  gate_delta : builder.gates.length = base.gates.length +
    Fintype.card tm.K * maxPushesPerStep tm + 2
  /-- Evaluation agrees exactly with pure prefix narrowing. -/
  eval : ∀ inputs,
    evalCfgBits builder inputs wires =
      narrowCfgBits (evalCfgBits base inputs source)
  /-- The fit output is true exactly when every overflow height bit is false. -/
  fit_eval : ∀ inputs, builder.evalWire inputs fit = true ↔
    (evalCfgBits base inputs source).FitsHeight

/-- Reuse the logical prefix and negate one disjunction of all overflow-height
wires.  The empty overflow list follows the same false-seed-plus-not path. -/
def narrowCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) : NarrowCfgResult base source := by
  letI : Fintype tm.K := tm.kFin
  let M := maxPushesPerStep tm
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let overflow : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * M) =>
      let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := M)).symm p
      source.stackHeight (keyEquiv.symm q.1)
        ⟨H + 1 + q.2.val, by simp only [M, workHeight]; omega⟩
  have hoverflow : ∀ wire ∈ overflow, base.WireValid wire := by
    intro wire hwire
    rw [List.mem_ofFn] at hwire
    rcases hwire with ⟨p, rfl⟩
    exact hvalid _
  let overflowAny := base.disjunction overflow hoverflow
  let hextAny := CircuitBuilder.disjunction_extends base overflow hoverflow
  have hanyValid := CircuitBuilder.disjunction_wireValid base overflow hoverflow
  let fit := overflowAny.1.not overflowAny.2 hanyValid
  let hextFit := CircuitBuilder.not_extends overflowAny.1 overflowAny.2 hanyValid
  let extension := hextAny.trans hextFit
  let wires : CfgWires tm H := fun slot =>
    match slot with
    | .inl _ => source.halted
    | .inr (.inl label) => source.label label
    | .inr (.inr (.inl state)) => source.state state
    | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
        source.stackHeight k
          ⟨height.val, by simp only [workHeight]; omega⟩
    | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
        source.stackCell k
          ⟨cell.val, by simp only [workHeight]; omega⟩ symbol
  refine
    { builder := fit.1
      wires := wires
      fit := fit.2
      extension := extension
      valid := ?_
      fitValid := CircuitBuilder.not_wireValid overflowAny.1 overflowAny.2
        hanyValid
      gate_delta := ?_
      eval := ?_
      fit_eval := ?_ }
  · intro slot
    rcases slot with (_ | label | state | ⟨k, height | cell⟩)
    · exact extension.wireValid (hvalid _)
    · exact extension.wireValid (hvalid _)
    · exact extension.wireValid (hvalid _)
    · exact extension.wireValid (hvalid _)
    · rcases cell with ⟨cell, symbol⟩
      exact extension.wireValid (hvalid _)
  · dsimp only [fit]
    rw [CircuitBuilder.not_gate_delta,
      CircuitBuilder.disjunction_gate_delta]
    simp only [overflow, List.length_ofFn, M]
  · intro inputs
    funext slot
    change fit.1.evalWire inputs (wires slot) = _
    rw [extension.evalWire_eq inputs]
    · rcases slot with (_ | label | state | ⟨k, height | cell⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rcases cell with ⟨cell, symbol⟩
        rfl
    · rcases slot with (_ | label | state | ⟨k, height | cell⟩)
      · exact hvalid _
      · exact hvalid _
      · exact hvalid _
      · exact hvalid _
      · rcases cell with ⟨cell, symbol⟩
        exact hvalid _
  · intro inputs
    dsimp only [fit]
    rw [CircuitBuilder.not_eval]
    rw [Bool.not_eq_true_eq_eq_false]
    rw [CircuitBuilder.disjunction_eval]
    rw [List.any_eq_false]
    change (∀ wire ∈ overflow, base.evalWire inputs wire ≠ true) ↔
      ∀ k (offset : Fin M),
        base.evalWire inputs
          (source.stackHeight k
            ⟨H + 1 + offset.val, by simp only [M, workHeight]; omega⟩) = false
    constructor
    · intro hall k offset
      apply Bool.eq_false_of_not_eq_true
      apply hall
      rw [List.mem_ofFn]
      let pair : Fin (Fintype.card tm.K) × Fin M := (keyEquiv k, offset)
      let p : Fin (Fintype.card tm.K * M) := finProdFinEquiv pair
      refine ⟨p, ?_⟩
      have hq :
          (finProdFinEquiv (m := Fintype.card tm.K) (n := M)).symm p =
            pair := by simp [p]
      simp only [hq, pair]
      simp
    · intro hall wire hwire
      rw [List.mem_ofFn] at hwire
      rcases hwire with ⟨p, rfl⟩
      let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := M)).symm p
      have hfalse := hall (keyEquiv.symm q.1) q.2
      simpa only [q, hfalse] using (by decide : ¬ false = true)

/-- Narrowing appends exactly the pure overflow-disjunction-plus-negation
trace. -/
theorem narrowCfg_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (narrowCfg base source hvalid).builder.gates =
      base.gates ++
        (narrowCfgGateTrace base.gates.length source).gates := by
  letI : Fintype tm.K := tm.kFin
  let M := maxPushesPerStep tm
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let overflow : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * M) =>
      let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := M)).symm p
      source.stackHeight (keyEquiv.symm q.1)
        ⟨H + 1 + q.2.val, by simp only [M, workHeight]; omega⟩
  have hoverflow : ∀ wire ∈ overflow, base.WireValid wire := by
    intro wire hwire
    rw [List.mem_ofFn] at hwire
    rcases hwire with ⟨p, rfl⟩
    exact hvalid _
  let overflowAny := base.disjunction overflow hoverflow
  have hanyValid := CircuitBuilder.disjunction_wireValid base overflow hoverflow
  change (overflowAny.1.not overflowAny.2 hanyValid).1.gates = _
  rw [CircuitBuilder.not_gates, CircuitBuilder.disjunction_gates_eq,
    CircuitBuilder.disjunction_wire_eq_trace]
  simp [narrowCfgGateTrace, narrowCfgOverflowWires, overflow, overflowAny,
    M, keyEquiv, List.append_assoc]

/-- The public fit wire is the fresh output named by the pure trace. -/
theorem narrowCfg_fit_wire_eq_trace {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (narrowCfg base source hvalid).fit =
      (narrowCfgGateTrace base.gates.length source).fit := by
  letI : Fintype tm.K := tm.kFin
  let M := maxPushesPerStep tm
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let overflow : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * M) =>
      let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := M)).symm p
      source.stackHeight (keyEquiv.symm q.1)
        ⟨H + 1 + q.2.val, by simp only [M, workHeight]; omega⟩
  have hoverflow : ∀ wire ∈ overflow, base.WireValid wire := by
    intro wire hwire
    rw [List.mem_ofFn] at hwire
    rcases hwire with ⟨p, rfl⟩
    exact hvalid _
  let overflowAny := base.disjunction overflow hoverflow
  have hanyValid := CircuitBuilder.disjunction_wireValid base overflow hoverflow
  change (overflowAny.1.not overflowAny.2 hanyValid).2 = _
  rw [CircuitBuilder.not_wire_eq, CircuitBuilder.disjunction_gates_eq]
  simp [narrowCfgGateTrace, narrowCfgOverflowWires, overflow, overflowAny,
    M, keyEquiv]

/-- Narrowing preserves the complete input builder prefix. -/
theorem narrowCfg_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    base.Extends (narrowCfg base source hvalid).builder :=
  (narrowCfg base source hvalid).extension

/-- Every row wire returned by narrowing belongs to its result builder. -/
theorem narrowCfg_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (narrowCfg base source hvalid).wires.ValidIn
      (narrowCfg base source hvalid).builder :=
  (narrowCfg base source hvalid).valid

/-- The narrowing fit output belongs to its result builder. -/
theorem narrowCfg_fit_wireValid {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (narrowCfg base source hvalid).builder.WireValid
      (narrowCfg base source hvalid).fit :=
  (narrowCfg base source hvalid).fitValid

/-- Narrowing uses one gate per overflow coordinate plus two fold gates. -/
theorem narrowCfg_gate_delta {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) :
    (narrowCfg base source hvalid).builder.gates.length =
      base.gates.length + Fintype.card tm.K * maxPushesPerStep tm + 2 :=
  (narrowCfg base source hvalid).gate_delta

/-- Circuit narrowing evaluates to the pure public-height prefix. -/
theorem narrowCfg_eval {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) (inputs : Nat → Bool) :
    evalCfgBits (narrowCfg base source hvalid).builder inputs
        (narrowCfg base source hvalid).wires =
      narrowCfgBits (evalCfgBits base inputs source) :=
  (narrowCfg base source hvalid).eval inputs

/-- The narrowing fit output is true exactly when all overflow height bits are
false. -/
theorem narrowCfg_fit_iff {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) (inputs : Nat → Bool) :
    (narrowCfg base source hvalid).builder.evalWire inputs
        (narrowCfg base source hvalid).fit = true ↔
      (evalCfgBits base inputs source).FitsHeight :=
  (narrowCfg base source hvalid).fit_eval inputs

/-! ## Widening and canonical decoding -/

/-- Widen a raw bounded code with blank physical cells. -/
private def widenRawCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) : BoundedCfg tm (workHeight tm H) where
  halted := code.halted
  label := code.label
  state := code.state
  stack k :=
    { height := ⟨(code.stack k).height.val, by simp only [workHeight]; omega⟩
      cells := fun i =>
        if hi : i.val < H then (code.stack k).cells ⟨i.val, hi⟩
        else Fin.last (reachableAlphabet tm k).card }

private theorem widenCfgBits_encodeRawCfgBits
    {tm : _root_.Turing.FinTM2} {H : Nat} (code : BoundedCfg tm H) :
    widenCfgBits (encodeRawCfgBits code) =
      encodeRawCfgBits (widenRawCfg code) := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · rfl
  · simp [widenCfgBits, encodeRawCfgBits, widenRawCfg, encodeOneHot]
  · simp [widenCfgBits, encodeRawCfgBits, widenRawCfg, encodeOneHot]
  · simp only [widenCfgBits, encodeRawCfgBits, widenRawCfg, encodeOneHot]
    split
    next hheight =>
      change decide ((⟨height.val, hheight⟩ : Fin (H + 1)) =
          (code.stack k).height) =
        decide (height = ⟨(code.stack k).height.val,
          by simp only [workHeight]; omega⟩)
      congr 1
      apply propext
      constructor <;> intro heq
      · apply Fin.ext
        simpa using congrArg Fin.val heq
      · apply Fin.ext
        simpa using congrArg Fin.val heq
    next hheight =>
      have hne : height ≠ ⟨(code.stack k).height.val,
          by simp only [workHeight]; omega⟩ := by
        intro heq
        have hval := congrArg Fin.val heq
        simp at hval
        omega
      simp [hne]
  · rcases cell with ⟨cell, symbol⟩
    simp only [widenCfgBits, encodeRawCfgBits, widenRawCfg]
    split
    next hcell => rfl
    next hcell =>
      simp only [encodeOneHot]
      split
      next hblank =>
        have heq : symbol = Fin.last (reachableAlphabet tm k).card := by
          apply Fin.ext
          simpa using hblank
        simp [heq]
      next hnonblank =>
        have hne : symbol ≠ Fin.last (reachableAlphabet tm k).card := by
          intro heq
          have hval := congrArg Fin.val heq
          simp at hval
          omega
        simp [hne]

private theorem widenRawCfg_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) (hvalid : code.Valid) :
    (widenRawCfg code).Valid := by
  constructor
  · exact hvalid.1
  · intro k i
    simp only [widenRawCfg]
    split
    next hi => simpa using hvalid.2 k ⟨i.val, hi⟩
    next hi => simp; omega

private theorem decodeCfg_widenRawCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) (hvalid : code.Valid) :
    decodeCfg tm (widenRawCfg code) (widenRawCfg_valid code hvalid) =
      decodeCfg tm code hvalid := by
  cases code with
  | mk halted label state stack =>
    simp only [decodeCfg]
    congr 1
    funext k
    simp only [decodeBoundedStack, widenRawCfg, List.ofFn_inj]
    funext i
    have hiH : i.val < H := lt_of_lt_of_le i.isLt
      (Nat.le_of_lt_succ (stack k).height.isLt)
    congr 1
    simp [BoundedStack.activeIndex, hiH]

/-- Widening preserves every successfully decoded machine configuration. -/
theorem widenCfg_decode_preserved
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm H)
    (hvalid : source.ValidIn base) (inputs : Nat → Bool) (c : tm.Cfg)
    (hdecoded : evalBundle base inputs source hvalid = some c) :
    evalBundle (widenCfg base source hvalid).builder inputs
        (widenCfg base source hvalid).wires
        (widenCfg base source hvalid).valid = some c := by
  let bits := evalCfgBits base inputs source
  unfold evalBundle evalRawBundle at hdecoded ⊢
  change (decodeRawCfg? bits).bind (decodeCfg? tm) = some c at hdecoded
  rcases hrawEq : decodeRawCfg? bits with _ | raw
  · rw [hrawEq] at hdecoded
    contradiction
  · have hbits : bits = encodeRawCfgBits raw :=
      (decodeRawCfg_eq_some_iff bits raw).mp hrawEq
    rw [hrawEq] at hdecoded
    rw [(widenCfg base source hvalid).eval]
    change (decodeRawCfg? (widenCfgBits bits)).bind (decodeCfg? tm) = some c
    rw [hbits, widenCfgBits_encodeRawCfgBits, decodeRawCfg_encode]
    simp only [Option.bind_some] at hdecoded ⊢
    unfold decodeCfg? at hdecoded ⊢
    split at hdecoded
    next hrawValid =>
      rw [dif_pos (widenRawCfg_valid raw hrawValid)]
      have hc : decodeCfg tm raw hrawValid = c := Option.some.inj hdecoded
      rw [decodeCfg_widenRawCfg raw hrawValid, hc]
    next => contradiction

/-! ## Narrowing and canonical decoding -/

/-- Project a raw workspace code whose selected stack heights fit {lit}`H`. -/
private def narrowRawCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm (workHeight tm H))
    (hfit : ∀ k, (code.stack k).height.val ≤ H) : BoundedCfg tm H where
  halted := code.halted
  label := code.label
  state := code.state
  stack k :=
    { height := ⟨(code.stack k).height.val, Nat.lt_succ_of_le (hfit k)⟩
      cells := fun i => (code.stack k).cells
        ⟨i.val, by simp only [workHeight]; omega⟩ }

private theorem narrowCfgBits_encodeRawCfgBits
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm (workHeight tm H))
    (hfit : ∀ k, (code.stack k).height.val ≤ H) :
    narrowCfgBits (encodeRawCfgBits code) =
      encodeRawCfgBits (narrowRawCfg code hfit) := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · rfl
  · rfl
  · rfl
  · change decide ((⟨height.val,
        by simp only [workHeight]; omega⟩ : Fin (workHeight tm H + 1)) =
        (code.stack k).height) =
      decide (height = ⟨(code.stack k).height.val,
        Nat.lt_succ_of_le (hfit k)⟩)
    congr 1
    apply propext
    constructor <;> intro heq
    · apply Fin.ext
      simpa using congrArg Fin.val heq
    · apply Fin.ext
      simpa using congrArg Fin.val heq
  · rcases cell with ⟨cell, symbol⟩
    rfl

private theorem narrowRawCfg_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm (workHeight tm H)) (hvalid : code.Valid)
    (hfit : ∀ k, (code.stack k).height.val ≤ H) :
    (narrowRawCfg code hfit).Valid := by
  constructor
  · exact hvalid.1
  · intro k i
    have hi : i.val < workHeight tm H := lt_of_lt_of_le i.isLt (by
      simp only [workHeight]
      omega)
    change ((code.stack k).cells ⟨i.val, hi⟩).val <
        (reachableAlphabet tm k).card ↔
      i.val < (code.stack k).height.val
    exact hvalid.2 k ⟨i.val, hi⟩

private theorem decodeCfg_narrowRawCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm (workHeight tm H)) (hvalid : code.Valid)
    (hfit : ∀ k, (code.stack k).height.val ≤ H) :
    decodeCfg tm (narrowRawCfg code hfit)
        (narrowRawCfg_valid code hvalid hfit) =
      decodeCfg tm code hvalid := by
  cases code with
  | mk halted label state stack =>
    simp only [decodeCfg]
    congr 1

/-- For a one-hot height field, rejecting every overflow coordinate is exactly
the statement that its selected height is at most {lit}`H`. -/
private theorem oneHot_overflow_false_iff_choose_le
    {H M : Nat} (bits : Fin (H + M + 1) → Bool) (hone : OneHot bits) :
    (∀ offset : Fin M, bits ⟨H + 1 + offset.val, by omega⟩ = false) ↔
      hone.choose.val ≤ H := by
  constructor
  · intro hall
    by_contra hnot
    have hM : 0 < M := by
      have := hone.choose.isLt
      omega
    let offset : Fin M := ⟨hone.choose.val - H - 1, by omega⟩
    have heq : (⟨H + 1 + offset.val, by omega⟩ : Fin (H + M + 1)) =
        hone.choose := by
      apply Fin.ext
      simp [offset]
      omega
    have := hall offset
    rw [heq, hone.choose_spec.1] at this
    contradiction
  · intro hle offset
    apply Bool.eq_false_of_not_eq_true
    intro htrue
    have heq := hone.choose_spec.2 _ htrue
    have hval := congrArg Fin.val heq
    simp at hval
    omega

/-- Under raw one-hot decodability, the fit output is equivalent to every
decoded raw stack height being at most {lit}`H`. -/
theorem narrowCfg_fit_iff_height_le
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) (inputs : Nat → Bool)
    (hraw : (evalCfgBits base inputs source).RawDecodable) :
    (narrowCfg base source hvalid).builder.evalWire inputs
        (narrowCfg base source hvalid).fit = true ↔
      ∀ k, ((rawCfgOf (evalCfgBits base inputs source) hraw).stack k).height.val ≤ H := by
  rw [(narrowCfg base source hvalid).fit_eval]
  constructor
  · intro hall k
    exact (oneHot_overflow_false_iff_choose_le _ (hraw.stackHeight k)).mp
      (hall k)
  · intro hall k
    exact (oneHot_overflow_false_iff_choose_le _ (hraw.stackHeight k)).mpr
      (hall k)

/-- A successfully decoded workspace row remains the same machine
configuration after narrowing, provided the fit output is true.  Both premises
are necessary: fit alone does not validate discarded physical cells. -/
theorem narrowCfg_decode_preserved
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm H))
    (hvalid : source.ValidIn base) (inputs : Nat → Bool) (c : tm.Cfg)
    (hdecoded : evalBundle base inputs source hvalid = some c)
    (hfitOutput :
      (narrowCfg base source hvalid).builder.evalWire inputs
        (narrowCfg base source hvalid).fit = true) :
    evalBundle (narrowCfg base source hvalid).builder inputs
        (narrowCfg base source hvalid).wires
        (narrowCfg base source hvalid).valid = some c := by
  let bits := evalCfgBits base inputs source
  have hoverflow :=
    ((narrowCfg base source hvalid).fit_eval inputs).mp hfitOutput
  unfold evalBundle evalRawBundle at hdecoded ⊢
  change (decodeRawCfg? bits).bind (decodeCfg? tm) = some c at hdecoded
  rcases hrawEq : decodeRawCfg? bits with _ | raw
  · rw [hrawEq] at hdecoded
    contradiction
  · have hbits : bits = encodeRawCfgBits raw :=
      (decodeRawCfg_eq_some_iff bits raw).mp hrawEq
    have hfitRaw : ∀ k, (raw.stack k).height.val ≤ H := by
      intro k
      by_contra hnot
      have hM : 0 < maxPushesPerStep tm := by
        have := (raw.stack k).height.isLt
        simp only [workHeight] at this
        omega
      let offset : Fin (maxPushesPerStep tm) :=
        ⟨(raw.stack k).height.val - H - 1, by
          have := (raw.stack k).height.isLt
          simp only [workHeight] at this
          omega⟩
      have hoff := hoverflow k offset
      change bits.stackHeight k
          ⟨H + 1 + offset.val, by simp only [workHeight]; omega⟩ = false at hoff
      rw [hbits] at hoff
      change encodeOneHot (raw.stack k).height
          ⟨H + 1 + offset.val, by simp only [workHeight]; omega⟩ = false at hoff
      have heq :
          (⟨H + 1 + offset.val,
            by simp only [workHeight]; omega⟩ : Fin (workHeight tm H + 1)) =
            (raw.stack k).height := by
        apply Fin.ext
        simp [offset]
        omega
      simp [encodeOneHot, heq] at hoff
    rw [(narrowCfg base source hvalid).eval]
    change (decodeRawCfg? (narrowCfgBits bits)).bind (decodeCfg? tm) = some c
    rw [hbits, narrowCfgBits_encodeRawCfgBits raw hfitRaw]
    rw [decodeRawCfg_encode]
    simp only [Option.bind_some] at hdecoded ⊢
    rw [hrawEq] at hdecoded
    simp only [Option.bind_some] at hdecoded
    unfold decodeCfg? at hdecoded ⊢
    split at hdecoded
    next hrawValid =>
      rw [dif_pos (narrowRawCfg_valid raw hrawValid hfitRaw)]
      have hc : decodeCfg tm raw hrawValid = c := Option.some.inj hdecoded
      rw [decodeCfg_narrowRawCfg raw hrawValid hfitRaw, hc]
    next => contradiction

end

end CLRS.Chapter34.Turing.CookLevin
