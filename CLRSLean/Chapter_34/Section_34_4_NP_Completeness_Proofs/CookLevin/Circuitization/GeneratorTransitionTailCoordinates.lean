import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeeds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.TransitionScript

/-!
# Closed phase coordinates for Cook--Levin transition scripts

The row seed fixes the public height and the first gate index of one local
transition circuit.  This file proves that the complete post-dispatch phase
layout is then arithmetic: narrowing carries, equality carries, and the final
conjunction operands have closed formulas independent of proof terms and of
the preceding gate contents.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Closed phase boundaries -/

/-- First gate of the overflow-narrowing phase. -/
def transitionNarrowStart (tm : _root_.Turing.FinTM2)
    (height start : Nat) : Nat :=
  start + 2 + dispatchGateCost tm height

/-- First gate of the complete public-row equality phase. -/
def transitionEqStart (tm : _root_.Turing.FinTM2)
    (height start : Nat) : Nat :=
  transitionNarrowStart tm height start +
    Fintype.card tm.K * maxPushesPerStep tm + 2

/-- Output of the false-seeded overflow disjunction. -/
def transitionNarrowSourceWire (tm : _root_.Turing.FinTM2)
    (height start : Nat) : Nat :=
  transitionNarrowStart tm height start +
    Fintype.card tm.K * maxPushesPerStep tm

/-- Output of the negated overflow disjunction. -/
def transitionFitWire (tm : _root_.Turing.FinTM2)
    (height start : Nat) : Nat :=
  transitionNarrowSourceWire tm height start + 1

/-- Output of the complete public-row equality. -/
def transitionEqWire (tm : _root_.Turing.FinTM2)
    (height start : Nat) : Nat :=
  transitionEqStart tm height start + 6 * cfgBitCount tm height

/-- Exact final conjunction frame of one local transition script. -/
def transitionFinalAndFrame (tm : _root_.Turing.FinTM2)
    (height start : Nat) : AffineAndFinPairFrame :=
  { right := transitionEqWire tm height start
    left := transitionFitWire tm height start }

/-! ## Generic canonical-frame arithmetic -/

private theorem disjunctionGateTrace_wire_eq (start : Nat) :
    ∀ wires : List CircuitBuilder.Wire,
      (CircuitBuilder.disjunctionGateTrace start wires).wire =
        start + wires.length := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [CircuitBuilder.disjunctionGateTrace,
        CircuitBuilder.disjunctionGateTrace_length]

private theorem affineOrFinCanonicalFrames_length (start : Nat) :
    ∀ wires : List CircuitBuilder.Wire,
      (affineOrFinCanonicalFrames start wires).length = wires.length := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [affineOrFinCanonicalFrames, ih]

private theorem affineOrFinCanonicalFrames_rights (start : Nat) :
    ∀ wires : List CircuitBuilder.Wire,
      (affineOrFinCanonicalFrames start wires).map
          (fun frame => frame.right) =
        (List.range wires.length).map (fun offset => start + offset) := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp only [affineOrFinCanonicalFrames, List.map_append,
        List.map_singleton, List.length_cons]
      rw [ih, disjunctionGateTrace_wire_eq]
      rw [List.range_succ]
      simp

private theorem affineOrFinCanonicalFrames_lefts (start : Nat) :
    ∀ wires : List CircuitBuilder.Wire,
      (affineOrFinCanonicalFrames start wires).map
          (fun frame => frame.left) = wires.reverse := by
  intro wires
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [affineOrFinCanonicalFrames, ih]

private theorem affineEqFinCanonicalFrames_length (start : Nat) :
    ∀ (n : Nat) (left right : Fin n → CircuitBuilder.Wire),
      (affineEqFinCanonicalFrames start n left right).length = n := by
  intro n
  induction n with
  | zero =>
      intro left right
      rfl
  | succ n ih =>
      intro left right
      simp [affineEqFinCanonicalFrames, ih]

private theorem affineEqFinCanonicalFrames_coordinates (start : Nat) :
    ∀ (n : Nat) (left right : Fin n → CircuitBuilder.Wire),
      (affineEqFinCanonicalFrames start n left right).map
          (fun frame => (frame.eqStart, frame.matched, frame.previous)) =
        List.ofFn fun coordinate : Fin n =>
          (start + 1 + 6 * coordinate.val,
            start + 5 + 6 * coordinate.val,
            start + 6 * coordinate.val) := by
  intro n
  induction n with
  | zero =>
      intro left right
      rfl
  | succ n ih =>
      intro left right
      simp only [affineEqFinCanonicalFrames, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1

private theorem affineEqFinCanonicalFrames_rights (start : Nat) :
    ∀ (n : Nat) (left right : Fin n → CircuitBuilder.Wire),
      (affineEqFinCanonicalFrames start n left right).map
          (fun frame => frame.right) =
        List.ofFn right := by
  intro n
  induction n with
  | zero =>
      intro left right
      rfl
  | succ n ih =>
      intro left right
      simp only [affineEqFinCanonicalFrames, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

private theorem affineEqFinCanonicalFrames_lefts (start : Nat) :
    ∀ (n : Nat) (left right : Fin n → CircuitBuilder.Wire),
      (affineEqFinCanonicalFrames start n left right).map
          (fun frame => frame.left) =
        List.ofFn left := by
  intro n
  induction n with
  | zero =>
      intro left right
      rfl
  | succ n ih =>
      intro left right
      simp only [affineEqFinCanonicalFrames, List.map_append,
        List.map_singleton]
      rw [ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

private theorem eqFinGateTrace_wire_eq (start : Nat) :
    ∀ (n : Nat) (left right : Fin n → CircuitBuilder.Wire),
      (CircuitBuilder.eqFinGateTrace start left right).wire =
        start + 6 * n := by
  intro n
  cases n with
  | zero =>
      intro left right
      rfl
  | succ n =>
      intro left right
      unfold CircuitBuilder.eqFinGateTrace
      simp only [CircuitBuilder.eqFinBodyGateTrace]
      rw [CircuitBuilder.eqFinBodyGateTrace_length,
        CircuitBuilder.boolEqGateTrace_length]
      ring

/-! ## The fixed public projection of a dispatched workspace row -/

/-- Pure wire-level projection from a workspace row back to public height.
Unlike `narrowCfg`, this definition records only the reused row wires and
does not construct the overflow-fit gates. -/
def narrowCfgWireProjection {tm : _root_.Turing.FinTM2} {height : Nat}
    (source : CfgWires tm (workHeight tm height)) : CfgWires tm height
  | .inl _ => source.halted
  | .inr (.inl label) => source.label label
  | .inr (.inr (.inl state)) => source.state state
  | .inr (.inr (.inr ⟨k, .inl stackHeight⟩)) =>
      source.stackHeight k
        ⟨stackHeight.val, by simp only [workHeight]; omega⟩
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      source.stackCell k
        ⟨cell.val, by simp only [workHeight]; omega⟩ symbol

/-- The proof-carrying narrowing builder reuses exactly the pure projected
workspace wires. -/
theorem narrowCfg_wires_eq_projection
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (source : CfgWires tm (workHeight tm height))
    (hvalid : source.ValidIn base) :
    (narrowCfg base source hvalid).wires =
      narrowCfgWireProjection source := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, stackHeight | cell⟩)
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases cell with ⟨cell, symbol⟩
    rfl

/-! ## Canonical transition-script projections -/

/-- Narrowing has one OR frame per fixed-machine overflow-height coordinate. -/
@[simp] theorem compileTransitionScript_narrowFrames_length
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).narrowFrames.length =
      Fintype.card tm.K * maxPushesPerStep tm := by
  letI : Fintype tm.K := tm.kFin
  simp only [compileTransitionScript]
  unfold affineNarrowCfgFrames
  rw [affineOrFinCanonicalFrames_length]
  simp [narrowCfgOverflowWires]

/-- The narrowing carry operands are consecutive fresh wires starting at the
false seed of that phase. -/
theorem compileTransitionScript_narrowFrameRights
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).narrowFrames.map
        (fun frame => frame.right) =
      (List.range (Fintype.card tm.K * maxPushesPerStep tm)).map
        (fun offset => transitionNarrowStart tm height
          base.gates.length + offset) := by
  letI : Fintype tm.K := tm.kFin
  simp only [compileTransitionScript]
  unfold affineNarrowCfgFrames
  rw [affineOrFinCanonicalFrames_rights]
  rw [show (narrowCfgOverflowWires
      (dispatchLabels tm height
        (widenCfg base current hcurrent).builder
        (widenCfg base current hcurrent).constants
        (widenCfg base current hcurrent).wires
        (widenCfg base current hcurrent).valid).wires).length =
      Fintype.card tm.K * maxPushesPerStep tm by
    simp [narrowCfgOverflowWires]]
  rw [dispatchLabels_gate_delta, widenCfg_gate_delta]
  rfl

/-- Narrowing reads the overflow coordinates of the dispatched workspace row
in the tail-first order used by the canonical disjunction trace. -/
theorem compileTransitionScript_narrowFrameLefts
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).narrowFrames.map
        (fun frame => frame.left) =
      (narrowCfgOverflowWires
        (dispatchLabels tm height
          (widenCfg base current hcurrent).builder
          (widenCfg base current hcurrent).constants
          (widenCfg base current hcurrent).wires
          (widenCfg base current hcurrent).valid).wires).reverse := by
  simp only [compileTransitionScript]
  unfold affineNarrowCfgFrames
  rw [affineOrFinCanonicalFrames_lefts]

/-- The stored narrowing source is the final OR carry. -/
@[simp] theorem compileTransitionScript_narrowSource_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).narrowSource =
      transitionNarrowSourceWire tm height base.gates.length := by
  letI : Fintype tm.K := tm.kFin
  simp only [compileTransitionScript]
  rw [disjunctionGateTrace_wire_eq]
  rw [dispatchLabels_gate_delta, widenCfg_gate_delta]
  simp [narrowCfgOverflowWires, transitionNarrowSourceWire,
    transitionNarrowStart]

/-- Equality has one frame per public tableau-row bit. -/
@[simp] theorem compileTransitionScript_eqFrames_length
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).eqFrames.length =
      cfgBitCount tm height := by
  simp only [compileTransitionScript]
  rw [affineEqFinCanonicalFrames_length]

/-- Every equality frame's three fresh-wire coordinates have a closed affine
formula from the local transition start. -/
theorem compileTransitionScript_eqFrameCoordinates
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).eqFrames.map
          (fun frame => (frame.eqStart, frame.matched, frame.previous)) =
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        (transitionEqStart tm height base.gates.length + 1 +
            6 * coordinate.val,
          transitionEqStart tm height base.gates.length + 5 +
            6 * coordinate.val,
          transitionEqStart tm height base.gates.length +
            6 * coordinate.val) := by
  letI : Fintype tm.K := tm.kFin
  simp only [compileTransitionScript]
  rw [affineEqFinCanonicalFrames_coordinates]
  rw [narrowCfg_gate_delta, dispatchLabels_gate_delta,
    widenCfg_gate_delta]
  rfl

/-- Equality compares against the actual next-row wires in canonical finite
slot order; these are the source operands not covered by the fresh skeleton. -/
theorem compileTransitionScript_eqFrameRights
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).eqFrames.map
        (fun frame => frame.right) =
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        next ((cfgSlotEquivFin tm height).symm coordinate) := by
  simp only [compileTransitionScript]
  rw [affineEqFinCanonicalFrames_rights]

/-- Equality's left operands are the fixed public-height projection of the
same dispatched workspace row consumed by narrowing. -/
theorem compileTransitionScript_eqFrameLefts
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).eqFrames.map
        (fun frame => frame.left) =
      List.ofFn fun coordinate : Fin (cfgBitCount tm height) =>
        narrowCfgWireProjection
          (dispatchLabels tm height
            (widenCfg base current hcurrent).builder
            (widenCfg base current hcurrent).constants
            (widenCfg base current hcurrent).wires
            (widenCfg base current hcurrent).valid).wires
          ((cfgSlotEquivFin tm height).symm coordinate) := by
  simp only [compileTransitionScript]
  rw [affineEqFinCanonicalFrames_lefts]
  rw [narrowCfg_wires_eq_projection]

/-- The final local-transition conjunction consumes exactly the public-row
equality output and the overflow-fit output. -/
@[simp] theorem compileTransitionScript_finalAnd_eq
    (tm : _root_.Turing.FinTM2) (height : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm height)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (compileTransitionScript tm height base current next hcurrent hnext).finalAnd =
      transitionFinalAndFrame tm height base.gates.length := by
  letI : Fintype tm.K := tm.kFin
  simp only [compileTransitionScript]
  rw [AffineAndFinPairFrame.mk.injEq]
  constructor
  · rw [narrowCfg_fit_wire_eq_trace]
    simp [narrowCfgGateTrace, CircuitBuilder.disjunctionGateTrace_length,
      narrowCfgOverflowWires, transitionFinalAndFrame, transitionFitWire,
      transitionNarrowSourceWire, transitionNarrowStart]
    rw [dispatchLabels_gate_delta, widenCfg_gate_delta]
    rfl
  · rw [cfgEq_wire_eq_trace, eqFinGateTrace_wire_eq]
    rw [narrowCfg_gate_delta, dispatchLabels_gate_delta,
      widenCfg_gate_delta]
    rfl

end CLRS.Chapter34.Turing.CookLevin
