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
