import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeeds

/-!
# Arithmetic workspace widening for Cook--Levin transition seeds

Every local transition starts by appending a false/true constant pair and
embedding the current public tableau row into the fixed-machine workspace.
This module removes the proof-carrying widening builder from the generator
boundary: its constant wires and complete workspace row are explicit functions
of the transition seed's height, gate start, and public-row base.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

/-! ## Closed workspace input layout -/

/-- Pure arithmetic workspace row obtained from a public arithmetic row.
`start` is the first fresh gate of the local transition, so it is also the
false constant wire; `start + 1` is the true constant wire. -/
def arithmeticWidenedCfgWires (tm : _root_.Turing.FinTM2)
    (height start rowBase : Nat) : CfgWires tm (workHeight tm height)
  | .inl _ => (arithmeticCfgWires tm height rowBase).halted
  | .inr (.inl label) =>
      (arithmeticCfgWires tm height rowBase).label label
  | .inr (.inr (.inl state)) =>
      (arithmeticCfgWires tm height rowBase).state state
  | .inr (.inr (.inr ⟨k, .inl stackHeight⟩)) =>
      if h : stackHeight.val < height + 1 then
        (arithmeticCfgWires tm height rowBase).stackHeight k
          ⟨stackHeight.val, h⟩
      else start
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      if h : cell.val < height then
        (arithmeticCfgWires tm height rowBase).stackCell k
          ⟨cell.val, h⟩ symbol
      else if symbol.val = (reachableAlphabet tm k).card then
        start + 1
      else start

/-- Widening's false constant is the local transition's first fresh wire. -/
@[simp] theorem widenCfg_falseWire_eq
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (source : CfgWires tm height)
    (hvalid : source.ValidIn base) :
    (widenCfg base source hvalid).constants.falseWire =
      base.gates.length := by
  simp [widenCfg]

/-- Widening's true constant immediately follows its false constant. -/
@[simp] theorem widenCfg_trueWire_eq
    {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (source : CfgWires tm height)
    (hvalid : source.ValidIn base) :
    (widenCfg base source hvalid).constants.trueWire =
      base.gates.length + 1 := by
  simp [widenCfg]

/-- Widening an arithmetic public row produces exactly the closed workspace
layout.  In particular, no gate payload or proof term is needed to recover
any dispatch input wire. -/
theorem widenCfg_arithmetic_wires_eq
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    (widenCfg base (arithmeticCfgWires tm height rowBase) hvalid).wires =
      arithmeticWidenedCfgWires tm height base.gates.length rowBase := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, stackHeight | cell⟩)
  · rfl
  · rfl
  · rfl
  · simp [widenCfg, arithmeticWidenedCfgWires]
  · rcases cell with ⟨cell, symbol⟩
    simp [widenCfg, arithmeticWidenedCfgWires]

/-! ## Seed-level packaging -/

/-- Exact dispatch input recovered from one raw transition-row seed. -/
structure TransitionWideningLayout (tm : _root_.Turing.FinTM2) where
  height : Nat
  falseWire : Nat
  trueWire : Nat
  wires : CfgWires tm (workHeight tm height)

/-- Arithmetic widening layout decoded directly from a transition seed. -/
def transitionWideningLayout (tm : _root_.Turing.FinTM2)
    (seed : TransitionRowSeed) : TransitionWideningLayout tm :=
  { height := seed.height
    falseWire := seed.start
    trueWire := seed.start + 1
    wires := arithmeticWidenedCfgWires tm seed.height seed.start seed.rowBase }

/-- The corresponding observable layout of the proof-carrying widening
builder. -/
def widenCfgLayout {tm : _root_.Turing.FinTM2} {height : Nat}
    (base : CircuitBuilder) (source : CfgWires tm height)
    (hvalid : source.ValidIn base) : TransitionWideningLayout tm :=
  { height := height
    falseWire := (widenCfg base source hvalid).constants.falseWire
    trueWire := (widenCfg base source hvalid).constants.trueWire
    wires := (widenCfg base source hvalid).wires }

/-- A seed whose start is the current builder length reconstructs the complete
observable widening layout of its arithmetic tableau row. -/
theorem widenCfgLayout_arithmetic_eq_seed
    (tm : _root_.Turing.FinTM2) (height rowBase : Nat)
    (base : CircuitBuilder)
    (hvalid : (arithmeticCfgWires tm height rowBase).ValidIn base) :
    widenCfgLayout base (arithmeticCfgWires tm height rowBase) hvalid =
      transitionWideningLayout tm
        { height := height, start := base.gates.length, rowBase := rowBase } := by
  simp only [widenCfgLayout, transitionWideningLayout]
  rw [widenCfg_falseWire_eq, widenCfg_trueWire_eq,
    widenCfg_arithmetic_wires_eq]

/-- The raw-input seed compiler therefore expands to the complete arithmetic
widening layout for every adjacent row, with the same local-start progression
used by the canonical transition family. -/
theorem verifierTransitionRowSeeds_wideningLayouts_eq_ofFn
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionRowSeeds W input).map
        (transitionWideningLayout W.machine.tm) =
      List.ofFn fun row : Fin ((verifierHorizon W).eval input.length) =>
        transitionWideningLayout W.machine.tm
          { height := (verifierHeight W).eval input.length
            start :=
              (verifierTransitionStartPolynomial W).eval input.length +
                row.val * transitionCircuitGateCost W.machine.tm
                  ((verifierHeight W).eval input.length)
            rowBase := row.val * cfgBitCount W.machine.tm
              ((verifierHeight W).eval input.length) } := by
  unfold verifierTransitionRowSeeds
  rw [verifierTransitionRowSeedTriples_eq_ofFn, List.map_map,
    List.map_ofFn]
  rfl

end CLRS.Chapter34.Turing.CookLevin
