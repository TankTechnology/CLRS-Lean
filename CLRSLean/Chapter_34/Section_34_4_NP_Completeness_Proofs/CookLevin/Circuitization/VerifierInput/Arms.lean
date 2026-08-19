import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.VerifierInput.Semantics.Helpers

/-!
# Polynomial verifier-input length arms

This internal construction prebuilds one separator-negation wire per physical
cell, builds one shape arm per certificate length, and never enumerates
certificate contents.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-- Gates emitted by the arm for the selected certificate length. -/
def verifierInputArmGateCost (H inputLength length : Nat) : Nat :=
  if length + 1 + inputLength ≤ H then length + inputLength + 3 else 0

namespace VerifierInput

structure SeparatorNotsResult {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} (base : CircuitBuilder) (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) where
  builder : CircuitBuilder
  wires : Fin H → CircuitBuilder.Wire
  extension : base.Extends builder
  valid : ∀ cell, builder.WireValid (wires cell)
  eval : ∀ inputs cell, builder.evalWire inputs (wires cell) =
    !(base.evalWire inputs
      (stack.cell ⟨cell.val, by omega⟩ separator))
  gate_delta : builder.gates.length = base.gates.length + H

private structure SeparatorNotsPrefix {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} (base : CircuitBuilder) (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1))
    (n : Nat) (hn : n ≤ H) where
  builder : CircuitBuilder
  wires : Fin n → CircuitBuilder.Wire
  extension : base.Extends builder
  valid : ∀ cell, builder.WireValid (wires cell)
  eval : ∀ inputs cell, builder.evalWire inputs (wires cell) =
    !(base.evalWire inputs
      (stack.cell ⟨cell.val, by omega⟩ separator))
  gate_delta : builder.gates.length = base.gates.length + n

private def buildSeparatorNotsPrefix {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} (base : CircuitBuilder) (stack : StackWires tm H k)
    (hstack : stack.ValidIn base)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) :
    (n : Nat) → (hn : n ≤ H) →
      SeparatorNotsPrefix base stack separator n hn
  | 0, _ =>
      { builder := base
        wires := Fin.elim0
        extension := .refl base
        valid := fun cell => Fin.elim0 cell
        eval := fun _ cell => Fin.elim0 cell
        gate_delta := by simp }
  | n + 1, hn => by
      let previous := buildSeparatorNotsPrefix base stack hstack separator n
        (by omega)
      let cell : Fin H := ⟨n, by omega⟩
      have hcell := previous.extension.wireValid (hstack.cell cell separator)
      let output := previous.builder.not (stack.cell cell separator) hcell
      let hext := CircuitBuilder.not_extends previous.builder
        (stack.cell cell separator) hcell
      let wires : Fin (n + 1) → CircuitBuilder.Wire := fun i =>
        if hi : i.val < n then previous.wires ⟨i.val, hi⟩ else output.2
      exact
        { builder := output.1
          wires := wires
          extension := previous.extension.trans hext
          valid := by
            intro i
            simp only [wires]
            split
            next hi => exact hext.wireValid (previous.valid ⟨i.val, hi⟩)
            next => exact CircuitBuilder.not_wireValid _ _ _
          eval := by
            intro inputs i
            simp only [wires]
            split
            next hi =>
              rw [hext.evalWire_eq inputs (previous.valid ⟨i.val, hi⟩),
                previous.eval]
            next hi =>
              have hiEq : i.val = n := by omega
              dsimp only [output]
              rw [CircuitBuilder.not_eval,
                previous.extension.evalWire_eq inputs (hstack.cell cell separator)]
              congr 3
              exact Fin.ext hiEq.symm
          gate_delta := by
            rw [CircuitBuilder.not_gate_delta, previous.gate_delta]
            omega }

def buildSeparatorNots {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} (base : CircuitBuilder) (stack : StackWires tm H k)
    (hstack : stack.ValidIn base)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) :
    SeparatorNotsResult base stack separator := by
  let result := buildSeparatorNotsPrefix base stack hstack separator H
    (Nat.le_refl H)
  exact { result with }

private def separatorNotsPrefixGateTrace
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1))
    : (n : Nat) → (hn : n ≤ H) → List CircuitGate
  | 0, _ => []
  | n + 1, hn =>
      separatorNotsPrefixGateTrace stack separator n (by omega) ++
        [.not (stack.cell ⟨n, by omega⟩ separator)]

/-- Literal ordered NOT trace for every physical separator cell. -/
def separatorNotsGateTrace {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) :
    List CircuitGate :=
  separatorNotsPrefixGateTrace stack separator H (Nat.le_refl H)

/-- Runtime source operands for the separator-negation phase, in the exact
physical-cell order used by the semantic builder. -/
def separatorNotSources {tm : _root_.Turing.FinTM2} {H : Nat}
    {k : tm.K} (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) : List Nat :=
  List.ofFn fun cell : Fin H => stack.cell cell separator

private theorem separatorNotsPrefixGateTrace_eq_sources
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) :
    ∀ (n : Nat) (hn : n ≤ H),
      separatorNotsPrefixGateTrace stack separator n hn =
        (List.ofFn fun cell : Fin n =>
          CircuitGate.not (stack.cell ⟨cell.val, by omega⟩ separator)) := by
  intro n hn
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [separatorNotsPrefixGateTrace]
      rw [ih]
      rw [List.ofFn_succ']
      simp [List.concat_eq_append]

/-- The public separator trace is exactly the map of `not` over its runtime
source operands. -/
theorem separatorNotsGateTrace_eq_sources
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (stack : StackWires tm H k)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) :
    separatorNotsGateTrace stack separator =
      (separatorNotSources stack separator).map CircuitGate.not := by
  unfold separatorNotsGateTrace
  rw [separatorNotsPrefixGateTrace_eq_sources]
  simp [separatorNotSources, Function.comp_def]

private theorem buildSeparatorNotsPrefix_gates_eq
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (base : CircuitBuilder) (stack : StackWires tm H k)
    (hstack : stack.ValidIn base)
    (separator : Fin ((reachableAlphabet tm k).card + 1))
    (n : Nat) (hn : n ≤ H) :
    (buildSeparatorNotsPrefix base stack hstack separator n hn).builder.gates =
      base.gates ++ separatorNotsPrefixGateTrace stack separator n hn := by
  induction n with
  | zero => simp [buildSeparatorNotsPrefix, separatorNotsPrefixGateTrace]
  | succ n ih =>
      simp only [buildSeparatorNotsPrefix]
      rw [CircuitBuilder.not_gates]
      rw [ih]
      simp [separatorNotsPrefixGateTrace, List.append_assoc]

/-- The proof-carrying separator builder appends exactly the literal NOT
trace. -/
theorem buildSeparatorNots_gates_eq
    {tm : _root_.Turing.FinTM2} {H : Nat} {k : tm.K}
    (base : CircuitBuilder) (stack : StackWires tm H k)
    (hstack : stack.ValidIn base)
    (separator : Fin ((reachableAlphabet tm k).card + 1)) :
    (buildSeparatorNots base stack hstack separator).builder.gates =
      base.gates ++ separatorNotsGateTrace stack separator := by
  simpa [buildSeparatorNots, separatorNotsGateTrace] using
    buildSeparatorNotsPrefix_gates_eq base stack hstack separator H
      (Nat.le_refl H)

private structure InputArmResult {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (length cost : Nat) where
  builder : CircuitBuilder
  wire : CircuitBuilder.Wire
  extension : base.Extends builder
  valid : builder.WireValid wire
  eval_true_iff : ∀ inputs,
    builder.evalWire inputs wire = true ↔
      VerifierInputArmMatches W H x (evalStackBits base inputs stack) length
  gate_delta : builder.gates.length = base.gates.length + cost

private def buildInputArm {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn base)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, base.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      base.evalWire inputs (separatorNots cell) =
        !(base.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (length : Nat) : InputArmResult W H x base stack length
      (verifierInputArmGateCost H x.length length) := by
  by_cases hfit : length + 1 + x.length ≤ H
  · let wires := inputArmWires W H x stack separatorNots length hfit
    let output := base.conjunction wires
      (inputArmWires_valid W H x base stack hstack separatorNots
        hseparatorNots length hfit)
    exact
      { builder := output.1
        wire := output.2
        extension := CircuitBuilder.conjunction_extends _ _ _
        valid := CircuitBuilder.conjunction_wireValid _ _ _
        eval_true_iff := by
          intro inputs
          rw [CircuitBuilder.conjunction_eval]
          exact inputArmWires_all_eq_true_iff W H x base inputs stack
            separatorNots (hseparatorEval inputs) length hfit
        gate_delta := by
          rw [CircuitBuilder.conjunction_gate_delta]
          simp only [wires, inputArmWires_length,
            verifierInputArmGateCost, if_pos hfit]
          omega }
  · exact
      { builder := base
        wire := pool.falseWire
        extension := .refl base
        valid := pool.falseValid
        eval_true_iff := by
          intro inputs
          rw [pool.false_eval]
          constructor
          · intro htrue
            exact Bool.noConfusion htrue
          · rintro ⟨hfit', _⟩
            exact (hfit hfit').elim
        gate_delta := by simp [verifierInputArmGateCost, hfit] }

/-- Literal total-constructor trace for one candidate certificate length.
Fitting arms append a tail-first conjunction; nonfitting arms append nothing
and reuse the shared false wire. -/
def inputArmGateTrace {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ) (start : Nat)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (length : Nat) : List CircuitGate := by
  if hfit : length + 1 + x.length ≤ H then
    exact (CircuitBuilder.conjunctionGateTrace start
      (inputArmWires W H x stack separatorNots length hfit)).gates
  else
    exact []

private theorem buildInputArm_gates_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (base : CircuitBuilder) (pool : base.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn base)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, base.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      base.evalWire inputs (separatorNots cell) =
        !(base.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (length : Nat) :
    (buildInputArm W H x base pool stack hstack separatorNots
      hseparatorNots hseparatorEval length).builder.gates =
      base.gates ++ inputArmGateTrace W H x base.gates.length stack
        separatorNots length := by
  classical
  by_cases hfit : length + 1 + x.length ≤ H
  · rw [show buildInputArm W H x base pool stack hstack separatorNots
        hseparatorNots hseparatorEval length =
        { builder := (base.conjunction
            (inputArmWires W H x stack separatorNots length hfit)
            (inputArmWires_valid W H x base stack hstack separatorNots
              hseparatorNots length hfit)).1
          wire := (base.conjunction
            (inputArmWires W H x stack separatorNots length hfit)
            (inputArmWires_valid W H x base stack hstack separatorNots
              hseparatorNots length hfit)).2
          extension := CircuitBuilder.conjunction_extends _ _ _
          valid := CircuitBuilder.conjunction_wireValid _ _ _
          eval_true_iff := by
            intro inputs
            rw [CircuitBuilder.conjunction_eval]
            exact inputArmWires_all_eq_true_iff W H x base inputs stack
              separatorNots (hseparatorEval inputs) length hfit
          gate_delta := by
            rw [CircuitBuilder.conjunction_gate_delta]
            simp only [inputArmWires_length, verifierInputArmGateCost,
              if_pos hfit]
            omega } by
      simp only [buildInputArm, hfit]
      rfl]
    rw [CircuitBuilder.conjunction_gates_eq]
    simp [inputArmGateTrace, hfit]
  · rw [show buildInputArm W H x base pool stack hstack separatorNots
        hseparatorNots hseparatorEval length =
        { builder := base
          wire := pool.falseWire
          extension := .refl base
          valid := pool.falseValid
          eval_true_iff := by
            intro inputs
            rw [pool.false_eval]
            constructor
            · intro htrue
              exact Bool.noConfusion htrue
            · rintro ⟨hfit', _⟩
              exact (hfit hfit').elim
          gate_delta := by simp [verifierInputArmGateCost, hfit] } by
      simp only [buildInputArm, hfit]
      rfl]
    simp [inputArmGateTrace, hfit]

structure InputArmsResult {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (start : CircuitBuilder) (H : Nat) (x : List Γ)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀) (n : Nat) where
  builder : CircuitBuilder
  wires : Fin n → CircuitBuilder.Wire
  extension : start.Extends builder
  valid : ∀ arm, builder.WireValid (wires arm)
  eval_true_iff : ∀ inputs arm,
    builder.evalWire inputs (wires arm) = true ↔
      VerifierInputArmMatches W H x (evalStackBits start inputs stack) arm.val
  gate_delta : builder.gates.length = start.gates.length +
    ∑ arm : Fin n, verifierInputArmGateCost H x.length arm.val

def buildInputArms {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none)))) :
    (n : Nat) → InputArmsResult W start H x stack n
  | 0 =>
      { builder := start
        wires := Fin.elim0
        extension := .refl start
        valid := fun arm => Fin.elim0 arm
        eval_true_iff := fun _ arm => Fin.elim0 arm
        gate_delta := by simp }
  | n + 1 => by
      let previous := buildInputArms W H x start pool stack hstack
        separatorNots hseparatorNots hseparatorEval n
      let arm := buildInputArm W H x previous.builder
        (pool.mono previous.extension) stack (hstack.mono previous.extension)
        separatorNots (fun cell => previous.extension.wireValid
          (hseparatorNots cell)) (fun inputs cell => by
            rw [previous.extension.evalWire_eq inputs (hseparatorNots cell),
              previous.extension.evalWire_eq inputs (hstack.cell cell _)];
            exact hseparatorEval inputs cell) n
      let wires : Fin (n + 1) → CircuitBuilder.Wire := fun i =>
        if hi : i.val < n then previous.wires ⟨i.val, hi⟩ else arm.wire
      exact
        { builder := arm.builder
          wires := wires
          extension := previous.extension.trans arm.extension
          valid := by
            intro i
            simp only [wires]
            split
            next hi => exact arm.extension.wireValid (previous.valid ⟨i.val, hi⟩)
            next => exact arm.valid
          eval_true_iff := by
            intro inputs i
            simp only [wires]
            split
            next hi =>
              rw [arm.extension.evalWire_eq inputs
                (previous.valid ⟨i.val, hi⟩)]
              exact previous.eval_true_iff inputs ⟨i.val, hi⟩
            next hi =>
              have hiEq : i.val = n := by omega
              rw [arm.eval_true_iff]
              rw [evalStackBits_extends previous.extension inputs stack hstack]
              simp only [hiEq]
          gate_delta := by
            rw [arm.gate_delta, previous.gate_delta, Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last]
            omega }

/-- Literal ordered trace for the recursive candidate-length family. -/
def inputArmsGateTrace {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none)))) :
    Nat → List CircuitGate
  | 0 => []
  | n + 1 =>
      let previous := buildInputArms W H x start pool stack hstack
        separatorNots hseparatorNots hseparatorEval n
      inputArmsGateTrace W H x start pool stack hstack separatorNots
          hseparatorNots hseparatorEval n ++
        inputArmGateTrace W H x previous.builder.gates.length stack
          separatorNots n

/-- The proof-carrying arm family appends exactly the recursive literal
trace. -/
theorem buildInputArms_gates_eq {Γ : Type} {L : Language Γ}
    (W : VerifierWitness L) (H : Nat) (x : List Γ)
    (start : CircuitBuilder) (pool : start.BoolWirePool)
    (stack : StackWires W.machine.tm H W.machine.tm.k₀)
    (hstack : stack.ValidIn start)
    (separatorNots : Fin H → CircuitBuilder.Wire)
    (hseparatorNots : ∀ cell, start.WireValid (separatorNots cell))
    (hseparatorEval : ∀ inputs cell,
      start.evalWire inputs (separatorNots cell) =
        !(start.evalWire inputs
          (stack.cell cell (verifierInputCode W none))))
    (n : Nat) :
    (buildInputArms W H x start pool stack hstack separatorNots
      hseparatorNots hseparatorEval n).builder.gates =
      start.gates ++ inputArmsGateTrace W H x start pool stack hstack
        separatorNots hseparatorNots hseparatorEval n := by
  induction n with
  | zero => simp [buildInputArms, inputArmsGateTrace]
  | succ n ih =>
      simp only [buildInputArms, inputArmsGateTrace]
      rw [buildInputArm_gates_eq]
      rw [ih]
      simp only [List.append_assoc]

end VerifierInput

end

end CLRS.Chapter34.Turing.CookLevin
