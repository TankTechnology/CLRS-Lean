import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau

/-!
# CLRS Section 34.4 - Canonical Cook--Levin row-validity circuits

This module is the circuitization layer for one bounded tableau row.  It builds
exactly-one constraints for every finite row field, enforces agreement between
the halted bit and the reserved none-label, and validates stack cells with one
linear suffix-OR active mask per stack.

Main results:

- Definition {lit}`validCfgCircuit`: a proof-carrying append-only circuit for
  canonical row validity.
- Theorem {lit}`validCfgCircuit_eval_iff`: the output is true exactly when
  evaluated row decoding succeeds.
- Theorem {lit}`validCfgCircuit_gate_delta`: the construction has the exact
  affine cost {lit}`validCfgGateCost`.
- Definition {lit}`cfgOneHotGroupEquivFin`: the one-hot family order is
  explicit and uniform in the runtime stack height.

Current gaps:

- The row-transition circuit and whole-tableau assembly belong to the next
  circuitization layers.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Canonical row-validity circuits -/

/-! ### Exact one-hot family trace -/

/-- Pure gate-order trace for a serial family of exactly-one constraints. -/
structure ExactlyOneFamilyGateTrace (n : Nat) where
  gates : List CircuitGate
  outputs : Fin n → CircuitBuilder.Wire

/-- Serialize the exact exactly-one trace of every group in family order. -/
def exactlyOneFamilyGateTrace (start : Nat) :
    (n : Nat) →
      (groups : Fin n → List CircuitBuilder.Wire) →
      ExactlyOneFamilyGateTrace n
  | 0, _ =>
      { gates := []
        outputs := fun i => Fin.elim0 i }
  | n + 1, groups =>
      let previous := exactlyOneFamilyGateTrace start n
        (fun i => groups i.castSucc)
      let last := exactlyOneGateTrace (start + previous.gates.length)
        (groups (Fin.last n))
      { gates := previous.gates ++ last.gates
        outputs := fun i =>
          if hi : i.val < n then previous.outputs ⟨i.val, hi⟩
          else last.wire }

/-- The family trace is the sum of the exact `3m+4` group costs. -/
@[simp] theorem exactlyOneFamilyGateTrace_length (start n : Nat)
    (groups : Fin n → List CircuitBuilder.Wire) :
    (exactlyOneFamilyGateTrace start n groups).gates.length =
      ∑ i, (3 * (groups i).length + 4) := by
  induction n with
  | zero => simp [exactlyOneFamilyGateTrace]
  | succ n ih =>
      simp only [exactlyOneFamilyGateTrace, List.length_append,
        exactlyOneGateTrace_length]
      rw [ih, Fin.sum_univ_castSucc]

/-- Proof-carrying result of a serial family of exactly-one constraints. -/
structure ExactlyOneFamilyResult (base : CircuitBuilder) (n : Nat)
    (groups : Fin n → List CircuitBuilder.Wire) where
  builder : CircuitBuilder
  outputs : Fin n → CircuitBuilder.Wire
  extension : base.Extends builder
  outputsValid : ∀ i, builder.WireValid (outputs i)
  gate_delta : builder.gates.length = base.gates.length +
    ∑ i, (3 * (groups i).length + 4)
  eval : ∀ inputs i, builder.evalWire inputs (outputs i) = true ↔
    (wireValues base inputs (groups i)).count true = 1

def exactlyOneFamily (base : CircuitBuilder) :
    (n : Nat) → (groups : Fin n → List CircuitBuilder.Wire) →
      (∀ i wire, wire ∈ groups i → base.WireValid wire) →
      ExactlyOneFamilyResult base n groups
  | 0, groups, _ =>
      { builder := base
        outputs := fun i => Fin.elim0 i
        extension := CircuitBuilder.Extends.refl base
        outputsValid := fun i => Fin.elim0 i
        gate_delta := by simp
        eval := fun _ i => Fin.elim0 i }
  | n + 1, groups, hvalid => by
      let initialGroups : Fin n → List CircuitBuilder.Wire := fun i =>
        groups i.castSucc
      let previous := exactlyOneFamily base n initialGroups (by
        intro i wire hwire
        exact hvalid i.castSucc wire hwire)
      have hlastValid : ∀ wire ∈ groups (Fin.last n),
          previous.builder.WireValid wire := by
        intro wire hwire
        exact previous.extension.wireValid (hvalid (Fin.last n) wire hwire)
      let last := exactlyOne previous.builder (groups (Fin.last n)) hlastValid
      let outputs : Fin (n + 1) → CircuitBuilder.Wire := fun i =>
        if hi : i.val < n then previous.outputs ⟨i.val, hi⟩ else last.wire
      refine
        { builder := last.builder
          outputs := outputs
          extension := previous.extension.trans last.extension
          outputsValid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro i
        simp only [outputs]
        split
        next hi =>
          exact last.extension.wireValid (previous.outputsValid ⟨i.val, hi⟩)
        next => exact last.valid
      · rw [exactlyOne_gate_delta, previous.gate_delta]
        rw [Fin.sum_univ_castSucc]
        simp only [initialGroups]
        omega
      · intro inputs i
        simp only [outputs]
        split
        next hi =>
          rw [last.extension.evalWire_eq inputs
            (previous.outputsValid ⟨i.val, hi⟩)]
          rw [previous.eval]
          have hindex : (⟨i.val, hi⟩ : Fin n).castSucc = i := by
            apply Fin.ext
            rfl
          simp only [initialGroups, hindex]
        next hi =>
          have hilast : i = Fin.last n := by
            apply Fin.ext
            simp
            omega
          subst i
          rw [exactlyOne_eval_iff]
          have hvalues :
              wireValues previous.builder inputs (groups (Fin.last n)) =
                wireValues base inputs (groups (Fin.last n)) := by
            apply List.map_congr_left
            intro wire hwire
            exact previous.extension.evalWire_eq inputs
              (hvalid (Fin.last n) wire hwire)
          rw [hvalues]

private theorem exactlyOneFamily_trace_eq (base : CircuitBuilder)
    (n : Nat) (groups : Fin n → List CircuitBuilder.Wire)
    (hvalid : ∀ i wire, wire ∈ groups i → base.WireValid wire) :
    (exactlyOneFamily base n groups hvalid).builder.gates =
        base.gates ++
          (exactlyOneFamilyGateTrace base.gates.length n groups).gates ∧
      ∀ i, (exactlyOneFamily base n groups hvalid).outputs i =
        (exactlyOneFamilyGateTrace base.gates.length n groups).outputs i := by
  induction n with
  | zero =>
      simp [exactlyOneFamily, exactlyOneFamilyGateTrace]
  | succ n ih =>
      let previousGroups : Fin n → List CircuitBuilder.Wire :=
        fun i => groups i.castSucc
      let hprevious : ∀ i wire,
          wire ∈ previousGroups i → base.WireValid wire :=
        fun i wire hwire => hvalid i.castSucc wire hwire
      rcases ih previousGroups hprevious with ⟨hgates, houtputs⟩
      dsimp only [previousGroups] at hgates houtputs
      simp only [exactlyOneFamily]
      rw [exactlyOne_gates_eq, hgates]
      simp only [exactlyOneFamilyGateTrace]
      constructor
      · simp [List.append_assoc]
      · intro i
        split
        next hi => exact houtputs ⟨i.val, hi⟩
        next =>
          rw [exactlyOne_wire_eq_trace]
          rw [hgates]
          simp

/-- The proof-carrying one-hot family appends exactly its pure gate trace. -/
theorem exactlyOneFamily_gates_eq (base : CircuitBuilder)
    (n : Nat) (groups : Fin n → List CircuitBuilder.Wire)
    (hvalid : ∀ i wire, wire ∈ groups i → base.WireValid wire) :
    (exactlyOneFamily base n groups hvalid).builder.gates =
      base.gates ++
        (exactlyOneFamilyGateTrace base.gates.length n groups).gates :=
  (exactlyOneFamily_trace_eq base n groups hvalid).1

/-- Every one-hot family output agrees with the corresponding pure trace. -/
theorem exactlyOneFamily_output_eq_trace (base : CircuitBuilder)
    (n : Nat) (groups : Fin n → List CircuitBuilder.Wire)
    (hvalid : ∀ i wire, wire ∈ groups i → base.WireValid wire)
    (i : Fin n) :
    (exactlyOneFamily base n groups hvalid).outputs i =
      (exactlyOneFamilyGateTrace base.gates.length n groups).outputs i :=
  (exactlyOneFamily_trace_eq base n groups hvalid).2 i

/-! ## Exact per-cell validity trace -/

/-- Pure gate-order trace of the per-cell active/nonblank equivalence family. -/
structure CellValidityGateTrace (n : Nat) where
  gates : List CircuitGate
  outputs : Fin n → CircuitBuilder.Wire

/-- Tail-first trace of the six primitive gates used for each stack cell:
one negation of the blank bit followed by the five-gate equality trace. -/
def cellValidityGateTrace (start : Nat) :
    (n : Nat) →
      (active blank : Fin n → CircuitBuilder.Wire) →
      CellValidityGateTrace n
  | 0, _, _ =>
      { gates := []
        outputs := fun i => Fin.elim0 i }
  | n + 1, active, blank =>
      let previous := cellValidityGateTrace start n
        (fun i => active i.castSucc) (fun i => blank i.castSucc)
      let next := start + previous.gates.length
      let matched := CircuitBuilder.boolEqGateTrace (next + 1)
        (active (Fin.last n)) next
      { gates := previous.gates ++ [.not (blank (Fin.last n))] ++ matched.gates
        outputs := fun i =>
          if hi : i.val < n then previous.outputs ⟨i.val, hi⟩
          else matched.wire }

/-- The cell-validity trace pays exactly six gates per cell. -/
@[simp] theorem cellValidityGateTrace_length (start n : Nat)
    (active blank : Fin n → CircuitBuilder.Wire) :
    (cellValidityGateTrace start n active blank).gates.length = 6 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [cellValidityGateTrace, ih]
      omega

/-- Proof-carrying result of the per-cell active/nonblank equivalence family. -/
structure CellValidityResult (base : CircuitBuilder) (n : Nat)
    (active blank : Fin n → CircuitBuilder.Wire) where
  builder : CircuitBuilder
  outputs : Fin n → CircuitBuilder.Wire
  extension : base.Extends builder
  outputsValid : ∀ i, builder.WireValid (outputs i)
  gate_delta : builder.gates.length = base.gates.length + 6 * n
  eval : ∀ inputs i, builder.evalWire inputs (outputs i) = true ↔
    base.evalWire inputs (active i) = !base.evalWire inputs (blank i)

def buildCellValidity (base : CircuitBuilder) :
    (n : Nat) → (active blank : Fin n → CircuitBuilder.Wire) →
      (∀ i, base.WireValid (active i)) →
      (∀ i, base.WireValid (blank i)) →
      CellValidityResult base n active blank
  | 0, active, blank, _, _ =>
      { builder := base
        outputs := fun i => Fin.elim0 i
        extension := CircuitBuilder.Extends.refl base
        outputsValid := fun i => Fin.elim0 i
        gate_delta := by simp
        eval := fun _ i => Fin.elim0 i }
  | n + 1, active, blank, hactive, hblank => by
      let previous := buildCellValidity base n (fun i => active i.castSucc)
        (fun i => blank i.castSucc) (fun i => hactive i.castSucc)
        (fun i => hblank i.castSucc)
      have hblankLast := previous.extension.wireValid (hblank (Fin.last n))
      let nonblank := previous.builder.not (blank (Fin.last n)) hblankLast
      let hextNot := CircuitBuilder.not_extends previous.builder
        (blank (Fin.last n)) hblankLast
      have hactiveLast := hextNot.wireValid
        (previous.extension.wireValid (hactive (Fin.last n)))
      have hnonblank := CircuitBuilder.not_wireValid previous.builder
        (blank (Fin.last n)) hblankLast
      let matched := nonblank.1.eq (active (Fin.last n)) nonblank.2
        hactiveLast hnonblank
      let hextEq := CircuitBuilder.eq_extends nonblank.1
        (active (Fin.last n)) nonblank.2 hactiveLast hnonblank
      let extension := previous.extension.trans (hextNot.trans hextEq)
      let outputs : Fin (n + 1) → CircuitBuilder.Wire := fun i =>
        if hi : i.val < n then previous.outputs ⟨i.val, hi⟩ else matched.2
      refine
        { builder := matched.1
          outputs := outputs
          extension := extension
          outputsValid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro i
        simp only [outputs]
        split
        next hi =>
          simpa only [matched] using
            ((hextNot.trans hextEq).wireValid
              (previous.outputsValid ⟨i.val, hi⟩))
        next =>
          simpa only [matched] using
            (CircuitBuilder.eq_wireValid nonblank.1
              (active (Fin.last n)) nonblank.2 hactiveLast hnonblank)
      · dsimp only [matched, nonblank]
        rw [CircuitBuilder.eq_gate_delta, CircuitBuilder.not_gate_delta,
          previous.gate_delta]
        omega
      · intro inputs i
        dsimp only [matched, nonblank]
        simp only [outputs]
        split
        next hi =>
          rw [(hextNot.trans hextEq).evalWire_eq inputs
            (previous.outputsValid ⟨i.val, hi⟩)]
          rw [previous.eval]
          have hindex : (⟨i.val, hi⟩ : Fin n).castSucc = i := by
            apply Fin.ext
            rfl
          simp only [hindex]
        next hi =>
          have hilast : i = Fin.last n := by
            apply Fin.ext
            simp
            omega
          subst i
          rw [CircuitBuilder.eq_eval]
          rw [hextNot.evalWire_eq inputs
            (previous.extension.wireValid (hactive (Fin.last n)))]
          rw [CircuitBuilder.not_eval]
          rw [previous.extension.evalWire_eq inputs (hactive (Fin.last n))]
          rw [previous.extension.evalWire_eq inputs (hblank (Fin.last n))]
          simp

private theorem buildCellValidity_trace_eq (base : CircuitBuilder)
    (n : Nat) (active blank : Fin n → CircuitBuilder.Wire)
    (hactive : ∀ i, base.WireValid (active i))
    (hblank : ∀ i, base.WireValid (blank i)) :
    (buildCellValidity base n active blank hactive hblank).builder.gates =
        base.gates ++
          (cellValidityGateTrace base.gates.length n active blank).gates ∧
      ∀ i, (buildCellValidity base n active blank hactive hblank).outputs i =
        (cellValidityGateTrace base.gates.length n active blank).outputs i := by
  induction n with
  | zero =>
      simp [buildCellValidity, cellValidityGateTrace]
  | succ n ih =>
      let previousActive : Fin n → CircuitBuilder.Wire :=
        fun i => active i.castSucc
      let previousBlank : Fin n → CircuitBuilder.Wire :=
        fun i => blank i.castSucc
      let hpreviousActive : ∀ i, base.WireValid (previousActive i) :=
        fun i => hactive i.castSucc
      let hpreviousBlank : ∀ i, base.WireValid (previousBlank i) :=
        fun i => hblank i.castSucc
      rcases ih previousActive previousBlank hpreviousActive hpreviousBlank with
        ⟨hgates, houtputs⟩
      dsimp only [previousActive, previousBlank] at hgates houtputs
      have hlength := congrArg List.length hgates
      simp only [List.length_append, cellValidityGateTrace_length] at hlength
      simp only [buildCellValidity]
      rw [CircuitBuilder.eq_gates_eq, CircuitBuilder.not_gates, hgates]
      simp only [CircuitBuilder.not_wire_eq, cellValidityGateTrace]
      constructor
      · rw [hlength]
        simp [CircuitBuilder.boolEqGateTrace, List.append_assoc]
        omega
      · intro i
        split
        next hi => exact houtputs ⟨i.val, hi⟩
        next =>
          rw [CircuitBuilder.eq_wire_eq_trace]
          simp only [CircuitBuilder.boolEqGateTrace,
            CircuitBuilder.not_gates, List.length_append,
            List.length_singleton]
          rw [hlength, cellValidityGateTrace_length]

/-- The proof-carrying cell-validity builder appends its pure trace exactly. -/
theorem buildCellValidity_gates_eq (base : CircuitBuilder)
    (n : Nat) (active blank : Fin n → CircuitBuilder.Wire)
    (hactive : ∀ i, base.WireValid (active i))
    (hblank : ∀ i, base.WireValid (blank i)) :
    (buildCellValidity base n active blank hactive hblank).builder.gates =
      base.gates ++
        (cellValidityGateTrace base.gates.length n active blank).gates :=
  (buildCellValidity_trace_eq base n active blank hactive hblank).1

/-- Every per-cell output wire agrees with the corresponding pure trace. -/
theorem buildCellValidity_output_eq_trace (base : CircuitBuilder)
    (n : Nat) (active blank : Fin n → CircuitBuilder.Wire)
    (hactive : ∀ i, base.WireValid (active i))
    (hblank : ∀ i, base.WireValid (blank i)) (i : Fin n) :
    (buildCellValidity base n active blank hactive hblank).outputs i =
      (cellValidityGateTrace base.gates.length n active blank).outputs i :=
  (buildCellValidity_trace_eq base n active blank hactive hblank).2 i

abbrev CfgOneHotGroup (tm : _root_.Turing.FinTM2) (H : Nat) :=
  Unit ⊕ (Unit ⊕ (Σ _ : tm.K, Unit ⊕ Fin H))

private noncomputable instance cfgOneHotGroupFintype
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    Fintype (CfgOneHotGroup tm H) := by
  letI := tm.kFin
  infer_instance

/-- Exact number of one-hot groups in one bounded row: label, state, and one
height plus `H` cell-symbol groups for each fixed machine stack. -/
def cfgOneHotGroupCount (tm : _root_.Turing.FinTM2) (H : Nat) : Nat :=
  2 + Fintype.card tm.K * (H + 1)

/-- Numeric offset of one stack's height group inside the stack-group block. -/
noncomputable def cfgOneHotStackOffset (tm : _root_.Turing.FinTM2)
    (H : Nat) (k : tm.K) : Nat :=
  (H + 1) * (Fintype.equivFin tm.K k).val

/-- Explicit local order consisting of the stack-height group followed by its
`H` cell-symbol groups. -/
private def cfgOneHotLocalEquivFin (H : Nat) :
    Unit ⊕ Fin H ≃ Fin (H + 1) :=
  ((((finOneEquiv : Fin 1 ≃ Unit).symm).sumCongr
      (Equiv.refl (Fin H))).trans finSumFinEquiv).trans
    (finCongr (by omega))

/-- Explicit row one-hot-group numbering.  Its only noncomputable enumeration
is the fixed machine-stack order; all `H`-dependent positions use literal
product and sum coordinates. -/
noncomputable def cfgOneHotGroupEquivFin
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgOneHotGroup tm H ≃ Fin (cfgOneHotGroupCount tm H) := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let stackGroups : (Σ _k : tm.K, Unit ⊕ Fin H) ≃
      Fin (Fintype.card tm.K * (H + 1)) :=
    (Equiv.sigmaCongrRight (fun _ => cfgOneHotLocalEquivFin H)).trans <|
      (Equiv.sigmaEquivProd tm.K (Fin (H + 1))).trans <|
        (keyEquiv.prodCongr (Equiv.refl (Fin (H + 1)))).trans
          finProdFinEquiv
  let stateAndStacks :=
    (((finOneEquiv : Fin 1 ≃ Unit).symm).sumCongr stackGroups).trans
      finSumFinEquiv
  let allGroups :=
    (((finOneEquiv : Fin 1 ≃ Unit).symm).sumCongr stateAndStacks).trans
      finSumFinEquiv
  exact allGroups.trans (finCongr (by
    simp only [cfgOneHotGroupCount]
    omega))

/-- The row-label one-hot group is first. -/
@[simp] theorem cfgOneHotGroupEquivFin_label_val
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (cfgOneHotGroupEquivFin tm H (.inl ())).val = 0 := by
  simp [cfgOneHotGroupEquivFin]

/-- The row-state one-hot group follows the label group. -/
@[simp] theorem cfgOneHotGroupEquivFin_state_val
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (cfgOneHotGroupEquivFin tm H (.inr (.inl ()))).val = 1 := by
  simp [cfgOneHotGroupEquivFin]

/-- Each stack-height group begins at its explicit fixed-stack block offset. -/
@[simp] theorem cfgOneHotGroupEquivFin_stackHeight_val
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) :
    (cfgOneHotGroupEquivFin tm H (.inr (.inr ⟨k, .inl ()⟩))).val =
      2 + cfgOneHotStackOffset tm H k := by
  simp [cfgOneHotGroupEquivFin, cfgOneHotLocalEquivFin,
    cfgOneHotStackOffset, finProdFinEquiv]
  omega

/-- Cell-symbol groups follow their stack-height group in increasing cell
order. -/
@[simp] theorem cfgOneHotGroupEquivFin_stackCell_val
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) (i : Fin H) :
    (cfgOneHotGroupEquivFin tm H (.inr (.inr ⟨k, .inr i⟩))).val =
      2 + cfgOneHotStackOffset tm H k + 1 + i.val := by
  simp [cfgOneHotGroupEquivFin, cfgOneHotLocalEquivFin,
    cfgOneHotStackOffset, finProdFinEquiv]
  omega

def cfgOneHotGroupWires {tm : _root_.Turing.FinTM2} {H : Nat}
    (wires : CfgWires tm H) : CfgOneHotGroup tm H → List CircuitBuilder.Wire
  | .inl _ => List.ofFn wires.label
  | .inr (.inl _) => List.ofFn wires.state
  | .inr (.inr ⟨k, .inl _⟩) => List.ofFn (wires.stackHeight k)
  | .inr (.inr ⟨k, .inr i⟩) => List.ofFn (wires.stackCell k i)

private def cfgOneHotGroupValid {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) : CfgOneHotGroup tm H → Prop
  | .inl _ => OneHot bits.label
  | .inr (.inl _) => OneHot bits.state
  | .inr (.inr ⟨k, .inl _⟩) => OneHot (bits.stackHeight k)
  | .inr (.inr ⟨k, .inr i⟩) => OneHot (bits.stackCell k i)

private def cfgOneHotGroupSize {tm : _root_.Turing.FinTM2} {H : Nat} :
    CfgOneHotGroup tm H → Nat
  | .inl _ => labelCount tm + 1
  | .inr (.inl _) => stateCount tm
  | .inr (.inr ⟨_, .inl _⟩) => H + 1
  | .inr (.inr ⟨k, .inr _⟩) => (reachableAlphabet tm k).card + 1

private theorem cfgOneHotGroupWires_length
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (wires : CfgWires tm H) (group : CfgOneHotGroup tm H) :
    (cfgOneHotGroupWires wires group).length = cfgOneHotGroupSize group := by
  rcases group with (_ | _ | ⟨k, _ | i⟩) <;>
    simp [cfgOneHotGroupWires, cfgOneHotGroupSize]

/-- Pure trace of every raw one-hot group in a configuration row. -/
structure RawOneHotGateTrace (tm : _root_.Turing.FinTM2) (H : Nat) where
  gates : List CircuitGate
  outputs : CfgOneHotGroup tm H → CircuitBuilder.Wire

/-- Exact family trace obtained from the canonical finite numbering of row
one-hot groups. -/
noncomputable def rawOneHotGateTrace {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H) : RawOneHotGateTrace tm H := by
  let equiv := cfgOneHotGroupEquivFin tm H
  let groups : Fin (cfgOneHotGroupCount tm H) →
      List CircuitBuilder.Wire := fun i =>
    cfgOneHotGroupWires wires (equiv.symm i)
  let family := exactlyOneFamilyGateTrace start _ groups
  exact
    { gates := family.gates
      outputs := fun group => family.outputs (equiv group) }

/-- Exact gate count of the raw row one-hot trace. -/
@[simp] theorem rawOneHotGateTrace_length
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H) :
    (rawOneHotGateTrace start wires).gates.length =
      (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
        ∑ k : tm.K, ((3 * (H + 1) + 4) +
          H * (3 * ((reachableAlphabet tm k).card + 1) + 4)) := by
  unfold rawOneHotGateTrace
  dsimp only
  rw [exactlyOneFamilyGateTrace_length]
  let equiv := cfgOneHotGroupEquivFin tm H
  have hequiv := equiv.symm.sum_comp
    (fun group => 3 * (cfgOneHotGroupWires wires group).length + 4)
  rw [hequiv]
  simp_rw [cfgOneHotGroupWires_length]
  have hs :
      (∑ k : tm.K, ∑ x : Unit ⊕ Fin H,
        (3 * cfgOneHotGroupSize (Sum.inr (Sum.inr ⟨k, x⟩)) + 4)) =
      ∑ k : tm.K, ((3 * (H + 1) + 4) +
        H * (3 * ((reachableAlphabet tm k).card + 1) + 4)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Fintype.sum_sum_type]
    simp [cfgOneHotGroupSize]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [Fintype.sum_unique]
  rw [hs]
  simp [cfgOneHotGroupSize]
  omega

/-- Proof-carrying result of all raw one-hot constraints in a row. -/
structure RawOneHotResult {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H) where
  builder : CircuitBuilder
  outputs : CfgOneHotGroup tm H → CircuitBuilder.Wire
  extension : base.Extends builder
  outputsValid : ∀ group, builder.WireValid (outputs group)
  gate_delta : builder.gates.length = base.gates.length +
    ((3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
      ∑ k : tm.K, ((3 * (H + 1) + 4) +
        H * (3 * ((reachableAlphabet tm k).card + 1) + 4)))
  eval : ∀ inputs group, builder.evalWire inputs (outputs group) = true ↔
    cfgOneHotGroupValid (evalCfgBits base inputs wires) group

def buildRawOneHot {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) : RawOneHotResult base wires := by
  let equiv := cfgOneHotGroupEquivFin tm H
  let groups : Fin (cfgOneHotGroupCount tm H) →
      List CircuitBuilder.Wire := fun i =>
    cfgOneHotGroupWires wires (equiv.symm i)
  let family := exactlyOneFamily base _ groups (by
    intro i wire hwire
    cases hgroup : equiv.symm i with
    | inl _unit =>
      simp only [groups, hgroup, cfgOneHotGroupWires, List.mem_ofFn] at hwire
      rcases hwire with ⟨j, rfl⟩
      apply hvalid
    | inr rest =>
      rcases rest with _unit | stack
      · simp only [groups, hgroup, cfgOneHotGroupWires, List.mem_ofFn] at hwire
        rcases hwire with ⟨j, rfl⟩
        apply hvalid
      · rcases stack with ⟨k, height | cell⟩
        · simp only [groups, hgroup, cfgOneHotGroupWires, List.mem_ofFn] at hwire
          rcases hwire with ⟨j, rfl⟩
          apply hvalid
        · simp only [groups, hgroup, cfgOneHotGroupWires, List.mem_ofFn] at hwire
          rcases hwire with ⟨j, rfl⟩
          apply hvalid)
  refine
    { builder := family.builder
      outputs := fun group => family.outputs (equiv group)
      extension := family.extension
      outputsValid := fun group => family.outputsValid (equiv group)
      gate_delta := ?_
      eval := ?_ }
  · rw [family.gate_delta]
    congr 1
    have hequiv := equiv.symm.sum_comp
      (fun group => 3 * (cfgOneHotGroupWires wires group).length + 4)
    rw [hequiv]
    simp_rw [cfgOneHotGroupWires_length]
    have hs :
        (∑ k : tm.K, ∑ x : Unit ⊕ Fin H,
          (3 * cfgOneHotGroupSize (Sum.inr (Sum.inr ⟨k, x⟩)) + 4)) =
        ∑ k : tm.K, ((3 * (H + 1) + 4) +
          H * (3 * ((reachableAlphabet tm k).card + 1) + 4)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_sum_type]
      simp [cfgOneHotGroupSize]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp only [Fintype.sum_unique]
    rw [hs]
    simp [cfgOneHotGroupSize]
    omega
  · intro inputs group
    rw [family.eval]
    rcases group with (_ | _ | ⟨k, _ | i⟩) <;>
      simp only [cfgOneHotGroupValid] <;>
      rw [oneHot_iff_count_eq_one]
    all_goals
      simp [groups, equiv, cfgOneHotGroupWires, wireValues,
        evalCfgBits, CfgBundle.state, Function.comp_def]
      try rfl

/-- The raw row one-hot builder appends exactly its pure family trace. -/
theorem buildRawOneHot_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (buildRawOneHot base wires hvalid).builder.gates =
      base.gates ++ (rawOneHotGateTrace base.gates.length wires).gates := by
  unfold buildRawOneHot rawOneHotGateTrace
  dsimp only
  apply exactlyOneFamily_gates_eq

/-- Every raw one-hot output agrees with the corresponding pure trace. -/
theorem buildRawOneHot_output_eq_trace
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) (group : CfgOneHotGroup tm H) :
    (buildRawOneHot base wires hvalid).outputs group =
      (rawOneHotGateTrace base.gates.length wires).outputs group := by
  unfold buildRawOneHot rawOneHotGateTrace
  dsimp only
  apply exactlyOneFamily_output_eq_trace

private theorem bool_eq_iff_true_iff (left right : Bool) :
    left = right ↔ (left = true ↔ right = true) := by
  cases left <;> cases right <;> simp

private theorem last_eq_false_iff_choose_lt {A : Nat}
    (bits : Fin (A + 1) → Bool) (hone : OneHot bits) :
    bits (Fin.last A) = false ↔ hone.choose.val < A := by
  cases hlast : bits (Fin.last A) with
  | false =>
      simp only [true_iff]
      by_contra hnot
      have heq : hone.choose = Fin.last A := by
        apply Fin.ext
        simp
        omega
      have := hone.choose_spec.1
      rw [heq, hlast] at this
      contradiction
  | true =>
      simp only [Bool.true_eq_false, false_iff]
      intro hlt
      have heq := hone.choose_spec.2 (Fin.last A) hlast
      have hval := congrArg Fin.val heq
      simp at hval
      omega

private def cellCanonicalAt {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) (hraw : bits.RawDecodable)
    (k : tm.K) (i : Fin H) : Prop :=
  (((rawCfgOf bits hraw).stack k).cells i).val <
      (reachableAlphabet tm k).card ↔
    (i.val < ((rawCfgOf bits hraw).stack k).height.val)

/-! ### Exact stack-validity family trace -/

/-- Pure gate-order trace for active-mask and cell-validity constraints across
an ordered finite family of machine stacks. -/
structure StackValidityFamilyGateTrace (H n : Nat) where
  gates : List CircuitGate
  outputs : Fin n → Fin H → CircuitBuilder.Wire

/-- Compose one suffix-OR mask and one six-gate-per-cell family for each stack. -/
def stackValidityFamilyGateTrace
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H) :
    (n : Nat) → (keys : Fin n → tm.K) →
      StackValidityFamilyGateTrace H n
  | 0, _ =>
      { gates := []
        outputs := fun j => Fin.elim0 j }
  | n + 1, keys =>
      let previous := stackValidityFamilyGateTrace start wires n
        (fun j => keys j.castSucc)
      let k := keys (Fin.last n)
      let next := start + previous.gates.length
      let mask := suffixOrGateTrace next
        (List.ofFn fun i : Fin H => wires.stackHeight k i.succ)
      let active : Fin H → CircuitBuilder.Wire := fun i =>
        mask.outputs (Fin.cast (by simp) i)
      let blank : Fin H → CircuitBuilder.Wire := fun i =>
        wires.stackCell k i (Fin.last (reachableAlphabet tm k).card)
      let cells := cellValidityGateTrace (next + mask.gates.length)
        H active blank
      { gates := previous.gates ++ mask.gates ++ cells.gates
        outputs := fun j =>
          if hj : j.val < n then previous.outputs ⟨j.val, hj⟩
          else cells.outputs }

/-- Each stack pays one {lit}`H+1` active mask and {lit}`6H` cell gates. -/
@[simp] theorem stackValidityFamilyGateTrace_length
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H)
    (n : Nat) (keys : Fin n → tm.K) :
    (stackValidityFamilyGateTrace start wires n keys).gates.length =
      ∑ _j : Fin n, ((H + 1) + 6 * H) := by
  induction n with
  | zero => simp [stackValidityFamilyGateTrace]
  | succ n ih =>
      simp only [stackValidityFamilyGateTrace, List.length_append,
        suffixOrGateTrace_length, List.length_ofFn,
        cellValidityGateTrace_length]
      rw [ih, Fin.sum_univ_castSucc]
      omega

/-- Proof-carrying result of stack-validity constraints across a family. -/
structure StackValidityFamilyResult {tm : _root_.Turing.FinTM2}
    {H : Nat} (base : CircuitBuilder) (wires : CfgWires tm H)
    (n : Nat) (keys : Fin n → tm.K) where
  builder : CircuitBuilder
  outputs : Fin n → Fin H → CircuitBuilder.Wire
  extension : base.Extends builder
  outputsValid : ∀ j i, builder.WireValid (outputs j i)
  gate_delta : builder.gates.length = base.gates.length +
    ∑ _j : Fin n, ((H + 1) + 6 * H)
  eval : ∀ inputs (hraw : (evalCfgBits base inputs wires).RawDecodable) j i,
    builder.evalWire inputs (outputs j i) = true ↔
      cellCanonicalAt (evalCfgBits base inputs wires) hraw (keys j) i

def buildStackValidityFamily {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (n : Nat) → (keys : Fin n → tm.K) →
      StackValidityFamilyResult base wires n keys
  | 0, keys =>
      { builder := base
        outputs := fun j => Fin.elim0 j
        extension := CircuitBuilder.Extends.refl base
        outputsValid := fun j => Fin.elim0 j
        gate_delta := by simp
        eval := fun _ _ j => Fin.elim0 j }
  | n + 1, keys => by
      let initialKeys : Fin n → tm.K := fun j => keys j.castSucc
      let previous := buildStackValidityFamily base wires hvalid n initialKeys
      let k := keys (Fin.last n)
      have hheightValid : ∀ j, previous.builder.WireValid
          (wires.stackHeight k j) := fun j =>
        previous.extension.wireValid (hvalid _)
      let mask := activeMask previous.builder H (wires.stackHeight k) hheightValid
      let active : Fin H → CircuitBuilder.Wire := fun i =>
        mask.outputs (Fin.cast (by simp) i)
      let blank : Fin H → CircuitBuilder.Wire := fun i =>
        wires.stackCell k i (Fin.last (reachableAlphabet tm k).card)
      have hactive : ∀ i, mask.builder.WireValid (active i) := fun i =>
        mask.outputsValid (Fin.cast (by simp) i)
      have hblank : ∀ i, mask.builder.WireValid (blank i) := fun i =>
        mask.extension.wireValid
          (previous.extension.wireValid (hvalid _))
      let cells := buildCellValidity mask.builder H active blank hactive hblank
      let outputs : Fin (n + 1) → Fin H → CircuitBuilder.Wire := fun j =>
        if hj : j.val < n then previous.outputs ⟨j.val, hj⟩ else cells.outputs
      let hext := previous.extension.trans (mask.extension.trans cells.extension)
      refine
        { builder := cells.builder
          outputs := outputs
          extension := hext
          outputsValid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro j i
        simp only [outputs]
        split
        next hj =>
          simpa only [cells] using
            ((mask.extension.trans cells.extension).wireValid
              (previous.outputsValid ⟨j.val, hj⟩ i))
        next => simpa only [cells] using cells.outputsValid i
      · dsimp only [cells, mask]
        rw [(buildCellValidity _ _ _ _ _ _).gate_delta,
          activeMask_gate_delta, previous.gate_delta]
        rw [Fin.sum_univ_castSucc]
        omega
      · intro inputs hraw j i
        simp only [outputs]
        split
        next hj =>
          rw [(mask.extension.trans cells.extension).evalWire_eq inputs
            (previous.outputsValid ⟨j.val, hj⟩ i)]
          rw [previous.eval inputs hraw]
          have hindex : (⟨j.val, hj⟩ : Fin n).castSucc = j := by
            apply Fin.ext
            rfl
          simp only [initialKeys, hindex]
        next hj =>
          have hjlast : j = Fin.last n := by
            apply Fin.ext
            simp
            omega
          subst j
          rw [cells.eval]
          rw [bool_eq_iff_true_iff]
          have hpreviousEval (height : Fin (H + 1)) :
              previous.builder.evalWire inputs (wires.stackHeight k height) =
                base.evalWire inputs (wires.stackHeight k height) :=
            previous.extension.evalWire_eq inputs (hvalid _)
          have honePrevious : OneHot (fun height =>
              previous.builder.evalWire inputs (wires.stackHeight k height)) := by
            refine ⟨(hraw.stackHeight k).choose, ?_, ?_⟩
            · change previous.builder.evalWire inputs
                (wires.stackHeight k (hraw.stackHeight k).choose) = true
              rw [hpreviousEval]
              have hr := (hraw.stackHeight k).choose_spec.1
              change base.evalWire inputs
                (wires.stackHeight k (hraw.stackHeight k).choose) = true at hr
              exact hr
            · intro height hheight
              apply (hraw.stackHeight k).choose_spec.2 height
              change previous.builder.evalWire inputs
                (wires.stackHeight k height) = true at hheight
              rw [hpreviousEval] at hheight
              change base.evalWire inputs (wires.stackHeight k height) = true
              exact hheight
          have hchoose : honePrevious.choose = (hraw.stackHeight k).choose := by
            apply (honePrevious.choose_spec.2 _ ?_).symm
            change previous.builder.evalWire inputs
              (wires.stackHeight k (hraw.stackHeight k).choose) = true
            rw [hpreviousEval]
            have hr := (hraw.stackHeight k).choose_spec.1
            change base.evalWire inputs
              (wires.stackHeight k (hraw.stackHeight k).choose) = true at hr
            exact hr
          rw [show mask.builder.evalWire inputs (active i) = true ↔
              i.val < honePrevious.choose.val by
            simpa [active, mask] using activeMask_eval_iff_lt_choose
              previous.builder H (wires.stackHeight k) hheightValid inputs
              honePrevious i]
          rw [Bool.not_eq_true_eq_eq_false]
          have hblankEval : mask.builder.evalWire inputs (blank i) =
              (evalCfgBits base inputs wires).stackCell k i
                (Fin.last (reachableAlphabet tm k).card) := by
            dsimp only [blank]
            change mask.builder.evalWire inputs
                (wires.stackCell k i (Fin.last (reachableAlphabet tm k).card)) =
              base.evalWire inputs
                (wires.stackCell k i (Fin.last (reachableAlphabet tm k).card))
            exact (previous.extension.trans mask.extension).evalWire_eq inputs
              (hvalid _)
          rw [hblankEval]
          rw [last_eq_false_iff_choose_lt
            ((evalCfgBits base inputs wires).stackCell k i)
            (hraw.stackCell k i)]
          rw [hchoose]
          simp only [cellCanonicalAt, rawCfgOf]
          exact iff_comm

private theorem buildStackValidityFamily_trace_eq
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) (n : Nat) (keys : Fin n → tm.K) :
    (buildStackValidityFamily base wires hvalid n keys).builder.gates =
        base.gates ++
          (stackValidityFamilyGateTrace base.gates.length wires n keys).gates ∧
      ∀ j i, (buildStackValidityFamily base wires hvalid n keys).outputs j i =
        (stackValidityFamilyGateTrace base.gates.length wires n keys).outputs j i := by
  induction n with
  | zero =>
      simp [buildStackValidityFamily, stackValidityFamilyGateTrace]
  | succ n ih =>
      let initialKeys : Fin n → tm.K := fun j => keys j.castSucc
      let previous := buildStackValidityFamily base wires hvalid n initialKeys
      let purePrevious := stackValidityFamilyGateTrace base.gates.length
        wires n initialKeys
      rcases ih initialKeys with ⟨hpreviousGates, hpreviousOutputs⟩
      have hpreviousLength : previous.builder.gates.length =
          base.gates.length + purePrevious.gates.length := by
        rw [hpreviousGates]
        simp only [List.length_append]
        rfl
      let k := keys (Fin.last n)
      have hheightValid : ∀ j, previous.builder.WireValid
          (wires.stackHeight k j) := fun j =>
        previous.extension.wireValid (hvalid _)
      let mask := activeMask previous.builder H (wires.stackHeight k) hheightValid
      let pureMask := suffixOrGateTrace
        (base.gates.length + purePrevious.gates.length)
        (List.ofFn fun i : Fin H => wires.stackHeight k i.succ)
      have hmaskGates : mask.builder.gates =
          previous.builder.gates ++ pureMask.gates := by
        rw [activeMask_gates_eq]
        simp only [pureMask, hpreviousLength]
      let active : Fin H → CircuitBuilder.Wire := fun i =>
        mask.outputs (Fin.cast (by simp) i)
      let pureActive : Fin H → CircuitBuilder.Wire := fun i =>
        pureMask.outputs (Fin.cast (by simp) i)
      have hactiveEq : active = pureActive := by
        funext i
        dsimp only [active, pureActive]
        rw [activeMask_output_eq_trace]
        simp only [pureMask, hpreviousLength]
      let blank : Fin H → CircuitBuilder.Wire := fun i =>
        wires.stackCell k i (Fin.last (reachableAlphabet tm k).card)
      have hactive : ∀ i, mask.builder.WireValid (active i) := fun i =>
        mask.outputsValid (Fin.cast (by simp) i)
      have hblank : ∀ i, mask.builder.WireValid (blank i) := fun i =>
        mask.extension.wireValid
          (previous.extension.wireValid (hvalid _))
      let cells := buildCellValidity mask.builder H active blank hactive hblank
      let pureCells := cellValidityGateTrace
        (base.gates.length + purePrevious.gates.length + pureMask.gates.length)
        H pureActive blank
      have hmaskLength : mask.builder.gates.length =
          base.gates.length + purePrevious.gates.length + pureMask.gates.length := by
        rw [hmaskGates, hpreviousGates]
        simp only [List.length_append]
        rfl
      have hcellsGates : cells.builder.gates =
          mask.builder.gates ++ pureCells.gates := by
        rw [buildCellValidity_gates_eq]
        simp only [pureCells, hmaskLength, hactiveEq]
      have hcellsOutputs (i : Fin H) :
          cells.outputs i = pureCells.outputs i := by
        rw [buildCellValidity_output_eq_trace]
        simp only [pureCells, hmaskLength, hactiveEq]
      simp only [buildStackValidityFamily, stackValidityFamilyGateTrace]
      constructor
      · rw [hcellsGates, hmaskGates, hpreviousGates]
        simp only [initialKeys, purePrevious, k, pureMask, pureActive,
          blank, pureCells, List.append_assoc]
      · intro j i
        split
        next hj => exact hpreviousOutputs ⟨j.val, hj⟩ i
        next => exact hcellsOutputs i

/-- The stack-validity family appends exactly its pure composite trace. -/
theorem buildStackValidityFamily_gates_eq
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) (n : Nat) (keys : Fin n → tm.K) :
    (buildStackValidityFamily base wires hvalid n keys).builder.gates =
      base.gates ++
        (stackValidityFamilyGateTrace base.gates.length wires n keys).gates :=
  (buildStackValidityFamily_trace_eq base wires hvalid n keys).1

/-- Every stack-cell validity output agrees with the pure composite trace. -/
theorem buildStackValidityFamily_output_eq_trace
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) (n : Nat) (keys : Fin n → tm.K)
    (j : Fin n) (i : Fin H) :
    (buildStackValidityFamily base wires hvalid n keys).outputs j i =
      (stackValidityFamilyGateTrace base.gates.length wires n keys).outputs j i :=
  (buildStackValidityFamily_trace_eq base wires hvalid n keys).2 j i

private theorem cfgOneHotGroup_forall_iff_raw
    {tm : _root_.Turing.FinTM2} {H : Nat} (bits : CfgBits tm H) :
    (∀ group : CfgOneHotGroup tm H, cfgOneHotGroupValid bits group) ↔
      bits.RawDecodable := by
  constructor
  · intro hall
    constructor
    · exact hall (.inl ())
    · exact hall (.inr (.inl ()))
    · intro k
      exact hall (.inr (.inr ⟨k, .inl ()⟩))
    · intro k i
      exact hall (.inr (.inr ⟨k, .inr i⟩))
  · intro hraw group
    rcases group with (_ | _ | ⟨k, _ | i⟩)
    · exact hraw.label
    · exact hraw.state
    · exact hraw.stackHeight k
    · exact hraw.stackCell k i

private theorem oneHot_apply_eq_true_iff {n : Nat} (bits : Fin n → Bool)
    (hone : OneHot bits) (i : Fin n) :
    bits i = true ↔ i = hone.choose := by
  exact ⟨hone.choose_spec.2 i, fun hi => by simpa [hi] using hone.choose_spec.1⟩

/-- Closed exact gate cost of canonical row validation.  For a fixed machine,
this expression is affine in the public stack bound {name}`H`. -/
def validCfgGateCost (tm : _root_.Turing.FinTM2) (H : Nat) : Nat := by
  letI := tm.kFin
  exact 3 * labelCount tm + 3 * stateCount tm + 20 +
    ∑ k : tm.K, (H * (3 * (reachableAlphabet tm k).card + 19) + 9)

private def validCfgGateCostRaw (tm : _root_.Turing.FinTM2) (H : Nat) : Nat := by
  letI := tm.kFin
  exact
    (3 * (labelCount tm + 1) + 4) +
    (3 * stateCount tm + 4) +
    (∑ k : tm.K,
      ((3 * (H + 1) + 4) +
       H * (3 * ((reachableAlphabet tm k).card + 1) + 4) +
       (H + 1) +
       6 * H)) +
    5 +
    (4 + ∑ _k : tm.K, (1 + 2 * H))

private theorem validCfgGateCostRaw_eq (tm : _root_.Turing.FinTM2) (H : Nat) :
    validCfgGateCostRaw tm H = validCfgGateCost tm H := by
  letI := tm.kFin
  have hstack :
      (∑ k : tm.K,
        ((3 * (H + 1) + 4) +
         H * (3 * ((reachableAlphabet tm k).card + 1) + 4) +
         (H + 1) +
         6 * H)) =
      ∑ k : tm.K, (H * (3 * (reachableAlphabet tm k).card + 17) + 8) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hfinal :
      (∑ _k : tm.K, (1 + 2 * H)) =
      ∑ _k : tm.K, (2 * H + 1) := by
    apply Finset.sum_congr rfl
    intro k _
    omega
  rw [validCfgGateCostRaw, validCfgGateCost, hstack, hfinal]
  have hcombine :
      (∑ k : tm.K, (H * (3 * (reachableAlphabet tm k).card + 17) + 8)) +
      (∑ _k : tm.K, (2 * H + 1)) =
      ∑ k : tm.K, (H * (3 * (reachableAlphabet tm k).card + 19) + 9) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  omega

private theorem listAll_ofFn_eq_true_iff {n : Nat} {alpha : Type}
    (f : Fin n → alpha) (predicate : alpha → Bool) :
    (List.ofFn f).all predicate = true ↔
      ∀ i, predicate (f i) = true := by
  rw [List.all_eq_true]
  constructor
  · intro hall i
    apply hall
    rw [List.mem_ofFn]
    exact ⟨i, rfl⟩
  · intro hall value hvalue
    rw [List.mem_ofFn] at hvalue
    rcases hvalue with ⟨i, rfl⟩
    exact hall i

/-- Pure gate-order trace of the complete canonical-validity circuit for one
bounded tableau row. -/
structure CanonicalValidityGateTrace where
  gates : List CircuitGate
  wire : CircuitBuilder.Wire

/-- Compose raw one-hot constraints, halted-label agreement, all stack-cell
constraints, and their final conjunction in the semantic builder's order. -/
def canonicalValidityGateTrace {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H) : CanonicalValidityGateTrace := by
  letI : Fintype tm.K := tm.kFin
  let raw := rawOneHotGateTrace start wires
  let haltedMatch := CircuitBuilder.boolEqGateTrace
    (start + raw.gates.length) wires.halted
    (wires.label (Fin.last (labelCount tm)))
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let stackTrace := stackValidityFamilyGateTrace
    (start + raw.gates.length + haltedMatch.gates.length) wires
    (Fintype.card tm.K) (fun j => keyEquiv.symm j)
  let groupEquiv := cfgOneHotGroupEquivFin tm H
  let rawConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun j : Fin (cfgOneHotGroupCount tm H) =>
      raw.outputs (groupEquiv.symm j)
  let stackConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * H) =>
      let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := H)).symm p
      stackTrace.outputs q.1 q.2
  let constraints := rawConstraints ++ haltedMatch.wire :: stackConstraints
  let final := CircuitBuilder.conjunctionGateTrace
    (start + raw.gates.length + haltedMatch.gates.length + stackTrace.gates.length)
    constraints
  exact
    { gates := raw.gates ++ haltedMatch.gates ++ stackTrace.gates ++ final.gates
      wire := final.wire }

private structure CanonicalValidityResult {tm : _root_.Turing.FinTM2}
    {H : Nat} (base : CircuitBuilder) (wires : CfgWires tm H) where
  builder : CircuitBuilder
  wire : CircuitBuilder.Wire
  extension : base.Extends builder
  valid : builder.WireValid wire
  gate_delta : builder.gates.length =
    base.gates.length + validCfgGateCost tm H
  eval : ∀ inputs, builder.evalWire inputs wire = true ↔
    (evalCfgBits base inputs wires).Canonical

private def buildCanonicalValidity {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) : CanonicalValidityResult base wires := by
  letI : Fintype tm.K := tm.kFin
  let raw := buildRawOneHot base wires hvalid
  have hhalted : raw.builder.WireValid wires.halted :=
    raw.extension.wireValid (hvalid _)
  have hnoneLabel : raw.builder.WireValid
      (wires.label (Fin.last (labelCount tm))) :=
    raw.extension.wireValid (hvalid _)
  let haltedMatch := raw.builder.eq wires.halted
    (wires.label (Fin.last (labelCount tm))) hhalted hnoneLabel
  let hextHalt := CircuitBuilder.eq_extends raw.builder wires.halted
    (wires.label (Fin.last (labelCount tm))) hhalted hnoneLabel
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  let stackFamily := buildStackValidityFamily (tm := tm) (H := H)
    haltedMatch.1 wires
    (hvalid.mono (raw.extension.trans hextHalt)) (Fintype.card tm.K)
    (fun j => keyEquiv.symm j)
  let groupEquiv := cfgOneHotGroupEquivFin tm H
  let rawConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun j : Fin (cfgOneHotGroupCount tm H) =>
      raw.outputs (groupEquiv.symm j)
  let stackConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * H) =>
      let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := H)).symm p
      stackFamily.outputs q.1 q.2
  let constraints := rawConstraints ++ haltedMatch.2 :: stackConstraints
  have hconstraints : ∀ wire ∈ constraints,
      stackFamily.builder.WireValid wire := by
    intro wire hwire
    simp only [constraints, List.mem_append, List.mem_cons] at hwire
    rcases hwire with hrawWire | hhaltedWire | hstackWire
    · rw [List.mem_ofFn] at hrawWire
      rcases hrawWire with ⟨j, rfl⟩
      exact stackFamily.extension.wireValid
        (hextHalt.wireValid (raw.outputsValid _))
    · subst wire
      exact stackFamily.extension.wireValid
        (CircuitBuilder.eq_wireValid raw.builder wires.halted
          (wires.label (Fin.last (labelCount tm))) hhalted hnoneLabel)
    · rw [List.mem_ofFn] at hstackWire
      rcases hstackWire with ⟨p, rfl⟩
      exact stackFamily.outputsValid _ _
  let final := stackFamily.builder.conjunction constraints hconstraints
  refine
    { builder := final.1
      wire := final.2
      extension := raw.extension.trans (hextHalt.trans
        (stackFamily.extension.trans
          (CircuitBuilder.conjunction_extends stackFamily.builder constraints
            hconstraints)))
      valid := CircuitBuilder.conjunction_wireValid stackFamily.builder constraints
        hconstraints
      gate_delta := ?_
      eval := ?_ }
  · dsimp only [final]
    rw [CircuitBuilder.conjunction_gate_delta, stackFamily.gate_delta,
      CircuitBuilder.eq_gate_delta, raw.gate_delta]
    rw [← validCfgGateCostRaw_eq tm H]
    unfold validCfgGateCostRaw
    simp only [constraints, rawConstraints, stackConstraints,
      List.length_append, List.length_cons, List.length_ofFn]
    simp [cfgOneHotGroupCount]
    have hsum :
        (∑ k : tm.K,
          (8 + H * 17 + H * (reachableAlphabet tm k).card * 3)) =
        (∑ k : tm.K,
          (7 + H * 10 + H * (reachableAlphabet tm k).card * 3)) +
          Fintype.card tm.K * (1 + H * 7) := by
      calc
        _ = ∑ k : tm.K,
            ((7 + H * 10 + H * (reachableAlphabet tm k).card * 3) +
              (1 + H * 7)) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
        _ = (∑ k : tm.K,
              (7 + H * 10 + H * (reachableAlphabet tm k).card * 3)) +
            ∑ _k : tm.K, (1 + H * 7) := Finset.sum_add_distrib
        _ = _ := by simp
    ring_nf
    rw [hsum]
    ring
  · dsimp only [final]
    intro inputs
    let bits := evalCfgBits base inputs wires
    let hextRawStacks := hextHalt.trans stackFamily.extension
    have hrawAll :
        rawConstraints.all
            (fun wire => stackFamily.builder.evalWire inputs wire) = true ↔
          bits.RawDecodable := by
      dsimp only [rawConstraints]
      rw [listAll_ofFn_eq_true_iff]
      constructor
      · intro hall
        apply (cfgOneHotGroup_forall_iff_raw bits).mp
        intro group
        have hgroup : stackFamily.builder.evalWire inputs
            (raw.outputs group) = true := by
          simpa using hall (groupEquiv group)
        rw [hextRawStacks.evalWire_eq inputs (raw.outputsValid group)] at hgroup
        exact (raw.eval inputs group).mp hgroup
      · intro hraw j
        let group := groupEquiv.symm j
        rw [hextRawStacks.evalWire_eq inputs (raw.outputsValid group)]
        exact (raw.eval inputs group).mpr
          ((cfgOneHotGroup_forall_iff_raw bits).mpr hraw group)
    have hhaltedMatch (hraw : bits.RawDecodable) :
        stackFamily.builder.evalWire inputs haltedMatch.2 = true ↔
          ((rawCfgOf bits hraw).halted = true ↔
            (rawCfgOf bits hraw).label.val = labelCount tm) := by
      have hmatchValid : haltedMatch.1.WireValid haltedMatch.2 :=
        CircuitBuilder.eq_wireValid raw.builder wires.halted
          (wires.label (Fin.last (labelCount tm))) hhalted hnoneLabel
      rw [stackFamily.extension.evalWire_eq inputs hmatchValid]
      dsimp only [haltedMatch]
      rw [CircuitBuilder.eq_eval]
      rw [decide_eq_true_eq]
      have hhaltEval : raw.builder.evalWire inputs wires.halted =
          bits.halted := by
        change raw.builder.evalWire inputs wires.halted =
          base.evalWire inputs wires.halted
        exact raw.extension.evalWire_eq inputs (hvalid _)
      have hlabelEval : raw.builder.evalWire inputs
          (wires.label (Fin.last (labelCount tm))) =
          bits.label (Fin.last (labelCount tm)) := by
        change raw.builder.evalWire inputs
            (wires.label (Fin.last (labelCount tm))) =
          base.evalWire inputs (wires.label (Fin.last (labelCount tm)))
        exact raw.extension.evalWire_eq inputs (hvalid _)
      rw [hhaltEval, hlabelEval]
      rw [bool_eq_iff_true_iff]
      change (bits.halted = true ↔
          bits.label (Fin.last (labelCount tm)) = true) ↔ _
      rw [oneHot_apply_eq_true_iff bits.label hraw.label]
      simp only [rawCfgOf]
      constructor
      · intro hiff
        constructor
        · intro hhaltedTrue
          have hlast := hiff.mp hhaltedTrue
          have hval := congrArg Fin.val hlast
          simpa using hval.symm
        · intro hlabel
          apply hiff.mpr
          apply Fin.ext
          simpa using hlabel.symm
      · intro hiff
        constructor
        · intro hhaltedTrue
          apply Fin.ext
          have hlabel := hiff.mp hhaltedTrue
          simpa using hlabel.symm
        · intro hlast
          apply hiff.mpr
          have hval := congrArg Fin.val hlast
          simpa using hval.symm
    have hstackAll (hraw : bits.RawDecodable) :
        stackConstraints.all
            (fun wire => stackFamily.builder.evalWire inputs wire) = true ↔
          ∀ k i, cellCanonicalAt bits hraw k i := by
      have hbitsHalt : evalCfgBits haltedMatch.1 inputs wires = bits := by
        exact evalCfgBits_extends (raw.extension.trans hextHalt) inputs wires
          hvalid
      have hrawHalt :
          (evalCfgBits haltedMatch.1 inputs wires).RawDecodable := by
        rw [hbitsHalt]
        exact hraw
      have hcellEval (j : Fin (Fintype.card tm.K)) (i : Fin H) :
          stackFamily.builder.evalWire inputs (stackFamily.outputs j i) = true ↔
            cellCanonicalAt bits hraw (keyEquiv.symm j) i := by
        rw [stackFamily.eval inputs hrawHalt]
        simp only [hbitsHalt]
      dsimp only [stackConstraints]
      rw [listAll_ofFn_eq_true_iff]
      constructor
      · intro hall k i
        let pair : Fin (Fintype.card tm.K) × Fin H := (keyEquiv k, i)
        let p : Fin (Fintype.card tm.K * H) :=
          finProdFinEquiv pair
        have hp := hall p
        have hq : (finProdFinEquiv (m := Fintype.card tm.K) (n := H)).symm p =
            pair := by simp [p]
        simp only [hq, pair] at hp
        simpa using (hcellEval (keyEquiv k) i).mp hp
      · intro hall p
        let q := (finProdFinEquiv (m := Fintype.card tm.K) (n := H)).symm p
        exact (hcellEval q.1 q.2).mpr (by
          simpa [q] using hall (keyEquiv.symm q.1) q.2)
    rw [CircuitBuilder.conjunction_eval]
    simp only [constraints, List.all_append, List.all_cons]
    rw [Bool.and_eq_true, Bool.and_eq_true]
    rw [hrawAll]
    change bits.RawDecodable ∧ _ ∧ _ ↔ bits.Canonical
    constructor
    · rintro ⟨hraw, hhaltedCanonical, hstacksCanonical⟩
      refine ⟨hraw, ?_, ?_⟩
      · exact (hhaltedMatch hraw).mp hhaltedCanonical
      · intro k i
        exact (hstackAll hraw).mp hstacksCanonical k i
    · rintro ⟨hraw, hcanonical⟩
      refine ⟨hraw, (hhaltedMatch hraw).mpr hcanonical.1, ?_⟩
      apply (hstackAll hraw).mpr
      intro k i
      exact hcanonical.2 k i

/-- Build the canonical-validity predicate for one bounded configuration row.
The input bundle must already be valid in {name}`base`; the result is a fresh valid
wire in an append-only extension. -/
def validCfgCircuit {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) : BuiltWire base :=
  let result := buildCanonicalValidity base wires hvalid
  { builder := result.builder
    wire := result.wire
    extension := result.extension
    valid := result.valid }

/-- Canonical row validation extends its input builder. -/
theorem validCfgCircuit_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    base.Extends (validCfgCircuit base wires hvalid).builder :=
  (buildCanonicalValidity base wires hvalid).extension

/-- The canonical row-validity output is a valid wire. -/
theorem validCfgCircuit_wireValid {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.WireValid
      (validCfgCircuit base wires hvalid).wire :=
  (buildCanonicalValidity base wires hvalid).valid

/-- Canonical row validation appends exactly its pure composite gate trace. -/
theorem validCfgCircuit_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.gates =
      base.gates ++
        (canonicalValidityGateTrace base.gates.length wires).gates := by
  letI : Fintype tm.K := tm.kFin
  simp only [validCfgCircuit, buildCanonicalValidity,
    canonicalValidityGateTrace, buildRawOneHot_gates_eq,
    buildRawOneHot_output_eq_trace, CircuitBuilder.eq_gates_eq,
    CircuitBuilder.eq_wire_eq_trace, buildStackValidityFamily_gates_eq,
    buildStackValidityFamily_output_eq_trace,
    CircuitBuilder.conjunction_gates_eq, List.length_append,
    List.append_assoc, Nat.add_assoc]

/-- The canonical row-validity output wire agrees with its pure trace. -/
theorem validCfgCircuit_wire_eq_trace
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).wire =
      (canonicalValidityGateTrace base.gates.length wires).wire := by
  letI : Fintype tm.K := tm.kFin
  simp only [validCfgCircuit, buildCanonicalValidity,
    canonicalValidityGateTrace, buildRawOneHot_gates_eq,
    buildRawOneHot_output_eq_trace, CircuitBuilder.eq_gates_eq,
    CircuitBuilder.eq_wire_eq_trace, buildStackValidityFamily_gates_eq,
    buildStackValidityFamily_output_eq_trace,
    CircuitBuilder.conjunction_wire_eq_trace, List.length_append,
    List.append_assoc, Nat.add_assoc]

/-- Canonical row validation has the advertised exact affine gate cost. -/
theorem validCfgCircuit_gate_delta {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.gates.length =
      base.gates.length + validCfgGateCost tm H :=
  (buildCanonicalValidity base wires hvalid).gate_delta

/-- The pure row-validity trace has the same exact affine gate cost as the
proof-carrying builder. -/
@[simp] theorem canonicalValidityGateTrace_length
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : Nat) (wires : CfgWires tm H) :
    (canonicalValidityGateTrace start wires).gates.length =
      validCfgGateCost tm H := by
  letI : Fintype tm.K := tm.kFin
  rw [← validCfgGateCostRaw_eq tm H]
  unfold canonicalValidityGateTrace validCfgGateCostRaw
  dsimp only
  simp only [List.length_append, rawOneHotGateTrace_length,
    CircuitBuilder.boolEqGateTrace_length,
    stackValidityFamilyGateTrace_length,
    CircuitBuilder.conjunctionGateTrace_length, List.length_ofFn,
    List.length_cons]
  simp [cfgOneHotGroupCount]
  have hsum :
      (∑ k : tm.K,
        (8 + H * 17 + H * (reachableAlphabet tm k).card * 3)) =
      (∑ k : tm.K,
        (7 + H * 10 + H * (reachableAlphabet tm k).card * 3)) +
        Fintype.card tm.K * (1 + H * 7) := by
    calc
      _ = ∑ k : tm.K,
          ((7 + H * 10 + H * (reachableAlphabet tm k).card * 3) +
            (1 + H * 7)) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ = (∑ k : tm.K,
            (7 + H * 10 + H * (reachableAlphabet tm k).card * 3)) +
          ∑ _k : tm.K, (1 + H * 7) := Finset.sum_add_distrib
      _ = _ := by simp
  ring_nf
  rw [hsum]
  ring

/-- Exact circuit semantics: the output is true precisely when the row
successfully decodes as a canonical machine configuration. -/
theorem validCfgCircuit_eval_iff {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.evalWire inputs
        (validCfgCircuit base wires hvalid).wire = true ↔
      (evalBundle base inputs wires hvalid).isSome = true := by
  change (buildCanonicalValidity base wires hvalid).builder.evalWire inputs
      (buildCanonicalValidity base wires hvalid).wire = true ↔ _
  rw [(buildCanonicalValidity base wires hvalid).eval]
  exact (evalBundle_isSome_iff_canonical base inputs wires hvalid).symm

/-- Equivalent witness form of successful canonical decoding. -/
theorem validCfgCircuit_eval_exists_iff
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.evalWire inputs
        (validCfgCircuit base wires hvalid).wire = true ↔
      ∃ c : tm.Cfg, evalBundle base inputs wires hvalid = some c := by
  rw [validCfgCircuit_eval_iff]
  exact Option.isSome_iff_exists

/-- Every bounded canonical encoding is accepted by the validity circuit. -/
theorem validCfgCircuit_accepts_encodeCfg
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) {c : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) (hheight : ∀ k, (c.stk k).length ≤ H)
    (heval : evalCfgBits base inputs wires =
      encodeRawCfgBits (encodeCfg tm hc hheight)) :
    (validCfgCircuit base wires hvalid).builder.evalWire inputs
        (validCfgCircuit base wires hvalid).wire = true := by
  rw [validCfgCircuit_eval_iff]
  rw [evalBundle_encodeCfg base inputs wires hvalid hc hheight heval]
  rfl


end

end CLRS.Chapter34.Turing.CookLevin
