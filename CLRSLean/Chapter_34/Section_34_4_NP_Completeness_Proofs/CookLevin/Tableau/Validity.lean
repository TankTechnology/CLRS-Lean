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

Current gaps:

- The row-transition circuit and whole-tableau assembly belong to the next
  circuitization layers.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Canonical row-validity circuits -/

private structure ExactlyOneFamilyResult (base : CircuitBuilder) (n : Nat)
    (groups : Fin n → List CircuitBuilder.Wire) where
  builder : CircuitBuilder
  outputs : Fin n → CircuitBuilder.Wire
  extension : base.Extends builder
  outputsValid : ∀ i, builder.WireValid (outputs i)
  gate_delta : builder.gates.length = base.gates.length +
    ∑ i, (3 * (groups i).length + 4)
  eval : ∀ inputs i, builder.evalWire inputs (outputs i) = true ↔
    (wireValues base inputs (groups i)).count true = 1

private def exactlyOneFamily (base : CircuitBuilder) :
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

private structure CellValidityResult (base : CircuitBuilder) (n : Nat)
    (active blank : Fin n → CircuitBuilder.Wire) where
  builder : CircuitBuilder
  outputs : Fin n → CircuitBuilder.Wire
  extension : base.Extends builder
  outputsValid : ∀ i, builder.WireValid (outputs i)
  gate_delta : builder.gates.length = base.gates.length + 6 * n
  eval : ∀ inputs i, builder.evalWire inputs (outputs i) = true ↔
    base.evalWire inputs (active i) = !base.evalWire inputs (blank i)

private def buildCellValidity (base : CircuitBuilder) :
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

private abbrev CfgOneHotGroup (tm : _root_.Turing.FinTM2) (H : Nat) :=
  Unit ⊕ (Unit ⊕ (Σ _ : tm.K, Unit ⊕ Fin H))

private noncomputable instance cfgOneHotGroupFintype
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    Fintype (CfgOneHotGroup tm H) := by
  letI := tm.kFin
  infer_instance

private def cfgOneHotGroupWires {tm : _root_.Turing.FinTM2} {H : Nat}
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

private structure RawOneHotResult {tm : _root_.Turing.FinTM2} {H : Nat}
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

private def buildRawOneHot {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) : RawOneHotResult base wires := by
  let equiv := Fintype.equivFin (CfgOneHotGroup tm H)
  let groups : Fin (Fintype.card (CfgOneHotGroup tm H)) →
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

private structure StackValidityFamilyResult {tm : _root_.Turing.FinTM2}
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

private def buildStackValidityFamily {tm : _root_.Turing.FinTM2} {H : Nat}
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
  let groupEquiv := Fintype.equivFin (CfgOneHotGroup tm H)
  let rawConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun j : Fin (Fintype.card (CfgOneHotGroup tm H)) =>
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
    simp [CfgOneHotGroup]
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

/-- Canonical row validation has the advertised exact affine gate cost. -/
theorem validCfgCircuit_gate_delta {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuit base wires hvalid).builder.gates.length =
      base.gates.length + validCfgGateCost tm H :=
  (buildCanonicalValidity base wires hvalid).gate_delta

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
