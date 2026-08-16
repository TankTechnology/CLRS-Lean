import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Configuration
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder

/-!
# CLRS Section 34.4 - Pure Cook--Levin row codecs and layouts

This file fixes the finite coordinate system for a bounded tableau row.  It
keeps external-input positions separate from internal circuit wires, proves
the exact row width, and provides two decoding layers: total one-hot decoding
to a raw bounded row, followed by the existing canonical machine decoder.

Main results:

- Theorem {lit}`card_cfgSlot`: the unified dependent slot type has exactly the
  advertised linear row width.
- Theorems {lit}`cfgSlotEquivFin_halted_val` through
  {lit}`cfgSlotEquivFin_stackCell_val`: every row-coordinate family has a
  literal runtime-uniform arithmetic wire offset.
- Theorems {lit}`decodeRawCfg_encode` and {lit}`encodeRawCfg_decode`: raw rows and their
  one-hot bit encodings round-trip exactly.
- Theorem `CfgInputLayout.writeCfgBits_index_of_disjoint`: writing one fresh
  row preserves every coordinate of a disjoint row.
- Definition {lit}`allocateCfgInputs`: proof-carrying linear allocation of one
  fresh input gate per row coordinate, with exact evaluation and gate count.
- Definition {lit}`exactlyOne`: a position-sensitive linear exactly-one circuit
  with exact semantics and gate count.

Current gaps:

- Canonical row validity is circuitized in the downstream
  {lit}`CookLevin.Tableau.Validity` module; row transitions and whole-tableau
  assembly belong to later circuitization layers.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Unified row coordinates -/

/-- One Boolean coordinate of a bounded configuration row.  The nested sum is
explicit so its cardinality reduces directly to the textbook width formula. -/
abbrev CfgSlot (tm : _root_.Turing.FinTM2) (H : Nat) :=
  Unit ⊕
    (Fin (labelCount tm + 1) ⊕
      (Fin (stateCount tm) ⊕
        (Σ k : tm.K,
          Fin (H + 1) ⊕
            (Fin H × Fin ((reachableAlphabet tm k).card + 1)))))

namespace CfgSlot

/-- The explicit halted-bit coordinate. -/
def halted (tm : _root_.Turing.FinTM2) (H : Nat) : CfgSlot tm H :=
  .inl ()

/-- One finite-control label coordinate, including the reserved halted label. -/
def label {tm : _root_.Turing.FinTM2} {H : Nat}
    (i : Fin (labelCount tm + 1)) : CfgSlot tm H :=
  .inr (.inl i)

/-- One internal-state coordinate. -/
def state {tm : _root_.Turing.FinTM2} {H : Nat}
    (i : Fin (stateCount tm)) : CfgSlot tm H :=
  .inr (.inr (.inl i))

/-- One stack-height coordinate. -/
def stackHeight {tm : _root_.Turing.FinTM2} {H : Nat}
    (k : tm.K) (i : Fin (H + 1)) : CfgSlot tm H :=
  .inr (.inr (.inr ⟨k, .inl i⟩))

/-- One physical stack-cell symbol coordinate, including the blank symbol. -/
def stackCell {tm : _root_.Turing.FinTM2} {H : Nat}
    (k : tm.K) (i : Fin H)
    (a : Fin ((reachableAlphabet tm k).card + 1)) : CfgSlot tm H :=
  .inr (.inr (.inr ⟨k, .inr (i, a)⟩))

end CfgSlot

/-- Exact Boolean width of one bounded configuration row. -/
noncomputable def cfgBitCount (tm : _root_.Turing.FinTM2) (H : Nat) : Nat := by
  letI : Fintype tm.K := tm.kFin
  exact 1 + (labelCount tm + 1) + stateCount tm +
    ∑ k : tm.K,
      ((H + 1) + H * ((reachableAlphabet tm k).card + 1))

noncomputable instance cfgSlotFintype (tm : _root_.Turing.FinTM2) (H : Nat) :
    Fintype (CfgSlot tm H) := by
  letI := tm.kFin
  infer_instance

noncomputable instance cfgSlotDecidableEq (tm : _root_.Turing.FinTM2) (H : Nat) :
    DecidableEq (CfgSlot tm H) := Classical.decEq _

/-- The unified slot type has exactly the advertised row width. -/
theorem card_cfgSlot (tm : _root_.Turing.FinTM2) (H : Nat) :
    Fintype.card (CfgSlot tm H) = cfgBitCount tm H := by
  letI := tm.kFin
  simp [CfgSlot, cfgBitCount, Nat.add_assoc]

/-- Number of Boolean coordinates occupied by one bounded machine stack. -/
def cfgStackBitWidth (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) : Nat :=
  (H + 1) + H * ((reachableAlphabet tm k).card + 1)

/-- Prefix occupied by stacks preceding `k` in the fixed machine-stack
numbering.  Only the fixed verifier contributes the stack ordering; the
runtime height enters through the explicit affine stack widths. -/
noncomputable def cfgStackBitOffset (tm : _root_.Turing.FinTM2)
    (H : Nat) (k : tm.K) : Nat := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  exact ∑ j : Fin (keyEquiv k),
    cfgStackBitWidth tm H
      (keyEquiv.symm (Fin.castLE (keyEquiv k).isLt.le j))

/-- Explicit local numbering of height bits followed by cell-symbol bits for
one stack. -/
private noncomputable def cfgStackLocalEquivFin
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K) :
    (Fin (H + 1) ⊕
      (Fin H × Fin ((reachableAlphabet tm k).card + 1))) ≃
        Fin (cfgStackBitWidth tm H k) :=
  ((Equiv.refl (Fin (H + 1))).sumCongr finProdFinEquiv).trans
    finSumFinEquiv

/-- Reindex dependent stack blocks by the fixed machine-stack enumeration.
The explicit casts preserve the local numeric coordinate. -/
private noncomputable def cfgKeySigmaEquiv
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (Σ k : tm.K, Fin (cfgStackBitWidth tm H k)) ≃
      (Σ j : Fin (Fintype.card tm.K),
        Fin (cfgStackBitWidth tm H ((Fintype.equivFin tm.K).symm j))) := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  exact
    { toFun := fun x =>
        ⟨keyEquiv x.1,
          Fin.cast (by rw [keyEquiv.symm_apply_apply]) x.2⟩
      invFun := fun x => ⟨keyEquiv.symm x.1, x.2⟩
      left_inv := by
        rintro ⟨k, i⟩
        dsimp
        let hkey := keyEquiv.symm_apply_apply k
        apply Sigma.ext hkey
        exact (Fin.heq_ext_iff
          (congrArg (cfgStackBitWidth tm H) hkey)).2 rfl
      right_inv := by
        rintro ⟨j, i⟩
        dsimp
        let hkey := keyEquiv.apply_symm_apply j
        apply Sigma.ext hkey
        exact (Fin.heq_ext_iff
          (congrArg (fun q => cfgStackBitWidth tm H (keyEquiv.symm q))
            hkey)).2 rfl }

@[simp] private theorem cfgKeySigmaEquiv_apply_fst
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K)
    (i : Fin (cfgStackBitWidth tm H k)) :
    (cfgKeySigmaEquiv tm H ⟨k, i⟩).1 = Fintype.equivFin tm.K k := rfl

@[simp] private theorem cfgKeySigmaEquiv_apply_snd_val
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K)
    (i : Fin (cfgStackBitWidth tm H k)) :
    (cfgKeySigmaEquiv tm H ⟨k, i⟩).2.val = i.val := by
  rfl

@[simp] private theorem cfgStackLocalEquivFin_height_val
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K)
    (i : Fin (H + 1)) :
    (cfgStackLocalEquivFin tm H k (.inl i)).val = i.val := rfl

@[simp] private theorem cfgStackLocalEquivFin_cell_val
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K)
    (i : Fin H) (a : Fin ((reachableAlphabet tm k).card + 1)) :
    (cfgStackLocalEquivFin tm H k (.inr (i, a))).val =
      (H + 1) + (a.val + ((reachableAlphabet tm k).card + 1) * i.val) := rfl

/-- Explicit numbering of all stack coordinates, using the fixed verifier's
finite stack numbering and runtime-computable affine block widths. -/
private noncomputable def cfgStacksEquivFin
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (Σ k : tm.K, Fin (H + 1) ⊕
      (Fin H × Fin ((reachableAlphabet tm k).card + 1))) ≃
        Fin (∑ k : tm.K, cfgStackBitWidth tm H k) := by
  letI : Fintype tm.K := tm.kFin
  let keyEquiv : tm.K ≃ Fin (Fintype.card tm.K) := Fintype.equivFin tm.K
  exact
    (Equiv.sigmaCongrRight (fun k => cfgStackLocalEquivFin tm H k)).trans <|
      (cfgKeySigmaEquiv tm H).trans <|
        finSigmaFinEquiv.trans <|
          finCongr (keyEquiv.symm.sum_comp
            (fun k => cfgStackBitWidth tm H k))

@[simp] private theorem cfgStacksEquivFin_apply_val
    (tm : _root_.Turing.FinTM2) (H : Nat) (k : tm.K)
    (i : Fin (H + 1) ⊕
      (Fin H × Fin ((reachableAlphabet tm k).card + 1))) :
    (cfgStacksEquivFin tm H ⟨k, i⟩).val =
      cfgStackBitOffset tm H k + (cfgStackLocalEquivFin tm H k i).val := by
  simp [cfgStacksEquivFin, cfgStackBitOffset, finSigmaFinEquiv_apply]
  congr

/-- Canonical finite numbering of all row coordinates.

Unlike an unconstrained `Fintype.equivFin`, this numbering is uniform in the
runtime height: halted, label, state, stack-height, and stack-cell blocks have
literal arithmetic offsets.  The only chosen enumeration belongs to the fixed
machine's finite stack type and can therefore live in TM2 finite control. -/
noncomputable def cfgSlotEquivFin (tm : _root_.Turing.FinTM2) (H : Nat) :
    CfgSlot tm H ≃ Fin (cfgBitCount tm H) := by
  let stackEquiv := cfgStacksEquivFin tm H
  let stateAndStacks :=
    ((Equiv.refl (Fin (stateCount tm))).sumCongr stackEquiv).trans
      finSumFinEquiv
  let labelStateStacks :=
    ((Equiv.refl (Fin (labelCount tm + 1))).sumCongr stateAndStacks).trans
      finSumFinEquiv
  let allSlots :=
    (((finOneEquiv : Fin 1 ≃ Unit).symm).sumCongr labelStateStacks).trans
      finSumFinEquiv
  exact allSlots.trans (finCongr (by
    simp only [cfgBitCount, cfgStackBitWidth]
    omega))

/-- The halted bit is the first coordinate of every explicit row encoding. -/
@[simp] theorem cfgSlotEquivFin_halted_val
    (tm : _root_.Turing.FinTM2) (H : Nat) :
    (cfgSlotEquivFin tm H (CfgSlot.halted tm H)).val = 0 := by
  simp [cfgSlotEquivFin, CfgSlot.halted]

/-- Label coordinates immediately follow the halted bit. -/
@[simp] theorem cfgSlotEquivFin_label_val
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (i : Fin (labelCount tm + 1)) :
    (cfgSlotEquivFin tm H (CfgSlot.label i)).val = 1 + i.val := by
  simp [cfgSlotEquivFin, CfgSlot.label]

/-- State coordinates immediately follow the halted and label blocks. -/
@[simp] theorem cfgSlotEquivFin_state_val
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (i : Fin (stateCount tm)) :
    (cfgSlotEquivFin tm H (CfgSlot.state i)).val =
      1 + (labelCount tm + 1) + i.val := by
  simp [cfgSlotEquivFin, CfgSlot.state]
  omega

/-- A stack-height coordinate has its literal outer block offset, its fixed
stack-prefix offset, and then its height index. -/
@[simp] theorem cfgSlotEquivFin_stackHeight_val
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (k : tm.K) (i : Fin (H + 1)) :
    (cfgSlotEquivFin tm H (CfgSlot.stackHeight k i)).val =
      1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k + i.val := by
  simp [cfgSlotEquivFin, CfgSlot.stackHeight]
  omega

/-- Cell-symbol coordinates follow the height block and use row-major
cell/symbol numbering inside their fixed stack block. -/
@[simp] theorem cfgSlotEquivFin_stackCell_val
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (k : tm.K) (i : Fin H)
    (a : Fin ((reachableAlphabet tm k).card + 1)) :
    (cfgSlotEquivFin tm H (CfgSlot.stackCell k i a)).val =
      1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k + (H + 1) +
          (a.val + ((reachableAlphabet tm k).card + 1) * i.val) := by
  simp [cfgSlotEquivFin, CfgSlot.stackCell]
  omega

/-! ## Bit and wire bundles -/

/-- A row-shaped bundle with a common payload type at every coordinate. -/
abbrev CfgBundle (tm : _root_.Turing.FinTM2) (H : Nat) (α : Type) :=
  CfgSlot tm H → α

/-- Internal circuit wires for one bounded row. -/
abbrev CfgWires (tm : _root_.Turing.FinTM2) (H : Nat) :=
  CfgBundle tm H CircuitBuilder.Wire

/-- Evaluated Boolean values for one bounded row. -/
abbrev CfgBits (tm : _root_.Turing.FinTM2) (H : Nat) :=
  CfgBundle tm H Bool

namespace CfgBundle

def halted {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) : α := bundle (CfgSlot.halted tm H)

def label {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (i : Fin (labelCount tm + 1)) : α :=
  bundle (CfgSlot.label i)

def state {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (i : Fin (stateCount tm)) : α :=
  bundle (CfgSlot.state i)

def stackHeight {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (k : tm.K) (i : Fin (H + 1)) : α :=
  bundle (CfgSlot.stackHeight k i)

def stackCell {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (k : tm.K) (i : Fin H)
    (a : Fin ((reachableAlphabet tm k).card + 1)) : α :=
  bundle (CfgSlot.stackCell k i a)

@[simp] theorem halted_apply {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) :
    bundle.halted = bundle (.inl ()) := rfl

@[simp] theorem label_apply {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (i : Fin (labelCount tm + 1)) :
    bundle.label i = bundle (.inr (.inl i)) := rfl

@[simp] theorem state_apply {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (i : Fin (stateCount tm)) :
    bundle.state i = bundle (.inr (.inr (.inl i))) := rfl

@[simp] theorem stackHeight_apply {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (k : tm.K) (i : Fin (H + 1)) :
    bundle.stackHeight k i = bundle (.inr (.inr (.inr ⟨k, .inl i⟩))) := rfl

@[simp] theorem stackCell_apply {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (k : tm.K) (i : Fin H)
    (a : Fin ((reachableAlphabet tm k).card + 1)) :
    bundle.stackCell k i a = bundle (.inr (.inr (.inr ⟨k, .inr (i, a)⟩))) := rfl

end CfgBundle

namespace CfgWires

/-- Every row wire refers to a gate already present in the builder. -/
def ValidIn {tm : _root_.Turing.FinTM2} {H : Nat}
    (wires : CfgWires tm H) (b : CircuitBuilder) : Prop :=
  ∀ slot, b.WireValid (wires slot)

namespace ValidIn

/-- Bundle validity is monotone under append-only circuit extension. -/
theorem mono {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {base next : CircuitBuilder}
    (hvalid : wires.ValidIn base) (hext : base.Extends next) :
    wires.ValidIn next := by
  intro slot
  exact hext.wireValid (hvalid slot)

end ValidIn

end CfgWires

/-- Evaluate every named row wire under one external-input assignment. -/
def evalCfgBits {tm : _root_.Turing.FinTM2} {H : Nat}
    (b : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H) :
    CfgBits tm H :=
  fun slot => b.evalWire inputs (wires slot)

/-- Appending gates preserves all values of an already valid row bundle. -/
theorem evalCfgBits_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    evalCfgBits next inputs wires = evalCfgBits base inputs wires := by
  funext slot
  exact hext.evalWire_eq inputs (hvalid slot)

/-! ## Fresh external-input layouts -/

/-- A tagged external input position, kept distinct from internal gate wires. -/
structure CfgInputIndex where
  val : Nat
deriving DecidableEq, Repr

/-- A consecutive block of external inputs reserved for one row. -/
structure CfgInputLayout (tm : _root_.Turing.FinTM2) (H : Nat) where
  base : Nat
deriving DecidableEq, Repr

namespace CfgInputLayout

/-- First external-input position strictly after this row. -/
def finish {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) : Nat :=
  layout.base + cfgBitCount tm H

/-- External input position assigned to a particular row coordinate. -/
def index {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (slot : CfgSlot tm H) : CfgInputIndex :=
  ⟨layout.base + (cfgSlotEquivFin tm H slot).val⟩

/-- The entire layout lies below the declared external-input arity. -/
def Fits {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (inputCount : Nat) : Prop :=
  layout.finish ≤ inputCount

/-- Two row layouts occupy nonoverlapping half-open external-input intervals. -/
def Disjoint {tm : _root_.Turing.FinTM2} {H : Nat}
    (left right : CfgInputLayout tm H) : Prop :=
  left.finish ≤ right.base ∨ right.finish ≤ left.base

/-- Every coordinate lies before the layout endpoint. -/
theorem index_lt {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (slot : CfgSlot tm H) :
    (layout.index slot).val < layout.finish := by
  change layout.base + (cfgSlotEquivFin tm H slot).val <
    layout.base + cfgBitCount tm H
  exact Nat.add_lt_add_left (cfgSlotEquivFin tm H slot).isLt layout.base

/-- Coordinate allocation inside one row is injective. -/
theorem index_injective {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) : Function.Injective layout.index := by
  intro left right heq
  have hval : (cfgSlotEquivFin tm H left).val =
      (cfgSlotEquivFin tm H right).val := by
    simpa [index] using congrArg CfgInputIndex.val heq
  exact (cfgSlotEquivFin tm H).injective (Fin.ext hval)

/-- Consecutive row layout starting at the current endpoint. -/
def next {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) : CfgInputLayout tm H :=
  ⟨layout.finish⟩

/-- A row and its consecutive successor are disjoint. -/
theorem next_disjoint {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) : layout.Disjoint layout.next :=
  Or.inl (Nat.le_refl _)

/-- Coordinates from disjoint layouts always receive distinct external inputs. -/
theorem index_ne_of_disjoint {tm : _root_.Turing.FinTM2} {H : Nat}
    {left right : CfgInputLayout tm H} (hdisjoint : left.Disjoint right)
    (leftSlot rightSlot : CfgSlot tm H) :
    left.index leftSlot ≠ right.index rightSlot := by
  intro heq
  have hval := congrArg CfgInputIndex.val heq
  rcases hdisjoint with hbefore | hbefore
  · have hleft := left.index_lt leftSlot
    have hrightBase : right.base ≤ (right.index rightSlot).val := by
      simp [index]
    omega
  · have hright := right.index_lt rightSlot
    have hleftBase : left.base ≤ (left.index leftSlot).val := by
      simp [index]
    omega

/-- Recover a row coordinate exactly on this layout's half-open interval. -/
def decodeIndex {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (inputIndex : Nat) : Option (CfgSlot tm H) :=
  if h : layout.base ≤ inputIndex ∧ inputIndex < layout.finish then
    some ((cfgSlotEquivFin tm H).symm
      ⟨inputIndex - layout.base, by
        unfold finish at h
        omega⟩)
  else none

/-- Decoding an allocated coordinate recovers that coordinate. -/
theorem decodeIndex_index {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (slot : CfgSlot tm H) :
    layout.decodeIndex (layout.index slot).val = some slot := by
  simp only [decodeIndex]
  rw [dif_pos]
  · congr 1
    apply (cfgSlotEquivFin tm H).injective
    apply Fin.ext
    simp [index]
  · constructor
    · simp [index]
    · exact layout.index_lt slot

/-- Patch one row's bits into an arbitrary total external-input assignment. -/
def writeCfgBits {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (bits : CfgBits tm H) : Nat → Bool :=
  fun inputIndex =>
    match layout.decodeIndex inputIndex with
    | some slot => bits slot
    | none => assignment inputIndex

/-- Reading a patched coordinate yields precisely the supplied row bit. -/
theorem writeCfgBits_at {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (bits : CfgBits tm H) (slot : CfgSlot tm H) :
    layout.writeCfgBits assignment bits (layout.index slot).val = bits slot := by
  simp [writeCfgBits, decodeIndex_index]

/-- Patching leaves every input outside the layout interval unchanged. -/
theorem writeCfgBits_outside {tm : _root_.Turing.FinTM2} {H : Nat}
    (layout : CfgInputLayout tm H) (assignment : Nat → Bool)
    (bits : CfgBits tm H) {inputIndex : Nat}
    (houtside : inputIndex < layout.base ∨ layout.finish ≤ inputIndex) :
    layout.writeCfgBits assignment bits inputIndex = assignment inputIndex := by
  unfold writeCfgBits decodeIndex
  rw [dif_neg]
  omega

/-- Writing a disjoint row preserves every already written coordinate. -/
theorem writeCfgBits_index_of_disjoint {tm : _root_.Turing.FinTM2} {H : Nat}
    {left right : CfgInputLayout tm H} (hdisjoint : left.Disjoint right)
    (assignment : Nat → Bool) (leftBits rightBits : CfgBits tm H)
    (slot : CfgSlot tm H) :
    right.writeCfgBits (left.writeCfgBits assignment leftBits) rightBits
        (left.index slot).val = leftBits slot := by
  rw [right.writeCfgBits_outside, left.writeCfgBits_at]
  rcases hdisjoint with hbefore | hbefore
  · exact Or.inl (lt_of_lt_of_le (left.index_lt slot) hbefore)
  · exact Or.inr (le_trans hbefore (by simp [index]))

end CfgInputLayout

/-! ## Linear fresh-input allocation -/

/-- A proof-carrying builder result with one designated output wire. -/
structure BuiltWire (base : CircuitBuilder) where
  builder : CircuitBuilder
  wire : CircuitBuilder.Wire
  extension : base.Extends builder
  valid : builder.WireValid wire

private structure FinInputAllocation (base : CircuitBuilder)
    (inputBase n : Nat) where
  builder : CircuitBuilder
  wires : Fin n → CircuitBuilder.Wire
  extension : base.Extends builder
  valid : ∀ i, builder.WireValid (wires i)
  gate_delta : builder.gates.length = base.gates.length + n
  wire_eq : ∀ i, wires i = base.gates.length + i.val
  eval : ∀ inputs i,
    builder.evalWire inputs (wires i) = inputs (inputBase + i.val)

private def allocateFinInputs (base : CircuitBuilder) (inputBase : Nat) :
    (n : Nat) → inputBase + n ≤ base.inputCount →
      FinInputAllocation base inputBase n
  | 0, _ =>
      { builder := base
        wires := fun i => Fin.elim0 i
        extension := CircuitBuilder.Extends.refl base
        valid := fun i => Fin.elim0 i
        gate_delta := by omega
        wire_eq := fun i => Fin.elim0 i
        eval := fun _ i => Fin.elim0 i }
  | n + 1, hfits => by
      let previous := allocateFinInputs base inputBase n (by omega)
      have hinputBase : inputBase + n < base.inputCount := by omega
      have hinput : inputBase + n < previous.builder.inputCount := by
        rw [previous.extension.1]
        exact hinputBase
      let fresh := previous.builder.input (inputBase + n) hinput
      let wires : Fin (n + 1) → CircuitBuilder.Wire := fun i =>
        if hi : i.val < n then previous.wires ⟨i.val, hi⟩ else fresh.2
      refine
        { builder := fresh.1
          wires := wires
          extension := previous.extension.trans
            (CircuitBuilder.input_extends previous.builder (inputBase + n) hinput)
          valid := ?_
          gate_delta := ?_
          wire_eq := ?_
          eval := ?_ }
      · intro i
        simp only [wires]
        split
        next hi =>
          exact (CircuitBuilder.input_extends previous.builder (inputBase + n) hinput).wireValid
            (previous.valid ⟨i.val, hi⟩)
        next =>
          exact CircuitBuilder.input_wireValid previous.builder (inputBase + n) hinput
      · rw [CircuitBuilder.input_gate_delta, previous.gate_delta]
        omega
      · intro i
        simp only [wires]
        split
        next hi => exact previous.wire_eq ⟨i.val, hi⟩
        next hi =>
          have hilast : i.val = n := by omega
          change previous.builder.gates.length = base.gates.length + i.val
          rw [previous.gate_delta, hilast]
      · intro inputs i
        simp only [wires]
        split
        next hi =>
          rw [(CircuitBuilder.input_extends previous.builder (inputBase + n) hinput).evalWire_eq
            inputs (previous.valid ⟨i.val, hi⟩)]
          exact previous.eval inputs ⟨i.val, hi⟩
        next hi =>
          have hilast : i.val = n := by omega
          rw [CircuitBuilder.input_eval]
          simp [hilast]

private theorem range'_succ_append (start n : Nat) :
    List.range' start (n + 1) =
      List.range' start n ++ [start + n] := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
      change
        start :: List.range' (start + 1) (n + 1) =
          start :: (List.range' (start + 1) n ++ [start + (n + 1)])
      rw [ih (start + 1)]
      rw [show start + 1 + n = start + (n + 1) by omega]

/-- The low-level allocator appends input gates in increasing external-index
order. -/
private theorem allocateFinInputs_gates_eq (base : CircuitBuilder)
    (inputBase n : Nat) (hfit : inputBase + n ≤ base.inputCount) :
    (allocateFinInputs base inputBase n hfit).builder.gates =
      base.gates ++
        (List.range' inputBase n).map CircuitGate.input := by
  induction n with
  | zero => simp [allocateFinInputs]
  | succ n ih =>
      simp only [allocateFinInputs]
      change
        (allocateFinInputs base inputBase n (by omega)).builder.gates ++
            [.input (inputBase + n)] =
          base.gates ++
            (List.range' inputBase (n + 1)).map CircuitGate.input
      rw [show
        (allocateFinInputs base inputBase n (by omega)).builder.gates =
          base.gates ++
            (List.range' inputBase n).map CircuitGate.input by
        exact ih (by omega)]
      rw [range'_succ_append, List.map_append]
      simp [List.append_assoc]

/-- Proof-carrying result of allocating one external input gate per row slot. -/
structure CfgInputAllocation {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : CircuitBuilder) (layout : CfgInputLayout tm H) where
  builder : CircuitBuilder
  extension : start.Extends builder
  wires : CfgWires tm H
  valid : wires.ValidIn builder
  gate_delta : builder.gates.length = start.gates.length + cfgBitCount tm H
  wire_eq : ∀ slot,
    wires slot = start.gates.length + (cfgSlotEquivFin tm H slot).val
  eval_slot : ∀ inputs slot,
    builder.evalWire inputs (wires slot) = inputs (layout.index slot).val

/-- Allocate one fresh internal input gate for every external row coordinate. -/
def allocateCfgInputs {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.Fits start.inputCount) : CfgInputAllocation start layout := by
  let allocated := allocateFinInputs start layout.base (cfgBitCount tm H) hfit
  let wires : CfgWires tm H := fun slot =>
    allocated.wires (cfgSlotEquivFin tm H slot)
  exact
    { builder := allocated.builder
      extension := allocated.extension
      wires := wires
      valid := fun slot => allocated.valid (cfgSlotEquivFin tm H slot)
      gate_delta := allocated.gate_delta
      wire_eq := fun slot => allocated.wire_eq (cfgSlotEquivFin tm H slot)
      eval_slot := by
        intro inputs slot
        simpa [wires, CfgInputLayout.index] using
          allocated.eval inputs (cfgSlotEquivFin tm H slot) }

/-- Row allocation appends exactly the consecutive input-gate block described
by its external-input layout. -/
theorem allocateCfgInputs_gates_eq {tm : _root_.Turing.FinTM2} {H : Nat}
    (start : CircuitBuilder) (layout : CfgInputLayout tm H)
    (hfit : layout.Fits start.inputCount) :
    (allocateCfgInputs start layout hfit).builder.gates =
      start.gates ++
        (List.range' layout.base (cfgBitCount tm H)).map CircuitGate.input := by
  unfold allocateCfgInputs
  exact allocateFinInputs_gates_eq start layout.base (cfgBitCount tm H) hfit

namespace CfgInputAllocation

/-- Patching this layout with row bits makes every allocated wire evaluate to
the corresponding bit. -/
theorem evalCfgBits_write {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {layout : CfgInputLayout tm H}
    (allocation : CfgInputAllocation start layout)
    (assignment : Nat → Bool) (bits : CfgBits tm H) :
    evalCfgBits allocation.builder (layout.writeCfgBits assignment bits)
      allocation.wires = bits := by
  funext slot
  rw [evalCfgBits, allocation.eval_slot, layout.writeCfgBits_at]

/-- Allocated row values remain unchanged after any later builder extension. -/
theorem evalCfgBits_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {layout : CfgInputLayout tm H}
    (allocation : CfgInputAllocation start layout)
    {next : CircuitBuilder} (hext : allocation.builder.Extends next)
    (inputs : Nat → Bool) :
    evalCfgBits next inputs allocation.wires =
      evalCfgBits allocation.builder inputs allocation.wires :=
  CookLevin.evalCfgBits_extends hext inputs allocation.wires allocation.valid

end CfgInputAllocation

/-! ## Linear exactly-one circuits -/

/-- Values of a wire list under a builder assignment, retaining list positions
so repeated wire aliases remain repeated observations. -/
def wireValues (b : CircuitBuilder) (inputs : Nat → Bool)
    (wires : List CircuitBuilder.Wire) : List Bool :=
  wires.map (b.evalWire inputs)

/-- Position-sensitive absence of two true entries. -/
def AtMostOneTrue (values : List Bool) : Prop :=
  values.Pairwise (fun left right => left = false ∨ right = false)

private def duplicateTrue : List Bool → Bool
  | [] => false
  | value :: values => duplicateTrue values || (values.any id && value)

private theorem duplicateTrue_eq_false_iff (values : List Bool) :
    duplicateTrue values = false ↔ AtMostOneTrue values := by
  induction values with
  | nil => simp [duplicateTrue, AtMostOneTrue]
  | cons value values ih =>
      cases value <;>
        simp [duplicateTrue, AtMostOneTrue, ih, List.any_eq_false, and_comm]

private theorem mem_and_atMostOneTrue_iff_count_eq_one (values : List Bool) :
    true ∈ values ∧ AtMostOneTrue values ↔ values.count true = 1 := by
  induction values with
  | nil => simp [AtMostOneTrue]
  | cons value values ih =>
      cases value with
      | false =>
        simpa [AtMostOneTrue] using ih
      | true =>
        simp only [List.mem_cons, true_or, true_and, AtMostOneTrue,
          List.pairwise_cons, Bool.true_eq_false, false_or,
          List.count_cons_self]
        constructor
        · rintro ⟨hall, hpairwise⟩
          have hzero : values.count true = 0 := by
            rw [List.count_eq_zero]
            intro hmem
            exact (by decide : true ≠ false) (hall true hmem)
          omega
        · intro hcount
          have hzero : values.count true = 0 := by omega
          have hall : ∀ value ∈ values, value ≠ true := by
            simpa [List.count_eq_zero] using hzero
          exact ⟨fun value hvalue => Bool.eq_false_of_not_eq_true
            (hall value hvalue), by
              rw [List.pairwise_iff_get]
              intro i j _
              left
              exact Bool.eq_false_of_not_eq_true
                (hall (values.get i) (List.get_mem values i))⟩

/-! ### Exact gate trace for the exactly-one scan -/

/-- Pure gate-order trace of the public {lit}`exactlyOne` builder.  The starting
index is the length of the builder prefix to which the trace will be
appended. -/
structure ExactlyOneGateTrace where
  gates : List CircuitGate
  wire : CircuitBuilder.Wire
deriving DecidableEq, Repr

private structure ExactlyOneScanGateTrace where
  gates : List CircuitGate
  seen : CircuitBuilder.Wire
  duplicate : CircuitBuilder.Wire

/-- Pure trace of the tail-first seen/duplicate scan. -/
private def exactlyOneScanGateTrace (start : Nat) :
    List CircuitBuilder.Wire → ExactlyOneScanGateTrace
  | [] =>
      { gates := [.const false, .const false]
        seen := start
        duplicate := start + 1 }
  | wire :: rest =>
      let tail := exactlyOneScanGateTrace start rest
      let next := start + tail.gates.length
      { gates := tail.gates ++
          [.and tail.seen wire, .or tail.duplicate next,
            .or tail.seen wire]
        seen := next + 2
        duplicate := next + 1 }

private theorem exactlyOneScanGateTrace_length (start : Nat)
    (wires : List CircuitBuilder.Wire) :
    (exactlyOneScanGateTrace start wires).gates.length =
      3 * wires.length + 2 := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [exactlyOneScanGateTrace, ih]
      omega

/-- Exact primitive-gate sequence emitted by `exactlyOne`. -/
def exactlyOneGateTrace (start : Nat)
    (wires : List CircuitBuilder.Wire) : ExactlyOneGateTrace :=
  let scan := exactlyOneScanGateTrace start wires
  let next := start + scan.gates.length
  { gates := scan.gates ++ [.not scan.duplicate, .and scan.seen next]
    wire := next + 1 }

/-- The pure exactly-one trace contains exactly {lit}`3*n+4` gates. -/
@[simp] theorem exactlyOneGateTrace_length (start : Nat)
    (wires : List CircuitBuilder.Wire) :
    (exactlyOneGateTrace start wires).gates.length = 3 * wires.length + 4 := by
  simp [exactlyOneGateTrace, exactlyOneScanGateTrace_length]

/-- The output of an exactly-one block is its last fresh gate.  This closed
index is the arithmetic interface used by uniform serializers of families of
exactly-one constraints. -/
@[simp] theorem exactlyOneGateTrace_wire (start : Nat)
    (wires : List CircuitBuilder.Wire) :
    (exactlyOneGateTrace start wires).wire =
      start + 3 * wires.length + 3 := by
  simp [exactlyOneGateTrace, exactlyOneScanGateTrace_length]
  omega

/-! The fold presentation below is the executable view used by the concrete
serializer.  It is intentionally public: clients do not need access to the
private proof-oriented scan record in order to enumerate the exact trace. -/

/-- Arithmetic scan state for forward execution over the reversed wire list. -/
structure ExactlyOneArithmeticScan where
  gates : List CircuitGate
  seen : CircuitBuilder.Wire
  duplicate : CircuitBuilder.Wire
deriving DecidableEq, Repr

/-- One forward scan update at the next source wire. -/
def exactlyOneArithmeticStep (start : Nat)
    (scan : ExactlyOneArithmeticScan) (wire : CircuitBuilder.Wire) :
    ExactlyOneArithmeticScan :=
  let next := start + scan.gates.length
  { gates := scan.gates ++
      [.and scan.seen wire, .or scan.duplicate next,
        .or scan.seen wire]
    seen := next + 2
    duplicate := next + 1 }

/-- Tail-first exactly-one scanning as a left fold over reversed wires. -/
def exactlyOneArithmeticScan (start : Nat)
    (wires : List CircuitBuilder.Wire) : ExactlyOneArithmeticScan :=
  wires.reverse.foldl (exactlyOneArithmeticStep start)
    { gates := [.const false, .const false]
      seen := start
      duplicate := start + 1 }

private theorem exactlyOneScanGateTrace_eq_arithmeticScan
    (start : Nat) (wires : List CircuitBuilder.Wire) :
    (exactlyOneScanGateTrace start wires).gates =
        (exactlyOneArithmeticScan start wires).gates ∧
      (exactlyOneScanGateTrace start wires).seen =
        (exactlyOneArithmeticScan start wires).seen ∧
      (exactlyOneScanGateTrace start wires).duplicate =
        (exactlyOneArithmeticScan start wires).duplicate := by
  induction wires with
  | nil => simp [exactlyOneScanGateTrace, exactlyOneArithmeticScan]
  | cons wire rest ih =>
      rcases ih with ⟨hgates, hseen, hduplicate⟩
      simp only [exactlyOneArithmeticScan, List.reverse_cons,
        List.foldl_append]
      simp only [exactlyOneScanGateTrace]
      rw [hgates, hseen, hduplicate]
      simp only [List.foldl]
      change
        _ = (exactlyOneArithmeticStep start
              (exactlyOneArithmeticScan start rest) wire).gates ∧
          _ = (exactlyOneArithmeticStep start
              (exactlyOneArithmeticScan start rest) wire).seen ∧
          _ = (exactlyOneArithmeticStep start
              (exactlyOneArithmeticScan start rest) wire).duplicate
      simp [exactlyOneArithmeticStep]

/-- The public arithmetic fold emits exactly the same gates as the semantic
tail-recursive trace. -/
theorem exactlyOneGateTrace_gates_eq_arithmeticScan
    (start : Nat) (wires : List CircuitBuilder.Wire) :
    (exactlyOneGateTrace start wires).gates =
      (exactlyOneArithmeticScan start wires).gates ++
        [.not (exactlyOneArithmeticScan start wires).duplicate,
          .and (exactlyOneArithmeticScan start wires).seen
            (start + (exactlyOneArithmeticScan start wires).gates.length)] := by
  rcases exactlyOneScanGateTrace_eq_arithmeticScan start wires with
    ⟨hgates, hseen, hduplicate⟩
  simp only [exactlyOneGateTrace]
  rw [hgates, hseen, hduplicate]

private structure ExactlyOneScan (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire) where
  builder : CircuitBuilder
  seen : CircuitBuilder.Wire
  duplicate : CircuitBuilder.Wire
  extension : base.Extends builder
  seenValid : builder.WireValid seen
  duplicateValid : builder.WireValid duplicate
  gate_delta : builder.gates.length = base.gates.length + 3 * wires.length + 2
  seen_eval : ∀ inputs,
    builder.evalWire inputs seen = (wireValues base inputs wires).any id
  duplicate_eval : ∀ inputs,
    builder.evalWire inputs duplicate = duplicateTrue (wireValues base inputs wires)

private def exactlyOneScan (base : CircuitBuilder) :
    (wires : List CircuitBuilder.Wire) →
      (∀ wire ∈ wires, base.WireValid wire) → ExactlyOneScan base wires
  | [], _ => by
      let seen := base.const false
      let duplicate := seen.1.const false
      let hextSeen := CircuitBuilder.const_extends base false
      let hextDuplicate := CircuitBuilder.const_extends seen.1 false
      refine
        { builder := duplicate.1
          seen := seen.2
          duplicate := duplicate.2
          extension := hextSeen.trans hextDuplicate
          seenValid := hextDuplicate.wireValid
            (CircuitBuilder.const_wireValid base false)
          duplicateValid := CircuitBuilder.const_wireValid seen.1 false
          gate_delta := ?_
          seen_eval := ?_
          duplicate_eval := ?_ }
      · rw [CircuitBuilder.const_gate_delta, CircuitBuilder.const_gate_delta]
        simp
      · intro inputs
        rw [hextDuplicate.evalWire_eq inputs
          (CircuitBuilder.const_wireValid base false)]
        exact CircuitBuilder.const_eval base false inputs
      · intro inputs
        exact CircuitBuilder.const_eval seen.1 false inputs
  | wire :: rest, hvalid => by
      let tail := exactlyOneScan base rest
        (fun old hold => hvalid old (by simp [hold]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      let both := tail.builder.and tail.seen wire tail.seenValid hwire
      let hextBoth := CircuitBuilder.and_extends tail.builder tail.seen wire
        tail.seenValid hwire
      let hduplicateBoth := hextBoth.wireValid tail.duplicateValid
      let duplicateNext := both.1.or tail.duplicate both.2 hduplicateBoth
        (CircuitBuilder.and_wireValid tail.builder tail.seen wire
          tail.seenValid hwire)
      let hextDuplicate := CircuitBuilder.or_extends both.1 tail.duplicate both.2
        hduplicateBoth (CircuitBuilder.and_wireValid tail.builder tail.seen wire
          tail.seenValid hwire)
      let hextToDuplicate := hextBoth.trans hextDuplicate
      let hseenDuplicate := hextToDuplicate.wireValid tail.seenValid
      let hwireDuplicate := hextToDuplicate.wireValid hwire
      let seenNext := duplicateNext.1.or tail.seen wire hseenDuplicate hwireDuplicate
      let hextSeen := CircuitBuilder.or_extends duplicateNext.1 tail.seen wire
        hseenDuplicate hwireDuplicate
      refine
        { builder := seenNext.1
          seen := seenNext.2
          duplicate := duplicateNext.2
          extension := tail.extension.trans (hextToDuplicate.trans hextSeen)
          seenValid := CircuitBuilder.or_wireValid duplicateNext.1 tail.seen wire
            hseenDuplicate hwireDuplicate
          duplicateValid := hextSeen.wireValid
            (CircuitBuilder.or_wireValid both.1 tail.duplicate both.2
              hduplicateBoth (CircuitBuilder.and_wireValid tail.builder tail.seen wire
                tail.seenValid hwire))
          gate_delta := ?_
          seen_eval := ?_
          duplicate_eval := ?_ }
      · rw [CircuitBuilder.or_gate_delta, CircuitBuilder.or_gate_delta,
          CircuitBuilder.and_gate_delta, tail.gate_delta]
        simp only [List.length_cons]
        omega
      · intro inputs
        rw [CircuitBuilder.or_eval duplicateNext.1 tail.seen wire
          hseenDuplicate hwireDuplicate]
        rw [hextToDuplicate.evalWire_eq inputs tail.seenValid]
        rw [hextToDuplicate.evalWire_eq inputs hwire]
        rw [tail.seen_eval]
        rw [tail.extension.evalWire_eq inputs (hvalid wire (by simp))]
        simp [wireValues, Bool.or_comm]
      · intro inputs
        rw [hextSeen.evalWire_eq inputs
          (CircuitBuilder.or_wireValid both.1 tail.duplicate both.2
            hduplicateBoth (CircuitBuilder.and_wireValid tail.builder tail.seen wire
              tail.seenValid hwire))]
        rw [CircuitBuilder.or_eval both.1 tail.duplicate both.2 hduplicateBoth
          (CircuitBuilder.and_wireValid tail.builder tail.seen wire tail.seenValid hwire)]
        rw [hextBoth.evalWire_eq inputs tail.duplicateValid]
        rw [CircuitBuilder.and_eval tail.builder tail.seen wire tail.seenValid hwire]
        rw [tail.duplicate_eval, tail.seen_eval]
        rw [tail.extension.evalWire_eq inputs (hvalid wire (by simp))]
        simp [wireValues, duplicateTrue]

private theorem exactlyOneScan_gates_eq (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    (exactlyOneScan base wires hvalid).builder.gates =
        base.gates ++ (exactlyOneScanGateTrace base.gates.length wires).gates ∧
      (exactlyOneScan base wires hvalid).seen =
        (exactlyOneScanGateTrace base.gates.length wires).seen ∧
      (exactlyOneScan base wires hvalid).duplicate =
        (exactlyOneScanGateTrace base.gates.length wires).duplicate := by
  induction wires with
  | nil =>
      simp [exactlyOneScan, exactlyOneScanGateTrace,
        CircuitBuilder.const_wire_eq]
  | cons wire rest ih =>
      let hrest : ∀ old ∈ rest, base.WireValid old :=
        fun old hold => hvalid old (by simp [hold])
      have htail := ih hrest
      rcases htail with ⟨hgates, hseen, hduplicate⟩
      simp only [exactlyOneScan]
      rw [CircuitBuilder.or_gates, CircuitBuilder.or_gates,
        CircuitBuilder.and_gates, hgates]
      simp only [CircuitBuilder.and_wire_eq, CircuitBuilder.or_wire_eq,
        CircuitBuilder.and_gates, CircuitBuilder.or_gates, hgates,
        List.length_append, List.length_singleton]
      simp only [exactlyOneScanGateTrace]
      rw [hseen, hduplicate]
      rw [exactlyOneScanGateTrace_length]
      constructor
      · simp [List.append_assoc]
      · constructor <;> simp

/-- Build a linear exactly-one test over wire positions.  Two occurrences of
the same true wire count as two selected positions. -/
def exactlyOne (base : CircuitBuilder) (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) : BuiltWire base := by
  let scan := exactlyOneScan base wires hvalid
  let notDuplicate := scan.builder.not scan.duplicate scan.duplicateValid
  let hextNot := CircuitBuilder.not_extends scan.builder scan.duplicate
    scan.duplicateValid
  let hseen := hextNot.wireValid scan.seenValid
  let hnotDuplicate := CircuitBuilder.not_wireValid scan.builder scan.duplicate
    scan.duplicateValid
  let output := notDuplicate.1.and scan.seen notDuplicate.2 hseen hnotDuplicate
  exact
    { builder := output.1
      wire := output.2
      extension := scan.extension.trans (hextNot.trans
        (CircuitBuilder.and_extends notDuplicate.1 scan.seen notDuplicate.2
          hseen hnotDuplicate))
      valid := CircuitBuilder.and_wireValid notDuplicate.1 scan.seen notDuplicate.2
        hseen hnotDuplicate }

/-- The proof-carrying exactly-one builder appends precisely the public pure
trace, gate for gate. -/
theorem exactlyOne_gates_eq (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    (exactlyOne base wires hvalid).builder.gates =
      base.gates ++ (exactlyOneGateTrace base.gates.length wires).gates := by
  rcases exactlyOneScan_gates_eq base wires hvalid with
    ⟨hgates, hseen, hduplicate⟩
  unfold exactlyOne
  dsimp only
  rw [CircuitBuilder.and_gates, CircuitBuilder.not_gates, hgates]
  simp only [CircuitBuilder.not_wire_eq]
  simp only [exactlyOneGateTrace]
  rw [hseen, hduplicate]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [hgates]
  simp

/-- The exactly-one output wire is the last wire advertised by its pure
trace. -/
theorem exactlyOne_wire_eq_trace (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    (exactlyOne base wires hvalid).wire =
      (exactlyOneGateTrace base.gates.length wires).wire := by
  rcases exactlyOneScan_gates_eq base wires hvalid with
    ⟨hgates, hseen, hduplicate⟩
  unfold exactlyOne
  dsimp only
  simp only [CircuitBuilder.and_wire_eq, exactlyOneGateTrace]
  rw [CircuitBuilder.not_gates, hgates]
  simp only [List.length_append, List.length_singleton]

/-- Exactly-one construction extends its starting builder. -/
theorem exactlyOne_extends (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    base.Extends (exactlyOne base wires hvalid).builder :=
  (exactlyOne base wires hvalid).extension

/-- Exactly-one construction returns a valid output wire. -/
theorem exactlyOne_wireValid (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    (exactlyOne base wires hvalid).builder.WireValid
      (exactlyOne base wires hvalid).wire :=
  (exactlyOne base wires hvalid).valid

/-- The linear seen/duplicate implementation uses exactly {lit}`3*n+4` gates. -/
theorem exactlyOne_gate_delta (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    (exactlyOne base wires hvalid).builder.gates.length =
      base.gates.length + 3 * wires.length + 4 := by
  unfold exactlyOne
  dsimp only
  rw [CircuitBuilder.and_gate_delta, CircuitBuilder.not_gate_delta,
    (exactlyOneScan base wires hvalid).gate_delta]

/-- Exact position-sensitive semantics of the linear exactly-one circuit. -/
theorem exactlyOne_eval_iff (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire)
    (inputs : Nat → Bool) :
    (exactlyOne base wires hvalid).builder.evalWire inputs
        (exactlyOne base wires hvalid).wire = true ↔
      (wireValues base inputs wires).count true = 1 := by
  unfold exactlyOne
  dsimp only
  let scan := exactlyOneScan base wires hvalid
  let notDuplicate := scan.builder.not scan.duplicate scan.duplicateValid
  let hextNot := CircuitBuilder.not_extends scan.builder scan.duplicate
    scan.duplicateValid
  let hseen := hextNot.wireValid scan.seenValid
  let hnotDuplicate := CircuitBuilder.not_wireValid scan.builder scan.duplicate
    scan.duplicateValid
  rw [CircuitBuilder.and_eval notDuplicate.1 scan.seen notDuplicate.2
    hseen hnotDuplicate]
  rw [hextNot.evalWire_eq inputs scan.seenValid]
  rw [CircuitBuilder.not_eval scan.builder scan.duplicate scan.duplicateValid]
  rw [scan.seen_eval, scan.duplicate_eval]
  rw [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
    duplicateTrue_eq_false_iff]
  rw [List.any_eq_true]
  simpa using mem_and_atMostOneTrue_iff_count_eq_one
    (wireValues base inputs wires)

/-- Repeating the same valid true wire twice is rejected as two selected
positions, rather than collapsed as one wire identity. -/
theorem exactlyOne_rejects_aliased_pair (base : CircuitBuilder)
    (wire : CircuitBuilder.Wire) (hvalid : base.WireValid wire)
    (inputs : Nat → Bool) (htrue : base.evalWire inputs wire = true) :
    (exactlyOne base [wire, wire] (by simpa using hvalid)).builder.evalWire inputs
        (exactlyOne base [wire, wire] (by simpa using hvalid)).wire = false := by
  apply Bool.eq_false_of_not_eq_true
  rw [exactlyOne_eval_iff]
  simp [wireValues, htrue]

/-! ## Linear suffix-OR masks -/

/-- Pure gate-order trace of a suffix-OR scan, including the carry and every
position-aligned output wire. -/
structure SuffixOrGateTrace (n : Nat) where
  gates : List CircuitGate
  carry : CircuitBuilder.Wire
  outputs : Fin n → CircuitBuilder.Wire

/-- Tail-first primitive-gate trace of the suffix-OR implementation. -/
def suffixOrGateTrace (start : Nat) :
    (wires : List CircuitBuilder.Wire) → SuffixOrGateTrace wires.length
  | [] =>
      { gates := [.const false]
        carry := start
        outputs := fun i => Fin.elim0 i }
  | wire :: rest =>
      let tail := suffixOrGateTrace start rest
      let next := start + tail.gates.length
      { gates := tail.gates ++ [.or tail.carry wire]
        carry := next
        outputs := fun i =>
          if hi : i.val = 0 then next
          else tail.outputs ⟨i.val - 1, by
            have hiLt : i.val < rest.length + 1 := by simpa using i.isLt
            omega⟩ }

/-- A suffix-OR trace contains its false seed and one OR per source wire. -/
@[simp] theorem suffixOrGateTrace_length (start : Nat)
    (wires : List CircuitBuilder.Wire) :
    (suffixOrGateTrace start wires).gates.length = wires.length + 1 := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
      simp [suffixOrGateTrace, ih]

/-- A tail-first linear suffix-OR scan. -/
structure SuffixOrResult (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire) where
  builder : CircuitBuilder
  carry : CircuitBuilder.Wire
  outputs : Fin wires.length → CircuitBuilder.Wire
  extension : base.Extends builder
  carryValid : builder.WireValid carry
  outputsValid : ∀ i, builder.WireValid (outputs i)
  gate_delta : builder.gates.length = base.gates.length + wires.length + 1
  carry_eval : ∀ inputs,
    builder.evalWire inputs carry = (wireValues base inputs wires).any id
  outputs_eval : ∀ inputs i,
    builder.evalWire inputs (outputs i) =
      (wireValues base inputs (wires.drop i.val)).any id

private def suffixOrScan (base : CircuitBuilder) :
    (wires : List CircuitBuilder.Wire) →
      (∀ wire ∈ wires, base.WireValid wire) → SuffixOrResult base wires
  | [], _ => by
      let seed := base.const false
      refine
        { builder := seed.1
          carry := seed.2
          outputs := fun i => Fin.elim0 i
          extension := CircuitBuilder.const_extends base false
          carryValid := CircuitBuilder.const_wireValid base false
          outputsValid := fun i => Fin.elim0 i
          gate_delta := by
            rw [CircuitBuilder.const_gate_delta]
            simp
          carry_eval := ?_
          outputs_eval := fun _ i => Fin.elim0 i }
      intro inputs
      simpa [wireValues] using CircuitBuilder.const_eval base false inputs
  | wire :: rest, hvalid => by
      let tail := suffixOrScan base rest
        (fun old hold => hvalid old (by simp [hold]))
      have hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      let next := tail.builder.or tail.carry wire tail.carryValid hwire
      let hext := CircuitBuilder.or_extends tail.builder tail.carry wire
        tail.carryValid hwire
      let outputs : Fin (wire :: rest).length → CircuitBuilder.Wire := fun i =>
        if hi : i.val = 0 then next.2
        else tail.outputs ⟨i.val - 1, by
          have hiLt : i.val < rest.length + 1 := by simpa using i.isLt
          omega⟩
      refine
        { builder := next.1
          carry := next.2
          outputs := outputs
          extension := tail.extension.trans hext
          carryValid := CircuitBuilder.or_wireValid tail.builder tail.carry wire
            tail.carryValid hwire
          outputsValid := ?_
          gate_delta := ?_
          carry_eval := ?_
          outputs_eval := ?_ }
      · intro i
        simp only [outputs]
        split
        next =>
          exact CircuitBuilder.or_wireValid tail.builder tail.carry wire
            tail.carryValid hwire
        next =>
          exact hext.wireValid (tail.outputsValid ⟨i.val - 1, by
            have hiLt : i.val < rest.length + 1 := by simpa using i.isLt
            omega⟩)
      · rw [CircuitBuilder.or_gate_delta, tail.gate_delta]
        simp only [List.length_cons]
        omega
      · intro inputs
        rw [CircuitBuilder.or_eval tail.builder tail.carry wire
          tail.carryValid hwire]
        rw [tail.carry_eval]
        rw [tail.extension.evalWire_eq inputs (hvalid wire (by simp))]
        simp [wireValues, Bool.or_comm]
      · intro inputs i
        simp only [outputs]
        split
        next hi =>
          rw [CircuitBuilder.or_eval tail.builder tail.carry wire
            tail.carryValid hwire]
          rw [tail.carry_eval]
          rw [tail.extension.evalWire_eq inputs (hvalid wire (by simp))]
          simp [wireValues, hi, Bool.or_comm]
        next hi =>
          rw [hext.evalWire_eq inputs (tail.outputsValid ⟨i.val - 1, by
            have hiLt : i.val < rest.length + 1 := by simpa using i.isLt
            omega⟩)]
          rw [tail.outputs_eval]
          have hdrop : (wire :: rest).drop i.val = rest.drop (i.val - 1) := by
            have hsucc : i.val = Nat.succ (i.val - 1) := by omega
            rw [hsucc, List.drop_succ_cons]
            simp
          rw [hdrop]

private theorem suffixOrScan_trace_eq (base : CircuitBuilder)
    (wires : List CircuitBuilder.Wire)
    (hvalid : ∀ wire ∈ wires, base.WireValid wire) :
    (suffixOrScan base wires hvalid).builder.gates =
        base.gates ++ (suffixOrGateTrace base.gates.length wires).gates ∧
      (suffixOrScan base wires hvalid).carry =
        (suffixOrGateTrace base.gates.length wires).carry ∧
      ∀ i, (suffixOrScan base wires hvalid).outputs i =
        (suffixOrGateTrace base.gates.length wires).outputs i := by
  induction wires with
  | nil =>
      simp [suffixOrScan, suffixOrGateTrace, CircuitBuilder.const_wire_eq]
  | cons wire rest ih =>
      let hrest : ∀ old ∈ rest, base.WireValid old :=
        fun old hold => hvalid old (by simp [hold])
      rcases ih hrest with ⟨hgates, hcarry, houtputs⟩
      simp only [suffixOrScan]
      rw [CircuitBuilder.or_gates, hgates]
      simp only [CircuitBuilder.or_wire_eq, suffixOrGateTrace]
      constructor
      · rw [hcarry]
        simp [List.append_assoc]
      · constructor
        · rw [hgates]
          simp
        · intro i
          split
          next hi =>
            rw [hgates]
            simp
          next hi =>
            exact houtputs _

/-- Build the active-cell suffix mask from the positive height coordinates. -/
def activeMask (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) : SuffixOrResult base
      (List.ofFn fun i : Fin H => height i.succ) :=
  suffixOrScan base (List.ofFn fun i : Fin H => height i.succ) (by
    intro wire hwire
    simp only [List.mem_ofFn] at hwire
    rcases hwire with ⟨i, rfl⟩
    exact hvalid i.succ)

/-- The active-mask builder appends exactly its pure suffix-OR gate trace. -/
theorem activeMask_gates_eq (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) :
    (activeMask base H height hvalid).builder.gates =
      base.gates ++
        (suffixOrGateTrace base.gates.length
          (List.ofFn fun i : Fin H => height i.succ)).gates :=
  (suffixOrScan_trace_eq base _ _).1

/-- The active-mask carry agrees with the pure suffix-OR trace. -/
theorem activeMask_carry_eq_trace (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) :
    (activeMask base H height hvalid).carry =
      (suffixOrGateTrace base.gates.length
        (List.ofFn fun i : Fin H => height i.succ)).carry :=
  (suffixOrScan_trace_eq base _ _).2.1

/-- Every position-aligned active-mask output agrees with the pure trace. -/
theorem activeMask_output_eq_trace (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) (i : Fin H) :
    (activeMask base H height hvalid).outputs (Fin.cast (by simp) i) =
      (suffixOrGateTrace base.gates.length
        (List.ofFn fun i : Fin H => height i.succ)).outputs
          (Fin.cast (by simp) i) :=
  (suffixOrScan_trace_eq base _ _).2.2 _

/-- The active mask uses exactly one suffix OR per cell plus its false seed. -/
theorem activeMask_gate_delta (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) :
    (activeMask base H height hvalid).builder.gates.length =
      base.gates.length + H + 1 := by
  simpa [activeMask] using (activeMask base H height hvalid).gate_delta

private theorem mem_drop_ofFn_iff {H : Nat} {alpha : Type}
    (f : Fin H → alpha) (i : Fin H) (x : alpha) :
    x ∈ (List.ofFn f).drop i.val ↔
      ∃ j : Fin H, i.val ≤ j.val ∧ f j = x := by
  constructor
  · intro hx
    rw [List.mem_iff_get] at hx
    rcases hx with ⟨j, hj⟩
    let original : Fin H := ⟨i.val + j.val, by
      have hjlt := j.isLt
      simp at hjlt
      omega⟩
    refine ⟨original, by simp [original], ?_⟩
    simpa [original] using hj
  · rintro ⟨j, hij, rfl⟩
    have hshift : j.val - i.val < ((List.ofFn f).drop i.val).length := by
      simp
      omega
    have hmem := List.getElem_mem hshift
    simp only [List.getElem_drop, List.getElem_ofFn] at hmem
    have hindex : i.val + (j.val - i.val) = j.val := by omega
    simpa [hindex] using hmem

/-- Under a one-hot height, the suffix mask is true exactly for active cells. -/
private theorem activeMask_eval_iff_lt (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) (inputs : Nat → Bool)
    (chosen : Fin (H + 1))
    (hchosen : base.evalWire inputs (height chosen) = true)
    (hunique : ∀ j, base.evalWire inputs (height j) = true → j = chosen)
    (i : Fin H) :
    let cellIndex : Fin (List.ofFn fun i : Fin H => height i.succ).length :=
      Fin.cast (by simp) i
    (activeMask base H height hvalid).builder.evalWire inputs
        ((activeMask base H height hvalid).outputs cellIndex) = true ↔
      i.val < chosen.val := by
  dsimp only
  rw [(activeMask base H height hvalid).outputs_eval]
  rw [List.any_eq_true]
  simp only [wireValues, List.mem_map]
  constructor
  · rintro ⟨value, ⟨wire, hwire, rfl⟩, htrue⟩
    simp only [Fin.val_cast] at hwire
    rw [mem_drop_ofFn_iff] at hwire
    rcases hwire with ⟨j, hij, hjwire⟩
    have hjchosen : j.succ = chosen := hunique j.succ (by
      simpa only [id_eq, hjwire] using htrue)
    have hval : j.val + 1 = chosen.val := by
      simpa using congrArg Fin.val hjchosen
    omega
  · intro hi
    let j : Fin H := ⟨chosen.val - 1, by omega⟩
    have hsucc : j.succ = chosen := by
      apply Fin.ext
      simp [j]
      omega
    refine ⟨base.evalWire inputs (height j.succ), ?_, ?_⟩
    refine ⟨height j.succ, ?_, rfl⟩
    simp only [Fin.val_cast]
    rw [mem_drop_ofFn_iff]
    refine ⟨j, by simp [j]; omega, rfl⟩
    simpa only [id_eq, hsucc] using hchosen

/-! ## Generic one-hot codes -/

/-- Exactly one coordinate of a Boolean family is selected. -/
def OneHot {ι : Type} (bits : ι → Bool) : Prop :=
  ∃ chosen, bits chosen = true ∧ ∀ i, bits i = true → i = chosen

/-- For a finite Boolean vector, one-hot selection is equivalent to exactly
one occurrence of {lit}`true` in its positional list representation. -/
theorem oneHot_iff_count_eq_one {n : Nat} (bits : Fin n → Bool) :
    OneHot bits ↔ (List.ofFn bits).count true = 1 := by
  induction n with
  | zero =>
      constructor
      · rintro ⟨chosen, _⟩
        exact Fin.elim0 chosen
      · simp
  | succ n ih =>
      rw [List.ofFn_succ, List.count_cons]
      cases hzero : bits 0 with
      | false =>
          constructor
          · rintro ⟨chosen, hchosen, hunique⟩
            have hchosenNe : chosen ≠ 0 := by
              intro heq
              subst chosen
              simp [hzero] at hchosen
            apply (ih (fun i => bits i.succ)).mp
            refine ⟨chosen.pred hchosenNe, ?_, ?_⟩
            · change bits ((chosen.pred hchosenNe).succ) = true
              rw [Fin.succ_pred chosen hchosenNe]
              exact hchosen
            · intro i hi
              apply Fin.succ_injective n
              rw [Fin.succ_pred chosen hchosenNe]
              exact hunique i.succ hi
          · intro hcount
            rcases (ih (fun i => bits i.succ)).mpr hcount with
              ⟨chosen, hchosen, hunique⟩
            refine ⟨chosen.succ, hchosen, ?_⟩
            intro i hi
            have hiNe : i ≠ 0 := by
              intro heq
              subst i
              simp [hzero] at hi
            have htail := hunique (i.pred hiNe) (by
              change bits ((i.pred hiNe).succ) = true
              rw [Fin.succ_pred i hiNe]
              exact hi)
            rw [← Fin.succ_pred i hiNe, htail]
      | true =>
          simp only [beq_self_eq_true, ↓reduceIte]
          constructor
          · rintro ⟨chosen, _, hunique⟩
            have hnone : true ∉ List.ofFn (fun i => bits i.succ) := by
              rw [List.mem_ofFn]
              rintro ⟨i, hi⟩
              have heq := hunique i.succ hi
              have hz := hunique 0 hzero
              exact Fin.succ_ne_zero i (heq.trans hz.symm)
            rw [List.count_eq_zero.mpr hnone]
          · intro hcount
            have hzeroCount :
                (List.ofFn (fun i => bits i.succ)).count true = 0 := by
              omega
            refine ⟨0, hzero, ?_⟩
            intro i hi
            by_contra hine
            have hmem : true ∈ List.ofFn (fun j => bits j.succ) := by
              rw [List.mem_ofFn]
              exact ⟨i.pred hine, by
                rwa [Fin.succ_pred i hine]⟩
            exact (List.count_eq_zero.mp hzeroCount) hmem

/-- Under a one-hot height, the linear suffix mask is true exactly below the
selected height. -/
theorem activeMask_eval_iff_lt_choose (base : CircuitBuilder) (H : Nat)
    (height : Fin (H + 1) → CircuitBuilder.Wire)
    (hvalid : ∀ i, base.WireValid (height i)) (inputs : Nat → Bool)
    (hone : OneHot (fun i => base.evalWire inputs (height i))) (i : Fin H) :
    let cellIndex : Fin (List.ofFn fun i : Fin H => height i.succ).length :=
      Fin.cast (by simp) i
    (activeMask base H height hvalid).builder.evalWire inputs
        ((activeMask base H height hvalid).outputs cellIndex) = true ↔
      i.val < hone.choose.val :=
  activeMask_eval_iff_lt base H height hvalid inputs hone.choose
    hone.choose_spec.1 hone.choose_spec.2 i

/-- Decode a unique selected coordinate, rejecting zero or multiple selections. -/
noncomputable def decodeOneHot {ι : Type} [Fintype ι]
    (bits : ι → Bool) : Option ι := by
  classical
  exact if h : OneHot bits then some h.choose else none

/-- Exact successful-decoding characterization. -/
theorem decodeOneHot_eq_some_iff {ι : Type} [Fintype ι]
    (bits : ι → Bool) (chosen : ι) :
    decodeOneHot bits = some chosen ↔
      bits chosen = true ∧ ∀ i, bits i = true → i = chosen := by
  classical
  unfold decodeOneHot
  split_ifs with h
  · constructor
    · intro heq
      have hchosen : h.choose = chosen := Option.some.inj heq
      subst chosen
      exact h.choose_spec
    · rintro ⟨hbit, hunique⟩
      congr 1
      exact hunique h.choose h.choose_spec.1
  · constructor
    · intro heq
      contradiction
    · intro hchosen
      exact False.elim (h ⟨chosen, hchosen⟩)

/-- Decoding succeeds exactly for a one-hot family. -/
theorem decodeOneHot_isSome_iff {ι : Type} [Fintype ι]
    (bits : ι → Bool) :
    (decodeOneHot bits).isSome = true ↔ OneHot bits := by
  classical
  unfold decodeOneHot
  split_ifs with h <;> simp [h]

/-- Decoding fails exactly when the family is not one-hot. -/
theorem decodeOneHot_eq_none_iff {ι : Type} [Fintype ι]
    (bits : ι → Bool) : decodeOneHot bits = none ↔ ¬ OneHot bits := by
  classical
  unfold decodeOneHot
  split_ifs with h <;> simp [h]

/-- An empty coordinate family has no selected element. -/
theorem decodeOneHot_fin_zero (bits : Fin 0 → Bool) :
    decodeOneHot bits = none := by
  rw [decodeOneHot_eq_none_iff]
  rintro ⟨chosen, _⟩
  exact Fin.elim0 chosen

/-- Canonical one-hot encoding of one finite coordinate. -/
def encodeOneHot {ι : Type} [DecidableEq ι] (chosen : ι) : ι → Bool :=
  fun i => decide (i = chosen)

/-- Canonical encoding selects exactly its designated coordinate. -/
theorem oneHot_encodeOneHot {ι : Type} [DecidableEq ι] (chosen : ι) :
    OneHot (encodeOneHot chosen) := by
  refine ⟨chosen, by simp [encodeOneHot], ?_⟩
  intro i hi
  simpa [encodeOneHot] using hi

/-- Canonical one-hot encoding decodes to its designated coordinate. -/
theorem decodeOneHot_encodeOneHot {ι : Type} [Fintype ι] [DecidableEq ι]
    (chosen : ι) : decodeOneHot (encodeOneHot chosen) = some chosen :=
  (decodeOneHot_eq_some_iff (encodeOneHot chosen) chosen).mpr
    ⟨by simp [encodeOneHot], by intro i hi; simpa [encodeOneHot] using hi⟩

private theorem encodeOneHot_eq_of_oneHot {ι : Type} [DecidableEq ι]
    {bits : ι → Bool} {chosen : ι}
    (hbit : bits chosen = true) (hunique : ∀ i, bits i = true → i = chosen) :
    encodeOneHot chosen = bits := by
  funext i
  by_cases hi : i = chosen
  · subst i
    simp [encodeOneHot, hbit]
  · have hfalse : bits i = false :=
      Bool.eq_false_of_not_eq_true (fun htrue => hi (hunique i htrue))
    simp [encodeOneHot, hi, hfalse]

/-! ## Raw bounded-row codecs -/

namespace CfgBits

/-- Every finite group needed for a raw bounded row has one selected code. -/
structure RawDecodable {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) : Prop where
  label : OneHot bits.label
  state : OneHot bits.state
  stackHeight : ∀ k, OneHot (bits.stackHeight k)
  stackCell : ∀ k i, OneHot (bits.stackCell k i)

end CfgBits

/-- Extract the unique raw bounded code from proof-carrying one-hot bits. -/
def rawCfgOf {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) (hraw : bits.RawDecodable) : BoundedCfg tm H where
  halted := bits.halted
  label := hraw.label.choose
  state := hraw.state.choose
  stack k :=
    { height := (hraw.stackHeight k).choose
      cells := fun i => (hraw.stackCell k i).choose }

namespace CfgBits

/-- A one-hot row whose uniquely selected raw code satisfies the canonical
machine-row constraints. -/
def Canonical {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) : Prop :=
  ∃ hraw : bits.RawDecodable, (rawCfgOf bits hraw).Valid

end CfgBits

/-- Reject a Boolean row unless every finite code group is one-hot. -/
def decodeRawCfg? {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) : Option (BoundedCfg tm H) := by
  classical
  exact if h : bits.RawDecodable then some (rawCfgOf bits h) else none

/-- Canonical one-hot encoding of every field in a raw bounded row. -/
def encodeRawCfgBits {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) : CfgBits tm H
  | .inl _ => code.halted
  | .inr (.inl label) => encodeOneHot code.label label
  | .inr (.inr (.inl state)) => encodeOneHot code.state state
  | .inr (.inr (.inr ⟨k, .inl height⟩)) =>
      encodeOneHot (code.stack k).height height
  | .inr (.inr (.inr ⟨k, .inr (cell, symbol)⟩)) =>
      encodeOneHot ((code.stack k).cells cell) symbol

private theorem encodeRawCfgBits_decodable {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) : (encodeRawCfgBits code).RawDecodable := by
  constructor
  · exact oneHot_encodeOneHot code.label
  · exact oneHot_encodeOneHot code.state
  · intro k
    exact oneHot_encodeOneHot (code.stack k).height
  · intro k i
    exact oneHot_encodeOneHot ((code.stack k).cells i)

private theorem boundedCfg_ext {tm : _root_.Turing.FinTM2} {H : Nat}
    {left right : BoundedCfg tm H}
    (hhalted : left.halted = right.halted)
    (hlabel : left.label = right.label)
    (hstate : left.state = right.state)
    (hstack : left.stack = right.stack) : left = right := by
  cases left
  cases right
  simp_all

private theorem boundedStack_ext {alphabetSize H : Nat}
    {left right : BoundedStack alphabetSize H}
    (hheight : left.height = right.height) (hcells : left.cells = right.cells) :
    left = right := by
  cases left
  cases right
  simp_all

private theorem rawCfgOf_encodeRawCfgBits {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) :
    rawCfgOf (encodeRawCfgBits code) (encodeRawCfgBits_decodable code) = code := by
  apply boundedCfg_ext
  · rfl
  · exact ((encodeRawCfgBits_decodable code).label.choose_spec.2 code.label (by
      change encodeOneHot code.label code.label = true
      simp [encodeOneHot])).symm
  · exact ((encodeRawCfgBits_decodable code).state.choose_spec.2 code.state (by
      change encodeOneHot code.state code.state = true
      simp [encodeOneHot])).symm
  · funext k
    apply boundedStack_ext
    · exact (((encodeRawCfgBits_decodable code).stackHeight k).choose_spec.2
        (code.stack k).height (by
          change encodeOneHot (code.stack k).height (code.stack k).height = true
          simp [encodeOneHot])).symm
    · funext i
      exact (((encodeRawCfgBits_decodable code).stackCell k i).choose_spec.2
        ((code.stack k).cells i) (by
          change encodeOneHot ((code.stack k).cells i)
            ((code.stack k).cells i) = true
          simp [encodeOneHot])).symm

/-- Encoding a raw row and decoding its fields recovers the entire row. -/
theorem decodeRawCfg_encode {tm : _root_.Turing.FinTM2} {H : Nat}
    (code : BoundedCfg tm H) :
    decodeRawCfg? (encodeRawCfgBits code) = some code := by
  unfold decodeRawCfg?
  rw [dif_pos (encodeRawCfgBits_decodable code)]
  congr 1
  exact rawCfgOf_encodeRawCfgBits code

/-- Re-encoding any proof-indexed raw decoding recovers every original bit. -/
theorem encodeRawCfg_decode {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) (hraw : bits.RawDecodable) :
    encodeRawCfgBits (rawCfgOf bits hraw) = bits := by
  funext slot
  rcases slot with (_ | label | state | ⟨k, height | cell⟩)
  · rfl
  · simpa [rawCfgOf, encodeRawCfgBits, CfgBundle.label, CfgSlot.label] using
      congrFun (encodeOneHot_eq_of_oneHot
        hraw.label.choose_spec.1 hraw.label.choose_spec.2) label
  · simpa [rawCfgOf, encodeRawCfgBits, CfgBundle.state, CfgSlot.state] using
      congrFun (encodeOneHot_eq_of_oneHot
        hraw.state.choose_spec.1 hraw.state.choose_spec.2) state
  · simpa [rawCfgOf, encodeRawCfgBits, CfgBundle.stackHeight,
      CfgSlot.stackHeight] using
      congrFun (encodeOneHot_eq_of_oneHot
        (hraw.stackHeight k).choose_spec.1
        (hraw.stackHeight k).choose_spec.2) height
  · rcases cell with ⟨i, symbol⟩
    simpa [rawCfgOf, encodeRawCfgBits, CfgBundle.stackCell,
      CfgSlot.stackCell] using
      congrFun (encodeOneHot_eq_of_oneHot
        (hraw.stackCell k i).choose_spec.1
        (hraw.stackCell k i).choose_spec.2) symbol

/-- Successful raw decoding is exactly canonical one-hot re-encoding. -/
theorem decodeRawCfg_eq_some_iff {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) (code : BoundedCfg tm H) :
    decodeRawCfg? bits = some code ↔ bits = encodeRawCfgBits code := by
  constructor
  · intro hdecode
    unfold decodeRawCfg? at hdecode
    split at hdecode
    next hraw =>
      have hcode : rawCfgOf bits hraw = code := Option.some.inj hdecode
      rw [← hcode]
      exact (encodeRawCfg_decode bits hraw).symm
    next => contradiction
  · intro hbits
    subst bits
    exact decodeRawCfg_encode code

/-- Raw decoding fails exactly when the bits are not one-hot-decodable. -/
theorem decodeRawCfg_eq_none_iff {tm : _root_.Turing.FinTM2} {H : Nat}
    (bits : CfgBits tm H) :
    decodeRawCfg? bits = none ↔ ¬ bits.RawDecodable := by
  classical
  unfold decodeRawCfg?
  split_ifs with h <;> simp [h]

/-! ## Evaluated row decoders -/

/-- Evaluate valid row wires and decode their raw bounded configuration.

The validity proof is intentionally mandatory even though decoding depends only
on the resulting bits: it rules out accidentally accepting a dangling wire via
the general circuit evaluator's out-of-range {lean}`false` default. -/
def evalRawBundle {tm : _root_.Turing.FinTM2} {H : Nat}
    (b : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (_hvalid : wires.ValidIn b) :
    Option (BoundedCfg tm H) :=
  decodeRawCfg? (evalCfgBits b inputs wires)

/-- Evaluate a row, decode its raw code, then enforce canonical machine-row
constraints using the configuration codec. -/
def evalBundle {tm : _root_.Turing.FinTM2} {H : Nat}
    (b : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn b) :
    Option tm.Cfg :=
  (evalRawBundle b inputs wires hvalid).bind (decodeCfg? tm)

private theorem decodeRawCfg_bind_isSome_iff_canonical
    {tm : _root_.Turing.FinTM2} {H : Nat} (bits : CfgBits tm H) :
    ((decodeRawCfg? bits).bind (decodeCfg? tm)).isSome = true ↔
      bits.Canonical := by
  classical
  unfold decodeRawCfg? CfgBits.Canonical
  split
  next hraw =>
    simp only [Option.bind_some]
    unfold decodeCfg?
    split
    next hvalid =>
      simp only [Option.isSome_some, true_iff]
      exact ⟨hraw, hvalid⟩
    next hnotValid =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      rintro ⟨hraw', hvalid'⟩
      have hproof : hraw' = hraw := Subsingleton.elim _ _
      subst hraw'
      exact hnotValid hvalid'
  next hnotRaw =>
    simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true,
      false_iff]
    exact fun hcanonical => hnotRaw hcanonical.choose

/-- Successful evaluated decoding is equivalent to the evaluated row bits
being one-hot and canonical. -/
theorem evalBundle_isSome_iff_canonical
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (b : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn b) :
    (evalBundle b inputs wires hvalid).isSome = true ↔
      (evalCfgBits b inputs wires).Canonical := by
  simpa only [evalBundle, evalRawBundle] using
    decodeRawCfg_bind_isSome_iff_canonical (evalCfgBits b inputs wires)

/-- Extension stability for raw row evaluation. -/
theorem evalRawBundle_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    evalRawBundle next inputs wires (hvalid.mono hext) =
      evalRawBundle base inputs wires hvalid := by
  simp [evalRawBundle, evalCfgBits_extends hext inputs wires hvalid]

/-- Extension stability for canonical machine-row evaluation. -/
theorem evalBundle_extends {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    evalBundle next inputs wires (hvalid.mono hext) =
      evalBundle base inputs wires hvalid := by
  simp [evalBundle, evalRawBundle_extends hext inputs wires hvalid]

private theorem decodeCfg?_encodeCfg (tm : _root_.Turing.FinTM2) {c : tm.Cfg}
    (hc : CfgAlphabetBounded tm c) {H : Nat}
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    decodeCfg? tm (encodeCfg tm hc hheight) = some c := by
  unfold decodeCfg?
  rw [dif_pos (encodeCfg_valid tm hc hheight)]
  congr 1
  exact decodeCfg_encodeCfg tm hc hheight

/-- Any wire bundle evaluating to the encoded bounded row decodes back to the
original machine configuration. -/
theorem evalBundle_encodeCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    (b : CircuitBuilder) (inputs : Nat → Bool) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn b) {c : tm.Cfg} (hc : CfgAlphabetBounded tm c)
    (hheight : ∀ k, (c.stk k).length ≤ H)
    (heval : evalCfgBits b inputs wires =
      encodeRawCfgBits (encodeCfg tm hc hheight)) :
    evalBundle b inputs wires hvalid = some c := by
  unfold evalBundle evalRawBundle
  rw [heval, decodeRawCfg_encode]
  exact decodeCfg?_encodeCfg tm hc hheight

namespace CfgInputAllocation

/-- Allocating a row and writing an encoded bounded row gives an exact raw
decoder round trip. -/
theorem evalRawBundle_write_encode {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {layout : CfgInputLayout tm H}
    (allocation : CfgInputAllocation start layout)
    (assignment : Nat → Bool) (code : BoundedCfg tm H) :
    evalRawBundle allocation.builder
        (layout.writeCfgBits assignment (encodeRawCfgBits code))
        allocation.wires allocation.valid = some code := by
  unfold evalRawBundle
  rw [allocation.evalCfgBits_write, decodeRawCfg_encode]

/-- Allocating a row and writing a canonical machine configuration gives an
exact machine decoder round trip. -/
theorem evalBundle_write_encodeCfg {tm : _root_.Turing.FinTM2} {H : Nat}
    {start : CircuitBuilder} {layout : CfgInputLayout tm H}
    (allocation : CfgInputAllocation start layout)
    (assignment : Nat → Bool) {c : tm.Cfg} (hc : CfgAlphabetBounded tm c)
    (hheight : ∀ k, (c.stk k).length ≤ H) :
    evalBundle allocation.builder
        (layout.writeCfgBits assignment
          (encodeRawCfgBits (encodeCfg tm hc hheight)))
        allocation.wires allocation.valid = some c := by
  apply evalBundle_encodeCfg
  exact allocation.evalCfgBits_write assignment
    (encodeRawCfgBits (encodeCfg tm hc hheight))

end CfgInputAllocation

end

end CLRS.Chapter34.Turing.CookLevin
