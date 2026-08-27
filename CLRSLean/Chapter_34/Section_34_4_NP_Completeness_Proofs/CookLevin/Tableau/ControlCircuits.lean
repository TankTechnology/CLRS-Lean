import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.BundleCombinators
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.ConstantPool

/-!
# CLRS Section 34.4 - Finite-control row circuits

This module centralizes the state, label, and halted coordinates of one
Cook--Levin row.  It supplies zero-gate pool-backed canonical encodings,
complete-row replacement operations, and semantic bridges from successful row
decoding to canonical finite-control bits.

Main results:

- Theorem {lit}`evalBundle_eq_some_canonical`: successful row decoding exposes
  an existential canonical row equality without a public choice accessor.
- Theorems {lit}`evalBundle_replaceState` and
  {lit}`evalBundle_replaceStatus`: replacing canonical control wires changes
  exactly the corresponding machine-configuration fields.

Layer boundary:

- Statement compilation is supplied by downstream {lit}`StatementCircuits`;
  {lit}`TransitionCircuits` supplies finite-label dispatch and the local step
  check, while the downstream boundary layer supplies exact initial and
  accepting constraints.  Downstream circuitization and assembly modules
  supply the polynomial bounds and verified whole-tableau circuit.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Typed state and label families -/

/-- Circuit wires indexed by every finite internal-state code. -/
abbrev StateWires (tm : _root_.Turing.FinTM2) :=
  Fin (stateCount tm) → CircuitBuilder.Wire

/-- Boolean values indexed by every finite internal-state code. -/
abbrev StateBits (tm : _root_.Turing.FinTM2) :=
  Fin (stateCount tm) → Bool

/-- Circuit wires indexed by every label code, including reserved {lean}`none`. -/
abbrev LabelWires (tm : _root_.Turing.FinTM2) :=
  Fin (labelCount tm + 1) → CircuitBuilder.Wire

/-- Boolean values indexed by every label code, including reserved {lean}`none`. -/
abbrev LabelBits (tm : _root_.Turing.FinTM2) :=
  Fin (labelCount tm + 1) → Bool

namespace StateWires

/-- Every state wire belongs to the selected builder. -/
def ValidIn {tm : _root_.Turing.FinTM2} (wires : StateWires tm)
    (builder : CircuitBuilder) : Prop :=
  ∀ i, builder.WireValid (wires i)

namespace ValidIn

/-- State-family validity is monotone under append-only builder extension. -/
theorem mono {tm : _root_.Turing.FinTM2} {wires : StateWires tm}
    {base next : CircuitBuilder} (hvalid : StateWires.ValidIn wires base)
    (hext : base.Extends next) : StateWires.ValidIn wires next :=
  fun i => hext.wireValid (hvalid i)

end ValidIn
end StateWires

namespace LabelWires

/-- Every label wire, including the reserved {lean}`none` coordinate, belongs to the
selected builder. -/
def ValidIn {tm : _root_.Turing.FinTM2} (wires : LabelWires tm)
    (builder : CircuitBuilder) : Prop :=
  ∀ i, builder.WireValid (wires i)

namespace ValidIn

/-- Label-family validity is monotone under append-only builder extension. -/
theorem mono {tm : _root_.Turing.FinTM2} {wires : LabelWires tm}
    {base next : CircuitBuilder} (hvalid : LabelWires.ValidIn wires base)
    (hext : base.Extends next) : LabelWires.ValidIn wires next :=
  fun i => hext.wireValid (hvalid i)

end ValidIn
end LabelWires

/-- Evaluate every wire in a state family. -/
def evalStateBits {tm : _root_.Turing.FinTM2} (builder : CircuitBuilder)
    (inputs : Nat → Bool) (wires : StateWires tm) : StateBits tm :=
  fun i => builder.evalWire inputs (wires i)

/-- Evaluate every wire in a label family. -/
def evalLabelBits {tm : _root_.Turing.FinTM2} (builder : CircuitBuilder)
    (inputs : Nat → Bool) (wires : LabelWires tm) : LabelBits tm :=
  fun i => builder.evalWire inputs (wires i)

/-- An old valid state family evaluates identically after builder extension. -/
theorem evalStateBits_extends {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : StateWires tm)
    (hvalid : StateWires.ValidIn wires base) :
    evalStateBits next inputs wires = evalStateBits base inputs wires := by
  funext i
  exact hext.evalWire_eq inputs (hvalid i)

/-- An old valid label family evaluates identically after builder extension. -/
theorem evalLabelBits_extends {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (hext : base.Extends next)
    (inputs : Nat → Bool) (wires : LabelWires tm)
    (hvalid : LabelWires.ValidIn wires base) :
    evalLabelBits next inputs wires = evalLabelBits base inputs wires := by
  funext i
  exact hext.evalWire_eq inputs (hvalid i)

/-! ## Complete-row control replacement -/

namespace CfgBundle

/-- Replace precisely the internal-state coordinates of a complete row. -/
def replaceState {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (replacement : Fin (stateCount tm) → α) :
    CfgBundle tm H α
  | .inl _ => bundle.halted
  | .inr (.inl label) => bundle.label label
  | .inr (.inr (.inl state)) => replacement state
  | .inr (.inr (.inr stack)) => bundle (.inr (.inr (.inr stack)))

/-- Replace the explicit halted coordinate and the complete label family
together. -/
def replaceStatus {tm : _root_.Turing.FinTM2} {H : Nat} {α : Type}
    (bundle : CfgBundle tm H α) (halted : α)
    (replacement : Fin (labelCount tm + 1) → α) : CfgBundle tm H α
  | .inl _ => halted
  | .inr (.inl label) => replacement label
  | .inr (.inr rest) => bundle (.inr (.inr rest))

/-- Replacing state preserves the halted coordinate. -/
@[simp] theorem replaceState_halted {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α)
    (replacement : Fin (stateCount tm) → α) :
    (bundle.replaceState replacement).halted = bundle.halted := rfl

/-- Replacing state preserves every label coordinate. -/
@[simp] theorem replaceState_label {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α)
    (replacement : Fin (stateCount tm) → α)
    (i : Fin (labelCount tm + 1)) :
    (bundle.replaceState replacement).label i = bundle.label i := rfl

/-- Replacing state exposes the replacement state family exactly. -/
@[simp] theorem replaceState_state {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α)
    (replacement : Fin (stateCount tm) → α) (i : Fin (stateCount tm)) :
    (bundle.replaceState replacement).state i = replacement i := rfl

/-- Replacing state preserves every dependently indexed stack. -/
@[simp] theorem replaceState_stack {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α)
    (replacement : Fin (stateCount tm) → α) (k : tm.K) :
    (bundle.replaceState replacement).stack k = bundle.stack k := by
  rfl

/-- Replacing status exposes the supplied halted coordinate. -/
@[simp] theorem replaceStatus_halted {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (halted : α)
    (replacement : Fin (labelCount tm + 1) → α) :
    (bundle.replaceStatus halted replacement).halted = halted := rfl

/-- Replacing status exposes every supplied label coordinate, including
reserved {lean}`none`. -/
@[simp] theorem replaceStatus_label {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (halted : α)
    (replacement : Fin (labelCount tm + 1) → α)
    (i : Fin (labelCount tm + 1)) :
    (bundle.replaceStatus halted replacement).label i = replacement i := rfl

/-- Replacing status preserves every state coordinate. -/
@[simp] theorem replaceStatus_state {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (halted : α)
    (replacement : Fin (labelCount tm + 1) → α)
    (i : Fin (stateCount tm)) :
    (bundle.replaceStatus halted replacement).state i = bundle.state i := rfl

/-- Replacing status preserves every dependently indexed stack. -/
@[simp] theorem replaceStatus_stack {tm : _root_.Turing.FinTM2} {H : Nat}
    {α : Type} (bundle : CfgBundle tm H α) (halted : α)
    (replacement : Fin (labelCount tm + 1) → α) (k : tm.K) :
    (bundle.replaceStatus halted replacement).stack k = bundle.stack k := by
  rfl

end CfgBundle

namespace CfgWires.ValidIn

/-- A valid complete row has a valid state projection. -/
theorem state {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {builder : CircuitBuilder}
    (hvalid : wires.ValidIn builder) :
    StateWires.ValidIn wires.state builder :=
  fun i => hvalid (CfgSlot.state i)

/-- A valid complete row has a valid label projection, including {lean}`none`. -/
theorem label {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {builder : CircuitBuilder}
    (hvalid : wires.ValidIn builder) :
    LabelWires.ValidIn wires.label builder :=
  fun i => hvalid (CfgSlot.label i)

/-- Replacing state by valid wires preserves complete-row validity. -/
theorem replaceState {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {builder : CircuitBuilder}
    (hvalid : wires.ValidIn builder) {replacement : StateWires tm}
    (hreplacement : StateWires.ValidIn replacement builder) :
    CfgWires.ValidIn (wires.replaceState replacement) builder := by
  intro slot
  rcases slot with (_ | label | state | stack)
  · exact hvalid _
  · exact hvalid _
  · exact hreplacement state
  · exact hvalid _

/-- Replacing status by one valid halted wire and valid label wires preserves
complete-row validity. -/
theorem replaceStatus {tm : _root_.Turing.FinTM2} {H : Nat}
    {wires : CfgWires tm H} {builder : CircuitBuilder}
    (hvalid : wires.ValidIn builder) {halted : CircuitBuilder.Wire}
    (hhalted : builder.WireValid halted) {replacement : LabelWires tm}
    (hreplacement : LabelWires.ValidIn replacement builder) :
    CfgWires.ValidIn (wires.replaceStatus halted replacement) builder := by
  intro slot
  rcases slot with (_ | label | rest)
  · exact hhalted
  · exact hreplacement label
  · exact hvalid _

end CfgWires.ValidIn

/-- Complete-row evaluation followed by state projection equals direct state
evaluation. -/
theorem evalStateBits_cfgState {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) :
    evalStateBits builder inputs wires.state =
      (evalCfgBits builder inputs wires).state := rfl

/-- Complete-row evaluation followed by label projection equals direct label
evaluation. -/
theorem evalLabelBits_cfgLabel {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) :
    evalLabelBits builder inputs wires.label =
      (evalCfgBits builder inputs wires).label := rfl

/-- Evaluation commutes exactly with complete-row state replacement. -/
theorem evalCfgBits_replaceState {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (replacement : StateWires tm) :
    evalCfgBits builder inputs (wires.replaceState replacement) =
      (evalCfgBits builder inputs wires).replaceState
        (evalStateBits builder inputs replacement) := by
  funext slot
  rcases slot with (_ | label | state | stack) <;> rfl

/-- Evaluation commutes exactly with complete-row status replacement. -/
theorem evalCfgBits_replaceStatus {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (halted : CircuitBuilder.Wire)
    (replacement : LabelWires tm) :
    evalCfgBits builder inputs (wires.replaceStatus halted replacement) =
      (evalCfgBits builder inputs wires).replaceStatus
        (builder.evalWire inputs halted)
        (evalLabelBits builder inputs replacement) := by
  funext slot
  rcases slot with (_ | label | rest) <;> rfl

/-! ## Pool-backed canonical control encodings -/

/-- Encode one machine state with existing true/false wires and no new gates. -/
def encodeStateWires {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (state : tm.σ) : StateWires tm :=
  fun code => if code = stateEquivFin tm state then
    pool.trueWire else pool.falseWire

/-- A pool-backed state encoding is valid without allocating gates. -/
theorem encodeStateWires_valid {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool) (state : tm.σ) :
    StateWires.ValidIn (encodeStateWires pool state) builder := by
  intro code
  by_cases hcode : code = stateEquivFin tm state
  · simp [encodeStateWires, hcode, pool.trueValid]
  · simp [encodeStateWires, hcode, pool.falseValid]

/-- Pool-backed state wires evaluate to the canonical state one-hot code. -/
theorem encodeStateWires_eval {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (state : tm.σ) :
    evalStateBits builder inputs (encodeStateWires pool state) =
      encodeOneHot (stateEquivFin tm state) := by
  funext code
  by_cases hcode : code = stateEquivFin tm state
  · simp [evalStateBits, encodeStateWires, encodeOneHot, hcode,
      pool.true_eval]
  · simp [evalStateBits, encodeStateWires, encodeOneHot, hcode,
      pool.false_eval]

/-- Transporting a pool leaves every static state wire unchanged. -/
theorem encodeStateWires_mono {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext : base.Extends next) (state : tm.σ) :
    encodeStateWires (pool.mono hext) state = encodeStateWires pool state := by
  rfl

/-- Static state encoding is independent of the extension proof used to
transport its pool. -/
theorem encodeStateWires_proof_irrel {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext₁ hext₂ : base.Extends next) (state : tm.σ) :
    encodeStateWires (pool.mono hext₁) state =
      encodeStateWires (pool.mono hext₂) state := by
  rfl

/-- Encode one optional label, including {lean}`none`, with existing constants. -/
def encodeLabelWires {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (label : Option tm.Λ) : LabelWires tm :=
  fun code => if code = encodeLabel tm label then
    pool.trueWire else pool.falseWire

/-- A pool-backed optional-label encoding is valid without allocating gates. -/
theorem encodeLabelWires_valid {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (label : Option tm.Λ) :
    LabelWires.ValidIn (encodeLabelWires pool label) builder := by
  intro code
  by_cases hcode : code = encodeLabel tm label
  · simp [encodeLabelWires, hcode, pool.trueValid]
  · simp [encodeLabelWires, hcode, pool.falseValid]

/-- Pool-backed label wires evaluate to the canonical optional-label code. -/
theorem encodeLabelWires_eval {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (label : Option tm.Λ) :
    evalLabelBits builder inputs (encodeLabelWires pool label) =
      encodeOneHot (encodeLabel tm label) := by
  funext code
  by_cases hcode : code = encodeLabel tm label
  · simp [evalLabelBits, encodeLabelWires, encodeOneHot, hcode,
      pool.true_eval]
  · simp [evalLabelBits, encodeLabelWires, encodeOneHot, hcode,
      pool.false_eval]

/-- Transporting a pool leaves every static optional-label wire unchanged. -/
theorem encodeLabelWires_mono {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext : base.Extends next) (label : Option tm.Λ) :
    encodeLabelWires (pool.mono hext) label = encodeLabelWires pool label := by
  rfl

/-- Static label encoding is independent of the extension proof used to
transport its pool. -/
theorem encodeLabelWires_proof_irrel {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext₁ hext₂ : base.Extends next) (label : Option tm.Λ) :
    encodeLabelWires (pool.mono hext₁) label =
      encodeLabelWires (pool.mono hext₂) label := by
  rfl

/-- Encode the halted view of an optional label with one existing constant. -/
def encodeLabelHaltedWire {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (label : Option tm.Λ) : CircuitBuilder.Wire :=
  if labelHalted label then pool.trueWire else pool.falseWire

/-- The pool-backed halted wire is valid without allocating a gate. -/
theorem encodeLabelHaltedWire_valid {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (label : Option tm.Λ) :
    builder.WireValid (encodeLabelHaltedWire pool label) := by
  cases label <;> simp [encodeLabelHaltedWire, labelHalted,
    pool.falseValid, pool.trueValid]

/-- The pool-backed halted wire evaluates exactly to {lit}`labelHalted`. -/
theorem encodeLabelHaltedWire_eval {tm : _root_.Turing.FinTM2}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (label : Option tm.Λ) :
    builder.evalWire inputs (encodeLabelHaltedWire pool label) =
      labelHalted label := by
  cases label <;> simp [encodeLabelHaltedWire, labelHalted,
    pool.false_eval, pool.true_eval]

/-- Transporting a pool leaves its static halted wire unchanged. -/
theorem encodeLabelHaltedWire_mono {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext : base.Extends next) (label : Option tm.Λ) :
    encodeLabelHaltedWire (pool.mono hext) label =
      encodeLabelHaltedWire pool label := by
  rfl

/-- Static halted encoding is independent of the extension proof used to
transport its pool. -/
theorem encodeLabelHaltedWire_proof_irrel {tm : _root_.Turing.FinTM2}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext₁ hext₂ : base.Extends next) (label : Option tm.Λ) :
    encodeLabelHaltedWire (pool.mono hext₁) label =
      encodeLabelHaltedWire (pool.mono hext₂) label := by
  rfl

/-! ## Canonical inversion and control projections -/

/-- Successful complete-row decoding exposes an existential canonical raw-row
encoding, without selecting a public raw-code or proof witness. -/
theorem evalBundle_eq_some_canonical
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) (c : tm.Cfg)
    (hdecoded : evalBundle builder inputs wires hvalid = some c) :
    ∃ (hc : CfgAlphabetBounded tm c)
      (hheight : ∀ k, (c.stk k).length ≤ H),
      evalCfgBits builder inputs wires =
        encodeRawCfgBits (encodeCfg tm hc hheight) := by
  unfold evalBundle evalRawBundle at hdecoded
  generalize hraw : decodeRawCfg? (evalCfgBits builder inputs wires) = raw
    at hdecoded
  cases raw with
  | none => simp at hdecoded
  | some code =>
      simp only [Option.bind_some] at hdecoded
      unfold decodeCfg? at hdecoded
      split at hdecoded
      next hcodeValid =>
        have hcEq : decodeCfg tm code hcodeValid = c := Option.some.inj hdecoded
        subst c
        refine ⟨decoded_alphabetBounded tm code hcodeValid,
          decoded_stack_length_le tm code hcodeValid, ?_⟩
        have hbits := (decodeRawCfg_eq_some_iff
          (evalCfgBits builder inputs wires) code).mp hraw
        rw [encodeCfg_decodeCfg tm code hcodeValid]
        exact hbits
      next => simp at hdecoded

/-- Successful row decoding determines the exact canonical state one-hot bits. -/
theorem evalStateBits_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) (c : tm.Cfg)
    (hdecoded : evalBundle builder inputs wires hvalid = some c) :
    evalStateBits builder inputs wires.state =
      encodeOneHot (stateEquivFin tm c.var) := by
  rcases evalBundle_eq_some_canonical builder inputs wires hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  funext i
  have hslot := congrFun hbits (CfgSlot.state i)
  simpa [evalStateBits, evalCfgBits, encodeRawCfgBits, encodeCfg,
    CfgBundle.state, CfgSlot.state] using hslot

/-- Successful row decoding determines the exact canonical optional-label
one-hot bits, including the reserved {lean}`none` coordinate. -/
theorem evalLabelBits_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) (c : tm.Cfg)
    (hdecoded : evalBundle builder inputs wires hvalid = some c) :
    evalLabelBits builder inputs wires.label =
      encodeOneHot (encodeLabel tm c.l) := by
  rcases evalBundle_eq_some_canonical builder inputs wires hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  funext i
  have hslot := congrFun hbits (CfgSlot.label i)
  simpa [evalLabelBits, evalCfgBits, encodeRawCfgBits, encodeCfg,
    CfgBundle.label, CfgSlot.label] using hslot

/-- Successful row decoding determines the explicit halted bit from its label. -/
theorem evalHaltedBit_of_evalBundle
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) (c : tm.Cfg)
    (hdecoded : evalBundle builder inputs wires hvalid = some c) :
    builder.evalWire inputs wires.halted = labelHalted c.l := by
  rcases evalBundle_eq_some_canonical builder inputs wires hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  have hslot := congrFun hbits (CfgSlot.halted tm H)
  simpa [evalCfgBits, encodeRawCfgBits, encodeCfg, CfgBundle.halted,
    CfgSlot.halted] using hslot

/-! ## Whole-row control semantics -/

/-- Replacing a decoded row's state with an exact canonical state family
decodes to the corresponding state-updated machine configuration. -/
theorem evalBundle_replaceState
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) (c : tm.Cfg)
    (hdecoded : evalBundle builder inputs wires hvalid = some c)
    (replacement : StateWires tm)
    (hreplacement : StateWires.ValidIn replacement builder)
    (newState : tm.σ)
    (heval : evalStateBits builder inputs replacement =
      encodeOneHot (stateEquivFin tm newState)) :
    evalBundle builder inputs (wires.replaceState replacement)
      (hvalid.replaceState hreplacement) = some { c with var := newState } := by
  rcases evalBundle_eq_some_canonical builder inputs wires hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  let updated : tm.Cfg := { c with var := newState }
  have hupdatedAlphabet : CfgAlphabetBounded tm updated := by
    simpa [updated, CfgAlphabetBounded] using hc
  have hupdatedHeight : ∀ k, (updated.stk k).length ≤ H := by
    simpa [updated] using hheight
  apply evalBundle_encodeCfg builder inputs _ _ hupdatedAlphabet hupdatedHeight
  rw [evalCfgBits_replaceState, hbits, heval]
  funext slot
  rcases slot with (_ | label | state | stack)
  · rfl
  · rfl
  · simp [CfgBundle.replaceState, encodeRawCfgBits, encodeCfg, updated]
  · rcases stack with ⟨k, height | cell⟩ <;> rfl

/-- Replacing a decoded row's label family and matching halted bit decodes to
the corresponding status-updated machine configuration. -/
theorem evalBundle_replaceStatus
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (builder : CircuitBuilder) (inputs : Nat → Bool)
    (wires : CfgWires tm H) (hvalid : wires.ValidIn builder) (c : tm.Cfg)
    (hdecoded : evalBundle builder inputs wires hvalid = some c)
    (halted : CircuitBuilder.Wire) (hhalted : builder.WireValid halted)
    (replacement : LabelWires tm)
    (hreplacement : LabelWires.ValidIn replacement builder)
    (newLabel : Option tm.Λ)
    (hhaltedEval : builder.evalWire inputs halted = labelHalted newLabel)
    (hlabelEval : evalLabelBits builder inputs replacement =
      encodeOneHot (encodeLabel tm newLabel)) :
    evalBundle builder inputs (wires.replaceStatus halted replacement)
      (hvalid.replaceStatus hhalted hreplacement) =
        some { c with l := newLabel } := by
  rcases evalBundle_eq_some_canonical builder inputs wires hvalid c hdecoded with
    ⟨hc, hheight, hbits⟩
  let updated : tm.Cfg := { c with l := newLabel }
  have hupdatedAlphabet : CfgAlphabetBounded tm updated := by
    simpa [updated, CfgAlphabetBounded] using hc
  have hupdatedHeight : ∀ k, (updated.stk k).length ≤ H := by
    simpa [updated] using hheight
  apply evalBundle_encodeCfg builder inputs _ _ hupdatedAlphabet hupdatedHeight
  rw [evalCfgBits_replaceStatus, hbits, hhaltedEval, hlabelEval]
  funext slot
  rcases slot with (_ | label | rest)
  · rfl
  · simp [CfgBundle.replaceStatus, encodeRawCfgBits, encodeCfg, updated]
  · rcases rest with state | stack
    · rfl
    · rcases stack with ⟨k, height | cell⟩ <;> rfl

end

end CLRS.Chapter34.Turing.CookLevin
