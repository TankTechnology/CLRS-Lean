import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.Basic

/-!
# CLRS Section 34.4 - A proved append-only circuit builder

Cook--Levin circuitization needs fresh named wires without ever creating a
forward or dangling reference.  This module packages a gate prefix together
with its gate-order invariant.  Every constructor appends gates, returns the
old gate count as its fresh wire, and exports exact validity, semantics, and
gate-count contracts.

Main results:

- `CircuitBuilder.Extends.evalWire_eq`: extensions preserve every old
  wire value.
- The primitive and Boolean-combinator theorem families expose extension,
  wire-validity, exact gate delta, and evaluation contracts.
- `CircuitBuilder.finish_wellFormed`: every selected valid output closes
  to an honest well-formed general circuit.

Current gaps:

- None for the append-only builder; bounded configuration wire bundles belong
  to the next tableau layer.
-/

namespace CLRS.Chapter34.Turing.CookLevin

/-! ## Builder state and extension semantics -/

/-- An append-only gate prefix whose stored gates are valid at their positions. -/
structure CircuitBuilder where
  inputCount : Nat
  gates : List CircuitGate
  valid : ∀ i (hi : i < gates.length),
    (gates.get ⟨i, hi⟩).ValidAt inputCount i

namespace CircuitBuilder

/-- A gate position used as a named Boolean wire. -/
abbrev Wire := Nat

/-- A wire belongs to the current gate prefix. -/
def WireValid (b : CircuitBuilder) (wire : Wire) : Prop :=
  wire < b.gates.length

/-- The empty builder with a fixed external-input arity. -/
def empty (inputCount : Nat) : CircuitBuilder where
  inputCount := inputCount
  gates := []
  valid := by simp

/-- One builder extends another when it preserves the input arity and appends
only a suffix to the old gate list. -/
def Extends (base next : CircuitBuilder) : Prop :=
  next.inputCount = base.inputCount ∧ ∃ suffix, next.gates = base.gates ++ suffix

namespace Extends

/-- Every builder extends itself by the empty suffix. -/
theorem refl (b : CircuitBuilder) : b.Extends b := by
  exact ⟨rfl, [], by simp⟩

/-- Builder extension is transitive. -/
theorem trans {first second third : CircuitBuilder}
    (h₁ : first.Extends second) (h₂ : second.Extends third) :
    first.Extends third := by
  rcases h₁ with ⟨hinputs₁, suffix₁, hgates₁⟩
  rcases h₂ with ⟨hinputs₂, suffix₂, hgates₂⟩
  refine ⟨hinputs₂.trans hinputs₁, suffix₁ ++ suffix₂, ?_⟩
  simp [hgates₂, hgates₁, List.append_assoc]

/-- An extension never shortens the gate prefix. -/
theorem length_le {base next : CircuitBuilder} (h : base.Extends next) :
    base.gates.length ≤ next.gates.length := by
  rcases h with ⟨_, suffix, hgates⟩
  rw [hgates]
  simp

/-- Every old valid wire remains valid in an extension. -/
theorem wireValid {base next : CircuitBuilder} (h : base.Extends next)
    {wire : Wire} (hwire : base.WireValid wire) : next.WireValid wire :=
  lt_of_lt_of_le hwire h.length_le

end Extends

/-! ## Evaluation and append stability -/

/-- Evaluate every gate in a builder prefix. -/
def evalValues (b : CircuitBuilder) (inputs : Nat → Bool) : Array Bool :=
  b.gates.foldl (fun values gate => values.push (gate.evalWith inputs values)) #[]

/-- Evaluate one named wire, defaulting only when the caller omits a validity
proof.  Public constructor theorems always supply valid wires. -/
def evalWire (b : CircuitBuilder) (inputs : Nat → Bool) (wire : Wire) : Bool :=
  (b.evalValues inputs).getD wire false

/-- Builder evaluation stores one value per gate. -/
theorem evalValues_size (b : CircuitBuilder) (inputs : Nat → Bool) :
    (b.evalValues inputs).size = b.gates.length := by
  let circuit : Circuit :=
    { inputCount := b.inputCount, gates := b.gates, output := 0 }
  simpa [evalValues, circuit, Circuit.evalValues] using
    Circuit.evalValues_size circuit inputs

private theorem evalFold_getD_eq_initial (inputs : Nat → Bool)
    (suffix : List CircuitGate) (initial : Array Bool) (wire : Nat)
    (hwire : wire < initial.size) :
    (suffix.foldl
      (fun values gate => values.push (gate.evalWith inputs values)) initial).getD
        wire false = initial.getD wire false := by
  induction suffix generalizing initial with
  | nil => rfl
  | cons gate suffix ih =>
      simp only [List.foldl_cons]
      rw [ih (initial := initial.push (gate.evalWith inputs initial))
        (hwire := by rw [Array.size_push]; omega)]
      have hpush : wire < (initial.push (gate.evalWith inputs initial)).size := by
        rw [Array.size_push]
        omega
      unfold Array.getD
      rw [dif_pos hpush, dif_pos hwire]
      exact Array.getElem_push_lt hwire

/-- Extending a builder preserves the evaluated value of every old valid wire. -/
theorem Extends.evalWire_eq {base next : CircuitBuilder}
    (h : base.Extends next) (inputs : Nat → Bool) {wire : Wire}
    (hwire : base.WireValid wire) :
    next.evalWire inputs wire = base.evalWire inputs wire := by
  rcases h with ⟨_, suffix, hgates⟩
  rw [evalWire, evalWire, evalValues, evalValues, hgates, List.foldl_append]
  apply evalFold_getD_eq_initial
  have hsize : wire < (base.evalValues inputs).size := by
    rw [evalValues_size]
    exact hwire
  simpa [evalValues] using hsize

private def appendGate (b : CircuitBuilder) (gate : CircuitGate)
    (hgate : gate.ValidAt b.inputCount b.gates.length) : CircuitBuilder where
  inputCount := b.inputCount
  gates := b.gates ++ [gate]
  valid := by
    intro i hi
    by_cases hold : i < b.gates.length
    · simpa [List.get_eq_getElem, hold] using b.valid i hold
    · have hiEq : i = b.gates.length := by simp at hi; omega
      subst i
      simpa using hgate

private theorem appendGate_extends (b : CircuitBuilder) (gate : CircuitGate)
    (hgate : gate.ValidAt b.inputCount b.gates.length) :
    b.Extends (appendGate b gate hgate) := by
  exact ⟨rfl, [gate], rfl⟩

private theorem appendGate_wireValid (b : CircuitBuilder) (gate : CircuitGate)
    (hgate : gate.ValidAt b.inputCount b.gates.length) :
    (appendGate b gate hgate).WireValid b.gates.length := by
  simp [WireValid, appendGate]

private theorem appendGate_delta (b : CircuitBuilder) (gate : CircuitGate)
    (hgate : gate.ValidAt b.inputCount b.gates.length) :
    (appendGate b gate hgate).gates.length = b.gates.length + 1 := by
  simp [appendGate]

private theorem appendGate_eval (b : CircuitBuilder) (gate : CircuitGate)
    (hgate : gate.ValidAt b.inputCount b.gates.length) (inputs : Nat → Bool) :
    (appendGate b gate hgate).evalWire inputs b.gates.length =
      gate.evalWith inputs (b.evalValues inputs) := by
  unfold evalWire evalValues appendGate
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hsize :
      (b.gates.foldl
        (fun values gate => values.push (gate.evalWith inputs values)) #[]).size =
        b.gates.length := evalValues_size b inputs
  unfold Array.getD
  rw [dif_pos (by rw [Array.size_push, hsize]; omega)]
  simp [Array.getElem_push, hsize]

/-! ## Primitive gates -/

/-- Append an external-input gate. -/
def input (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) : CircuitBuilder × Wire :=
  (appendGate b (.input inputIndex) hinput, b.gates.length)

/-- Appending an external input records its exact gate at the end of the
stream. -/
@[simp] theorem input_gates (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) :
    (b.input inputIndex hinput).1.gates = b.gates ++ [.input inputIndex] := by
  rfl

/-- The fresh input wire is the previous gate count. -/
theorem input_wire_eq (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) :
    (b.input inputIndex hinput).2 = b.gates.length := by
  rfl

/-- Appending an input gate extends the original prefix. -/
theorem input_extends (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) :
    b.Extends (b.input inputIndex hinput).1 :=
  appendGate_extends b (.input inputIndex) hinput

/-- The fresh input wire is valid in the returned builder. -/
theorem input_wireValid (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) :
    (b.input inputIndex hinput).1.WireValid (b.input inputIndex hinput).2 :=
  appendGate_wireValid b (.input inputIndex) hinput

/-- An input constructor appends exactly one gate. -/
theorem input_gate_delta (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) :
    (b.input inputIndex hinput).1.gates.length = b.gates.length + 1 :=
  appendGate_delta b (.input inputIndex) hinput

/-- The fresh input wire evaluates to its external input bit. -/
theorem input_eval (b : CircuitBuilder) (inputIndex : Nat)
    (hinput : inputIndex < b.inputCount) (inputs : Nat → Bool) :
    (b.input inputIndex hinput).1.evalWire inputs (b.input inputIndex hinput).2 =
      inputs inputIndex := by
  exact appendGate_eval b (.input inputIndex) hinput inputs

/-- Append a Boolean constant gate. -/
def const (b : CircuitBuilder) (value : Bool) : CircuitBuilder × Wire :=
  (appendGate b (.const value) trivial, b.gates.length)

/-- Appending a constant records its exact gate tag at the end of the gate
stream. -/
@[simp] theorem const_gates (b : CircuitBuilder) (value : Bool) :
    (b.const value).1.gates = b.gates ++ [.const value] := by
  rfl

/-- The fresh constant wire is the previous gate count. -/
theorem const_wire_eq (b : CircuitBuilder) (value : Bool) :
    (b.const value).2 = b.gates.length := by
  rfl

/-- Appending a constant gate extends the original prefix. -/
theorem const_extends (b : CircuitBuilder) (value : Bool) :
    b.Extends (b.const value).1 := appendGate_extends b (.const value) trivial

/-- The fresh constant wire is valid in the returned builder. -/
theorem const_wireValid (b : CircuitBuilder) (value : Bool) :
    (b.const value).1.WireValid (b.const value).2 :=
  appendGate_wireValid b (.const value) trivial

/-- A constant constructor appends exactly one gate. -/
theorem const_gate_delta (b : CircuitBuilder) (value : Bool) :
    (b.const value).1.gates.length = b.gates.length + 1 :=
  appendGate_delta b (.const value) trivial

/-- The fresh constant wire evaluates to its stored Boolean value. -/
theorem const_eval (b : CircuitBuilder) (value : Bool) (inputs : Nat → Bool) :
    (b.const value).1.evalWire inputs (b.const value).2 = value := by
  exact appendGate_eval b (.const value) trivial inputs

/-- Append Boolean negation of an existing valid wire. -/
def not (b : CircuitBuilder) (source : Wire) (hsource : b.WireValid source) :
    CircuitBuilder × Wire :=
  (appendGate b (.not source) hsource, b.gates.length)

/-- Appending negation records its exact source reference. -/
@[simp] theorem not_gates (b : CircuitBuilder) (source : Wire)
    (hsource : b.WireValid source) :
    (b.not source hsource).1.gates = b.gates ++ [.not source] := by
  rfl

/-- The fresh negation wire is the previous gate count. -/
theorem not_wire_eq (b : CircuitBuilder) (source : Wire)
    (hsource : b.WireValid source) :
    (b.not source hsource).2 = b.gates.length := by
  rfl

/-- Appending negation extends the original prefix. -/
theorem not_extends (b : CircuitBuilder) (source : Wire)
    (hsource : b.WireValid source) : b.Extends (b.not source hsource).1 :=
  appendGate_extends b (.not source) hsource

/-- The fresh negation wire is valid in the returned builder. -/
theorem not_wireValid (b : CircuitBuilder) (source : Wire)
    (hsource : b.WireValid source) :
    (b.not source hsource).1.WireValid (b.not source hsource).2 :=
  appendGate_wireValid b (.not source) hsource

/-- Negation appends exactly one gate. -/
theorem not_gate_delta (b : CircuitBuilder) (source : Wire)
    (hsource : b.WireValid source) :
    (b.not source hsource).1.gates.length = b.gates.length + 1 :=
  appendGate_delta b (.not source) hsource

/-- The fresh negation wire evaluates to the negated old wire value. -/
theorem not_eval (b : CircuitBuilder) (source : Wire)
    (hsource : b.WireValid source) (inputs : Nat → Bool) :
    (b.not source hsource).1.evalWire inputs (b.not source hsource).2 =
      !(b.evalWire inputs source) := by
  exact appendGate_eval b (.not source) hsource inputs

/-- Append conjunction of two existing valid wires. -/
def and (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    CircuitBuilder × Wire :=
  (appendGate b (.and left right) ⟨hleft, hright⟩, b.gates.length)

/-- Appending conjunction records its exact two source references. -/
@[simp] theorem and_gates (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.and left right hleft hright).1.gates =
      b.gates ++ [.and left right] := by
  rfl

/-- The fresh conjunction wire is the previous gate count. -/
theorem and_wire_eq (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.and left right hleft hright).2 = b.gates.length := by
  rfl

/-- Appending conjunction extends the original prefix. -/
theorem and_extends (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    b.Extends (b.and left right hleft hright).1 :=
  appendGate_extends b (.and left right) ⟨hleft, hright⟩

/-- The fresh conjunction wire is valid in the returned builder. -/
theorem and_wireValid (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.and left right hleft hright).1.WireValid
      (b.and left right hleft hright).2 :=
  appendGate_wireValid b (.and left right) ⟨hleft, hright⟩

/-- Conjunction appends exactly one gate. -/
theorem and_gate_delta (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.and left right hleft hright).1.gates.length = b.gates.length + 1 :=
  appendGate_delta b (.and left right) ⟨hleft, hright⟩

/-- The fresh conjunction wire evaluates to both old wire values conjoined. -/
theorem and_eval (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right)
    (inputs : Nat → Bool) :
    (b.and left right hleft hright).1.evalWire inputs
        (b.and left right hleft hright).2 =
      (b.evalWire inputs left && b.evalWire inputs right) := by
  exact appendGate_eval b (.and left right) ⟨hleft, hright⟩ inputs

/-- Append disjunction of two existing valid wires. -/
def or (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    CircuitBuilder × Wire :=
  (appendGate b (.or left right) ⟨hleft, hright⟩, b.gates.length)

/-- Appending disjunction records its exact two source references. -/
@[simp] theorem or_gates (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.or left right hleft hright).1.gates =
      b.gates ++ [.or left right] := by
  rfl

/-- The fresh disjunction wire is the previous gate count. -/
theorem or_wire_eq (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.or left right hleft hright).2 = b.gates.length := by
  rfl

/-- Appending disjunction extends the original prefix. -/
theorem or_extends (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    b.Extends (b.or left right hleft hright).1 :=
  appendGate_extends b (.or left right) ⟨hleft, hright⟩

/-- The fresh disjunction wire is valid in the returned builder. -/
theorem or_wireValid (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.or left right hleft hright).1.WireValid
      (b.or left right hleft hright).2 :=
  appendGate_wireValid b (.or left right) ⟨hleft, hright⟩

/-- Disjunction appends exactly one gate. -/
theorem or_gate_delta (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.or left right hleft hright).1.gates.length = b.gates.length + 1 :=
  appendGate_delta b (.or left right) ⟨hleft, hright⟩

/-- The fresh disjunction wire evaluates to the disjunction of old values. -/
theorem or_eval (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right)
    (inputs : Nat → Bool) :
    (b.or left right hleft hright).1.evalWire inputs
        (b.or left right hleft hright).2 =
      (b.evalWire inputs left || b.evalWire inputs right) := by
  exact appendGate_eval b (.or left right) ⟨hleft, hright⟩ inputs

/-! ## Boolean folds -/

/-- Pure gate-order trace of the tail-first conjunction fold. -/
structure ConjunctionGateTrace where
  gates : List CircuitGate
  wire : Wire
deriving DecidableEq, Repr

/-- The empty conjunction emits a true seed; every source wire then appends
one conjunction gate in tail-first order. -/
def conjunctionGateTrace (start : Nat) : List Wire → ConjunctionGateTrace
  | [] =>
      { gates := [.const true]
        wire := start }
  | wire :: rest =>
      let tail := conjunctionGateTrace start rest
      let next := start + tail.gates.length
      { gates := tail.gates ++ [.and wire tail.wire]
        wire := next }

/-- A conjunction trace contains its true seed and one gate per source. -/
@[simp] theorem conjunctionGateTrace_length (start : Nat) (wires : List Wire) :
    (conjunctionGateTrace start wires).gates.length = wires.length + 1 := by
  induction wires with
  | nil => rfl
  | cons wire rest ih => simp [conjunctionGateTrace, ih]

/-- Internal result package used to compose builders while retaining the
extension and fresh-wire invariants. -/
private structure BuiltWire (base : CircuitBuilder) where
  builder : CircuitBuilder
  wire : Wire
  extension : base.Extends builder
  valid : builder.WireValid wire

private def conjunctionResult (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) : BuiltWire b :=
  match wires with
  | [] =>
      { builder := (b.const true).1
        wire := (b.const true).2
        extension := const_extends b true
        valid := const_wireValid b true }
  | wire :: rest =>
      let tail := conjunctionResult b rest (fun w hw => hvalid w (by simp [hw]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      let next := tail.builder.and wire tail.wire hwire tail.valid
      { builder := next.1
        wire := next.2
        extension := tail.extension.trans
          (and_extends tail.builder wire tail.wire hwire tail.valid)
        valid := and_wireValid tail.builder wire tail.wire hwire tail.valid }
termination_by wires.length

private theorem conjunctionResult_trace_eq (b : CircuitBuilder)
    (wires : List Wire) (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (conjunctionResult b wires hvalid).builder.gates =
        b.gates ++ (conjunctionGateTrace b.gates.length wires).gates ∧
      (conjunctionResult b wires hvalid).wire =
        (conjunctionGateTrace b.gates.length wires).wire := by
  induction wires with
  | nil =>
      simp [conjunctionResult, conjunctionGateTrace, const_wire_eq]
  | cons wire rest ih =>
      let hrest : ∀ old ∈ rest, b.WireValid old :=
        fun old hold => hvalid old (by simp [hold])
      rcases ih hrest with ⟨hgates, hwire⟩
      simp only [conjunctionResult]
      rw [and_gates, hgates]
      simp only [and_wire_eq, conjunctionGateTrace]
      constructor
      · rw [hwire]
        simp [List.append_assoc]
      · rw [hgates]
        simp

/-- Conjoin a list of old valid wires.  The empty conjunction is true. -/
def conjunction (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) : CircuitBuilder × Wire :=
  let result := conjunctionResult b wires hvalid
  (result.builder, result.wire)

/-- The conjunction builder appends exactly its pure tail-first trace. -/
theorem conjunction_gates_eq (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.conjunction wires hvalid).1.gates =
      b.gates ++ (conjunctionGateTrace b.gates.length wires).gates :=
  (conjunctionResult_trace_eq b wires hvalid).1

/-- The conjunction output wire agrees with the pure trace. -/
theorem conjunction_wire_eq_trace (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.conjunction wires hvalid).2 =
      (conjunctionGateTrace b.gates.length wires).wire :=
  (conjunctionResult_trace_eq b wires hvalid).2

/-- A conjunction fold extends its starting builder. -/
theorem conjunction_extends (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    b.Extends (b.conjunction wires hvalid).1 :=
  (conjunctionResult b wires hvalid).extension

/-- A conjunction fold returns a valid fresh output wire. -/
theorem conjunction_wireValid (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.conjunction wires hvalid).1.WireValid (b.conjunction wires hvalid).2 :=
  (conjunctionResult b wires hvalid).valid

private theorem conjunctionResult_delta (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (conjunctionResult b wires hvalid).builder.gates.length =
      b.gates.length + wires.length + 1 := by
  induction wires with
  | nil => simpa [conjunctionResult] using const_gate_delta b true
  | cons wire rest ih =>
      simp only [conjunctionResult]
      let tail := conjunctionResult b rest (fun w hw => hvalid w (by simp [hw]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      have hstep := and_gate_delta tail.builder wire tail.wire hwire tail.valid
      have htail := ih (fun w hw => hvalid w (by simp [hw]))
      dsimp only [tail] at hstep htail ⊢
      simp only [List.length_cons]
      omega

/-- A conjunction fold appends exactly one true seed and one gate per wire. -/
theorem conjunction_gate_delta (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.conjunction wires hvalid).1.gates.length =
      b.gates.length + wires.length + 1 :=
  conjunctionResult_delta b wires hvalid

private theorem conjunctionResult_eval (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) (inputs : Nat → Bool) :
    (conjunctionResult b wires hvalid).builder.evalWire inputs
      (conjunctionResult b wires hvalid).wire =
        wires.all (fun wire => b.evalWire inputs wire) := by
  induction wires with
  | nil => simpa [conjunctionResult] using const_eval b true inputs
  | cons wire rest ih =>
      simp only [conjunctionResult]
      let tail := conjunctionResult b rest (fun w hw => hvalid w (by simp [hw]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      have hgate := and_eval tail.builder wire tail.wire hwire tail.valid inputs
      have htail := ih (fun w hw => hvalid w (by simp [hw]))
      have hold := tail.extension.evalWire_eq inputs (hvalid wire (by simp))
      dsimp only [tail] at hgate htail hold ⊢
      rw [hgate, hold, htail]
      rfl

/-- A conjunction fold evaluates to the Boolean conjunction of the old wire values. -/
theorem conjunction_eval (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) (inputs : Nat → Bool) :
    (b.conjunction wires hvalid).1.evalWire inputs
      (b.conjunction wires hvalid).2 =
        wires.all (fun wire => b.evalWire inputs wire) :=
  conjunctionResult_eval b wires hvalid inputs

/-! ## Tail-first disjunction traces -/

/-- Pure gate-order trace of the tail-first disjunction fold. -/
structure DisjunctionGateTrace where
  gates : List CircuitGate
  wire : Wire
deriving DecidableEq, Repr

/-- The empty disjunction emits a false seed; every source wire then appends
one ordered OR gate. -/
def disjunctionGateTrace (start : Nat) : List Wire → DisjunctionGateTrace
  | [] =>
      { gates := [.const false]
        wire := start }
  | wire :: rest =>
      let tail := disjunctionGateTrace start rest
      let next := start + tail.gates.length
      { gates := tail.gates ++ [.or wire tail.wire]
        wire := next }

@[simp] theorem disjunctionGateTrace_length (start : Nat)
    (wires : List Wire) :
    (disjunctionGateTrace start wires).gates.length = wires.length + 1 := by
  induction wires with
  | nil => rfl
  | cons wire rest ih => simp [disjunctionGateTrace, ih]

private def disjunctionResult (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) : BuiltWire b :=
  match wires with
  | [] =>
      { builder := (b.const false).1
        wire := (b.const false).2
        extension := const_extends b false
        valid := const_wireValid b false }
  | wire :: rest =>
      let tail := disjunctionResult b rest (fun w hw => hvalid w (by simp [hw]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      let next := tail.builder.or wire tail.wire hwire tail.valid
      { builder := next.1
        wire := next.2
        extension := tail.extension.trans
          (or_extends tail.builder wire tail.wire hwire tail.valid)
        valid := or_wireValid tail.builder wire tail.wire hwire tail.valid }
termination_by wires.length

private theorem disjunctionResult_trace_eq (b : CircuitBuilder)
    (wires : List Wire) (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (disjunctionResult b wires hvalid).builder.gates =
        b.gates ++ (disjunctionGateTrace b.gates.length wires).gates ∧
      (disjunctionResult b wires hvalid).wire =
        (disjunctionGateTrace b.gates.length wires).wire := by
  induction wires with
  | nil =>
      simp [disjunctionResult, disjunctionGateTrace, const_wire_eq]
  | cons wire rest ih =>
      let hrest : ∀ old ∈ rest, b.WireValid old :=
        fun old hold => hvalid old (by simp [hold])
      rcases ih hrest with ⟨hgates, hwire⟩
      simp only [disjunctionResult]
      rw [or_gates, hgates]
      simp only [or_wire_eq, disjunctionGateTrace]
      constructor
      · rw [hwire]
        simp [List.append_assoc]
      · rw [hgates]
        simp

/-- Disjoin a list of old valid wires.  The empty disjunction is false. -/
def disjunction (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) : CircuitBuilder × Wire :=
  let result := disjunctionResult b wires hvalid
  (result.builder, result.wire)

/-- The disjunction builder appends exactly its pure tail-first trace. -/
theorem disjunction_gates_eq (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.disjunction wires hvalid).1.gates =
      b.gates ++ (disjunctionGateTrace b.gates.length wires).gates :=
  (disjunctionResult_trace_eq b wires hvalid).1

/-- The disjunction output wire agrees with the pure trace. -/
theorem disjunction_wire_eq_trace (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.disjunction wires hvalid).2 =
      (disjunctionGateTrace b.gates.length wires).wire :=
  (disjunctionResult_trace_eq b wires hvalid).2

/-- A disjunction fold extends its starting builder. -/
theorem disjunction_extends (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    b.Extends (b.disjunction wires hvalid).1 :=
  (disjunctionResult b wires hvalid).extension

/-- A disjunction fold returns a valid fresh output wire. -/
theorem disjunction_wireValid (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.disjunction wires hvalid).1.WireValid (b.disjunction wires hvalid).2 :=
  (disjunctionResult b wires hvalid).valid

private theorem disjunctionResult_delta (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (disjunctionResult b wires hvalid).builder.gates.length =
      b.gates.length + wires.length + 1 := by
  induction wires with
  | nil => simpa [disjunctionResult] using const_gate_delta b false
  | cons wire rest ih =>
      simp only [disjunctionResult]
      let tail := disjunctionResult b rest (fun w hw => hvalid w (by simp [hw]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      have hstep := or_gate_delta tail.builder wire tail.wire hwire tail.valid
      have htail := ih (fun w hw => hvalid w (by simp [hw]))
      dsimp only [tail] at hstep htail ⊢
      simp only [List.length_cons]
      omega

/-- A disjunction fold appends exactly one false seed and one gate per wire. -/
theorem disjunction_gate_delta (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) :
    (b.disjunction wires hvalid).1.gates.length =
      b.gates.length + wires.length + 1 :=
  disjunctionResult_delta b wires hvalid

private theorem disjunctionResult_eval (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) (inputs : Nat → Bool) :
    (disjunctionResult b wires hvalid).builder.evalWire inputs
      (disjunctionResult b wires hvalid).wire =
        wires.any (fun wire => b.evalWire inputs wire) := by
  induction wires with
  | nil => simpa [disjunctionResult] using const_eval b false inputs
  | cons wire rest ih =>
      simp only [disjunctionResult]
      let tail := disjunctionResult b rest (fun w hw => hvalid w (by simp [hw]))
      let hwire : tail.builder.WireValid wire :=
        tail.extension.wireValid (hvalid wire (by simp))
      have hgate := or_eval tail.builder wire tail.wire hwire tail.valid inputs
      have htail := ih (fun w hw => hvalid w (by simp [hw]))
      have hold := tail.extension.evalWire_eq inputs (hvalid wire (by simp))
      dsimp only [tail] at hgate htail hold ⊢
      rw [hgate, hold, htail]
      rfl

/-- A disjunction fold evaluates to the Boolean disjunction of the old wire values. -/
theorem disjunction_eval (b : CircuitBuilder) (wires : List Wire)
    (hvalid : ∀ wire ∈ wires, b.WireValid wire) (inputs : Nat → Bool) :
    (b.disjunction wires hvalid).1.evalWire inputs
      (b.disjunction wires hvalid).2 =
        wires.any (fun wire => b.evalWire inputs wire) :=
  disjunctionResult_eval b wires hvalid inputs

/-! ## Equality and multiplexing -/

/-- Pure five-gate trace of the Boolean equality (XNOR) implementation. -/
structure BoolEqGateTrace where
  gates : List CircuitGate
  wire : Wire
deriving DecidableEq, Repr

/-- Exact primitive gate order and fresh-wire references used by Boolean
equality at a given starting gate index. -/
def boolEqGateTrace (start left right : Nat) : BoolEqGateTrace :=
  { gates :=
      [.not left, .not right, .and left right,
        .and start (start + 1), .or (start + 2) (start + 3)]
    wire := start + 4 }

/-- Boolean equality always emits five primitive gates. -/
@[simp] theorem boolEqGateTrace_length (start left right : Nat) :
    (boolEqGateTrace start left right).gates.length = 5 := by
  rfl

private def eqResult (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) : BuiltWire b :=
  let leftNot := b.not left hleft
  let hright₁ := (not_extends b left hleft).wireValid hright
  let rightNot := leftNot.1.not right hright₁
  let hleft₂ := ((not_extends b left hleft).trans
    (not_extends leftNot.1 right hright₁)).wireValid hleft
  let hright₂ := ((not_extends b left hleft).trans
    (not_extends leftNot.1 right hright₁)).wireValid hright
  let bothTrue := rightNot.1.and left right hleft₂ hright₂
  let hextTrue := (not_extends b left hleft).trans
    ((not_extends leftNot.1 right hright₁).trans
      (and_extends rightNot.1 left right hleft₂ hright₂))
  let hleftNot₃ := ((not_extends leftNot.1 right hright₁).trans
    (and_extends rightNot.1 left right hleft₂ hright₂)).wireValid
      (not_wireValid b left hleft)
  let hrightNot₃ := (and_extends rightNot.1 left right hleft₂ hright₂).wireValid
    (not_wireValid leftNot.1 right hright₁)
  let bothFalse := bothTrue.1.and leftNot.2 rightNot.2 hleftNot₃ hrightNot₃
  let hextFalse := hextTrue.trans
    (and_extends bothTrue.1 leftNot.2 rightNot.2 hleftNot₃ hrightNot₃)
  let hbothTrue := (and_extends bothTrue.1 leftNot.2 rightNot.2
    hleftNot₃ hrightNot₃).wireValid
    (and_wireValid rightNot.1 left right hleft₂ hright₂)
  let hbothFalse := and_wireValid bothTrue.1 leftNot.2 rightNot.2
    hleftNot₃ hrightNot₃
  let output := bothFalse.1.or bothTrue.2 bothFalse.2 hbothTrue hbothFalse
  { builder := output.1
    wire := output.2
    extension := hextFalse.trans
      (or_extends bothFalse.1 bothTrue.2 bothFalse.2 hbothTrue hbothFalse)
    valid := or_wireValid bothFalse.1 bothTrue.2 bothFalse.2 hbothTrue hbothFalse }

private theorem eqResult_delta (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (eqResult b left right hleft hright).builder.gates.length =
      b.gates.length + 5 := by
  unfold eqResult
  dsimp only
  rw [or_gate_delta, and_gate_delta, and_gate_delta, not_gate_delta,
    not_gate_delta]

private theorem eqResult_eval (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right)
    (inputs : Nat → Bool) :
    (eqResult b left right hleft hright).builder.evalWire inputs
        (eqResult b left right hleft hright).wire =
      decide (b.evalWire inputs left = b.evalWire inputs right) := by
  unfold eqResult
  dsimp only
  let leftNot := b.not left hleft
  let hright₁ := (not_extends b left hleft).wireValid hright
  let rightNot := leftNot.1.not right hright₁
  let hextNot := (not_extends b left hleft).trans
    (not_extends leftNot.1 right hright₁)
  let hleft₂ := hextNot.wireValid hleft
  let hright₂ := hextNot.wireValid hright
  let bothTrue := rightNot.1.and left right hleft₂ hright₂
  let hextTrue := hextNot.trans
    (and_extends rightNot.1 left right hleft₂ hright₂)
  let hleftNot₃ := ((not_extends leftNot.1 right hright₁).trans
    (and_extends rightNot.1 left right hleft₂ hright₂)).wireValid
      (not_wireValid b left hleft)
  let hrightNot₃ := (and_extends rightNot.1 left right hleft₂ hright₂).wireValid
    (not_wireValid leftNot.1 right hright₁)
  let bothFalse := bothTrue.1.and leftNot.2 rightNot.2 hleftNot₃ hrightNot₃
  let hextFalse := hextTrue.trans
    (and_extends bothTrue.1 leftNot.2 rightNot.2 hleftNot₃ hrightNot₃)
  let hbothTrue := (and_extends bothTrue.1 leftNot.2 rightNot.2
    hleftNot₃ hrightNot₃).wireValid
      (and_wireValid rightNot.1 left right hleft₂ hright₂)
  let hbothFalse := and_wireValid bothTrue.1 leftNot.2 rightNot.2
    hleftNot₃ hrightNot₃
  rw [or_eval bothFalse.1 bothTrue.2 bothFalse.2 hbothTrue hbothFalse]
  rw [(and_extends bothTrue.1 leftNot.2 rightNot.2
    hleftNot₃ hrightNot₃).evalWire_eq inputs
    (and_wireValid rightNot.1 left right hleft₂ hright₂)]
  rw [and_eval bothTrue.1 leftNot.2 rightNot.2 hleftNot₃ hrightNot₃]
  rw [(and_extends rightNot.1 left right hleft₂ hright₂).evalWire_eq inputs
    (not_wireValid leftNot.1 right hright₁)]
  rw [(and_extends rightNot.1 left right hleft₂ hright₂).evalWire_eq inputs
    ((not_extends leftNot.1 right hright₁).wireValid (not_wireValid b left hleft))]
  rw [and_eval rightNot.1 left right hleft₂ hright₂]
  rw [hextNot.evalWire_eq inputs hleft, hextNot.evalWire_eq inputs hright]
  rw [not_eval leftNot.1 right hright₁ inputs]
  rw [(not_extends b left hleft).evalWire_eq inputs hright]
  rw [(not_extends leftNot.1 right hright₁).evalWire_eq inputs
    (not_wireValid b left hleft)]
  rw [not_eval b left hleft inputs]
  cases b.evalWire inputs left <;> cases b.evalWire inputs right <;> decide

/-- Build Boolean equality (XNOR) for two old valid wires. -/
def eq (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    CircuitBuilder × Wire :=
  let result := eqResult b left right hleft hright
  (result.builder, result.wire)

/-- The equality builder appends exactly the public five-gate trace. -/
theorem eq_gates_eq (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.eq left right hleft hright).1.gates =
      b.gates ++ (boolEqGateTrace b.gates.length left right).gates := by
  unfold eq eqResult
  dsimp only
  rw [or_gates, and_gates, and_gates, not_gates, not_gates]
  simp only [not_wire_eq, and_wire_eq, boolEqGateTrace]
  simp [List.append_assoc]

/-- The equality builder returns the output wire named by the public trace. -/
theorem eq_wire_eq_trace (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.eq left right hleft hright).2 =
      (boolEqGateTrace b.gates.length left right).wire := by
  unfold eq eqResult
  dsimp only
  simp only [or_wire_eq, and_gates, not_gates, List.length_append,
    List.length_singleton, boolEqGateTrace]

/-- Boolean equality extends the starting prefix. -/
theorem eq_extends (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    b.Extends (b.eq left right hleft hright).1 :=
  (eqResult b left right hleft hright).extension

/-- Boolean equality returns a valid output wire. -/
theorem eq_wireValid (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.eq left right hleft hright).1.WireValid
      (b.eq left right hleft hright).2 :=
  (eqResult b left right hleft hright).valid

/-- The XNOR implementation appends exactly five primitive gates. -/
theorem eq_gate_delta (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right) :
    (b.eq left right hleft hright).1.gates.length = b.gates.length + 5 :=
  eqResult_delta b left right hleft hright

/-- Boolean equality is true exactly when the two old wire values agree. -/
theorem eq_eval (b : CircuitBuilder) (left right : Wire)
    (hleft : b.WireValid left) (hright : b.WireValid right)
    (inputs : Nat → Bool) :
    (b.eq left right hleft hright).1.evalWire inputs
        (b.eq left right hleft hright).2 =
      decide (b.evalWire inputs left = b.evalWire inputs right) := by
  exact eqResult_eval b left right hleft hright inputs

private def muxResult (b : CircuitBuilder) (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) : BuiltWire b :=
  let conditionNot := b.not condition hcondition
  let hcondition₁ := (not_extends b condition hcondition).wireValid hcondition
  let htrue₁ := (not_extends b condition hcondition).wireValid htrue
  let trueArm := conditionNot.1.and condition whenTrue hcondition₁ htrue₁
  let hextTrue := (not_extends b condition hcondition).trans
    (and_extends conditionNot.1 condition whenTrue hcondition₁ htrue₁)
  let hconditionNot₂ := (and_extends conditionNot.1 condition whenTrue
    hcondition₁ htrue₁).wireValid
    (not_wireValid b condition hcondition)
  let hfalse₂ := hextTrue.wireValid hfalse
  let falseArm := trueArm.1.and conditionNot.2 whenFalse hconditionNot₂ hfalse₂
  let hextFalse := hextTrue.trans
    (and_extends trueArm.1 conditionNot.2 whenFalse hconditionNot₂ hfalse₂)
  let htrueArm := (and_extends trueArm.1 conditionNot.2 whenFalse
    hconditionNot₂ hfalse₂).wireValid
    (and_wireValid conditionNot.1 condition whenTrue hcondition₁ htrue₁)
  let hfalseArm := and_wireValid trueArm.1 conditionNot.2 whenFalse
    hconditionNot₂ hfalse₂
  let output := falseArm.1.or trueArm.2 falseArm.2 htrueArm hfalseArm
  { builder := output.1
    wire := output.2
    extension := hextFalse.trans
      (or_extends falseArm.1 trueArm.2 falseArm.2 htrueArm hfalseArm)
    valid := or_wireValid falseArm.1 trueArm.2 falseArm.2 htrueArm hfalseArm }

private theorem muxResult_delta (b : CircuitBuilder)
    (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) :
    (muxResult b condition whenTrue whenFalse hcondition htrue hfalse).builder.gates.length =
      b.gates.length + 4 := by
  unfold muxResult
  dsimp only
  rw [or_gate_delta, and_gate_delta, and_gate_delta, not_gate_delta]

private theorem muxResult_eval (b : CircuitBuilder)
    (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) (inputs : Nat → Bool) :
    (muxResult b condition whenTrue whenFalse hcondition htrue hfalse).builder.evalWire
        inputs (muxResult b condition whenTrue whenFalse hcondition htrue hfalse).wire =
      if b.evalWire inputs condition then
        b.evalWire inputs whenTrue
      else b.evalWire inputs whenFalse := by
  unfold muxResult
  dsimp only
  let conditionNot := b.not condition hcondition
  let hcondition₁ := (not_extends b condition hcondition).wireValid hcondition
  let htrue₁ := (not_extends b condition hcondition).wireValid htrue
  let trueArm := conditionNot.1.and condition whenTrue hcondition₁ htrue₁
  let hextTrue := (not_extends b condition hcondition).trans
    (and_extends conditionNot.1 condition whenTrue hcondition₁ htrue₁)
  let hconditionNot₂ := (and_extends conditionNot.1 condition whenTrue
    hcondition₁ htrue₁).wireValid (not_wireValid b condition hcondition)
  let hfalse₂ := hextTrue.wireValid hfalse
  let falseArm := trueArm.1.and conditionNot.2 whenFalse hconditionNot₂ hfalse₂
  let hextFalse := hextTrue.trans
    (and_extends trueArm.1 conditionNot.2 whenFalse hconditionNot₂ hfalse₂)
  let htrueArm := (and_extends trueArm.1 conditionNot.2 whenFalse
    hconditionNot₂ hfalse₂).wireValid
      (and_wireValid conditionNot.1 condition whenTrue hcondition₁ htrue₁)
  let hfalseArm := and_wireValid trueArm.1 conditionNot.2 whenFalse
    hconditionNot₂ hfalse₂
  rw [or_eval falseArm.1 trueArm.2 falseArm.2 htrueArm hfalseArm]
  rw [(and_extends trueArm.1 conditionNot.2 whenFalse
    hconditionNot₂ hfalse₂).evalWire_eq inputs
    (and_wireValid conditionNot.1 condition whenTrue hcondition₁ htrue₁)]
  rw [and_eval trueArm.1 conditionNot.2 whenFalse hconditionNot₂ hfalse₂]
  rw [(and_extends conditionNot.1 condition whenTrue hcondition₁ htrue₁).evalWire_eq
    inputs (not_wireValid b condition hcondition)]
  rw [hextTrue.evalWire_eq inputs hfalse]
  rw [and_eval conditionNot.1 condition whenTrue hcondition₁ htrue₁]
  rw [(not_extends b condition hcondition).evalWire_eq inputs hcondition]
  rw [(not_extends b condition hcondition).evalWire_eq inputs htrue]
  rw [not_eval b condition hcondition inputs]
  cases b.evalWire inputs condition <;>
    cases b.evalWire inputs whenTrue <;>
      cases b.evalWire inputs whenFalse <;> rfl

/-- Build a Boolean multiplexer selecting between two old valid wires. -/
def mux (b : CircuitBuilder) (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) : CircuitBuilder × Wire :=
  let result := muxResult b condition whenTrue whenFalse hcondition htrue hfalse
  (result.builder, result.wire)

/-- A multiplexer extends the starting prefix. -/
theorem mux_extends (b : CircuitBuilder) (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) :
    b.Extends (b.mux condition whenTrue whenFalse hcondition htrue hfalse).1 :=
  (muxResult b condition whenTrue whenFalse hcondition htrue hfalse).extension

/-- A multiplexer returns a valid output wire. -/
theorem mux_wireValid (b : CircuitBuilder) (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) :
    (b.mux condition whenTrue whenFalse hcondition htrue hfalse).1.WireValid
      (b.mux condition whenTrue whenFalse hcondition htrue hfalse).2 :=
  (muxResult b condition whenTrue whenFalse hcondition htrue hfalse).valid

/-- The multiplexer implementation appends exactly four primitive gates. -/
theorem mux_gate_delta (b : CircuitBuilder) (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) :
    (b.mux condition whenTrue whenFalse hcondition htrue hfalse).1.gates.length =
      b.gates.length + 4 :=
  muxResult_delta b condition whenTrue whenFalse hcondition htrue hfalse

/-- A multiplexer evaluates to its true arm when the condition is true and to
its false arm otherwise. -/
theorem mux_eval (b : CircuitBuilder) (condition whenTrue whenFalse : Wire)
    (hcondition : b.WireValid condition) (htrue : b.WireValid whenTrue)
    (hfalse : b.WireValid whenFalse) (inputs : Nat → Bool) :
    (b.mux condition whenTrue whenFalse hcondition htrue hfalse).1.evalWire inputs
        (b.mux condition whenTrue whenFalse hcondition htrue hfalse).2 =
      if b.evalWire inputs condition then
        b.evalWire inputs whenTrue
      else b.evalWire inputs whenFalse := by
  exact muxResult_eval b condition whenTrue whenFalse hcondition htrue hfalse inputs

/-! ## Closing a builder -/

/-- Select a valid builder wire as the output of a general circuit. -/
def finish (b : CircuitBuilder) (output : Wire)
    (_houtput : b.WireValid output) : Circuit where
  inputCount := b.inputCount
  gates := b.gates
  output := output

/-- Closing a builder at a valid wire produces a well-formed circuit. -/
theorem finish_wellFormed (b : CircuitBuilder) (output : Wire)
    (houtput : b.WireValid output) : (b.finish output houtput).WellFormed :=
  ⟨houtput, b.valid⟩

/-- Closing the builder does not change the selected wire's semantics. -/
theorem finish_eval (b : CircuitBuilder) (output : Wire)
    (houtput : b.WireValid output) (inputs : Nat → Bool) :
    (b.finish output houtput).eval inputs = b.evalWire inputs output := by
  rfl

end CircuitBuilder

end CLRS.Chapter34.Turing.CookLevin
