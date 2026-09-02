import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder

/-!
# CLRS Section 34.4 - Finite-family circuit combinators

Symbolic Cook--Levin rows repeatedly apply the same Boolean operation to a
finite family of wires.  This module packages two such operations without
depending on the tableau representation: a multiplexer sharing one selector
negation across every coordinate, and a streaming pointwise equality test.

Main results:

- Definition {lit}`CircuitBuilder.muxFin`: a proof-carrying family multiplexer
  with exact gate delta {lit}`3 * n + 1`.
- Definition {lit}`CircuitBuilder.eqFin`: a proof-carrying pointwise equality
  test with exact gate delta {lit}`6 * n + 1`.
- Definitions {lit}`muxFinGateTrace` and {lit}`eqFinGateTrace`, together with
  {lit}`muxFin_gates_eq` and {lit}`eqFin_gates_eq`: exact ordered gate streams,
  fresh-wire references, and output-wire identity for both kernels.
- Theorems {lit}`CircuitBuilder.muxFin_eval` and
  {lit}`CircuitBuilder.eqFin_eval_iff`: exact evaluation contracts, including
  the empty family.

Layer boundary:

- Symbolic stack and configuration operations using these generic combinators
  belong to the downstream tableau stack-primitive layer.
- Recursive bundled-statement compilation is supplied by downstream
  {lit}`StatementCircuits`, while {lit}`TransitionCircuits` now supplies
  finite-label dispatch and the local step check.  Downstream fresh-row,
  tableau-constraint, and assembly modules supply non-aliasing allocation and
  verified whole-tableau assembly.
-/

namespace CLRS.Chapter34.Turing.CookLevin

namespace CircuitBuilder

/-! ## A shared-negation finite-family multiplexer -/

/-- Exact gate suffix emitted by the coordinate body of {lit}`muxFin`.  The
starting index is the first gate after the shared selector negation. -/
def muxFinBodyGateTrace (start selector selectorNot : Nat) :
    (n : Nat) → (whenTrue whenFalse : Fin n → Wire) → List CircuitGate
  | 0, _, _ => []
  | n + 1, whenTrue, whenFalse =>
      let previous := muxFinBodyGateTrace start selector selectorNot n
        (fun i => whenTrue i.castSucc) (fun i => whenFalse i.castSucc)
      let trueArm := start + previous.length
      let falseArm := trueArm + 1
      previous ++
        [.and selector (whenTrue (Fin.last n)),
          .and selectorNot (whenFalse (Fin.last n)),
          .or trueArm falseArm]

/-- Exact gate order of {lit}`muxFin`, including its shared selector negation. -/
def muxFinGateTrace (start selector : Nat) {n : Nat}
    (whenTrue whenFalse : Fin n → Wire) : List CircuitGate :=
  .not selector :: muxFinBodyGateTrace (start + 1) selector start n
    whenTrue whenFalse

/-- The multiplexer body emits exactly three gates per coordinate. -/
@[simp] theorem muxFinBodyGateTrace_length (start selector selectorNot : Nat)
    (n : Nat) (whenTrue whenFalse : Fin n → Wire) :
    (muxFinBodyGateTrace start selector selectorNot n
      whenTrue whenFalse).length = 3 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [muxFinBodyGateTrace, ih]
      omega

/-- The complete multiplexer trace has one shared negation and three gates
per coordinate. -/
@[simp] theorem muxFinGateTrace_length (start selector : Nat) {n : Nat}
    (whenTrue whenFalse : Fin n → Wire) :
    (muxFinGateTrace start selector whenTrue whenFalse).length = 3 * n + 1 := by
  simp [muxFinGateTrace]

/-- Proof-carrying result of multiplexing two finite wire families. -/
structure MuxFinResult (base : CircuitBuilder) {n : Nat}
    (selector : Wire) (whenTrue whenFalse : Fin n → Wire) where
  /-- Builder after the shared selector negation and coordinate gates. -/
  builder : CircuitBuilder
  /-- One selected output wire per finite coordinate. -/
  wires : Fin n → Wire
  /-- The result preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Every output wire belongs to the result builder. -/
  valid : ∀ i, builder.WireValid (wires i)
  /-- One shared negation and three gates per coordinate are emitted. -/
  gate_delta : builder.gates.length = base.gates.length + (3 * n + 1)
  /-- Every output evaluates to the arm selected by the original condition. -/
  eval : ∀ inputs i, builder.evalWire inputs (wires i) =
    if base.evalWire inputs selector then
      base.evalWire inputs (whenTrue i)
    else
      base.evalWire inputs (whenFalse i)

private structure MuxFinBodyResult (start : CircuitBuilder) {n : Nat}
    (selector selectorNot : Wire) (whenTrue whenFalse : Fin n → Wire) where
  builder : CircuitBuilder
  wires : Fin n → Wire
  extension : start.Extends builder
  valid : ∀ i, builder.WireValid (wires i)
  gate_delta : builder.gates.length = start.gates.length + 3 * n
  eval : ∀ inputs i, builder.evalWire inputs (wires i) =
    ((start.evalWire inputs selector && start.evalWire inputs (whenTrue i)) ||
      (start.evalWire inputs selectorNot && start.evalWire inputs (whenFalse i)))

private def muxFinBody (start : CircuitBuilder)
    (selector selectorNot : Wire) :
    (n : Nat) → (whenTrue whenFalse : Fin n → Wire) →
      start.WireValid selector → start.WireValid selectorNot →
      (∀ i, start.WireValid (whenTrue i)) →
      (∀ i, start.WireValid (whenFalse i)) →
      MuxFinBodyResult start selector selectorNot whenTrue whenFalse
  | 0, whenTrue, whenFalse, _, _, _, _ =>
      { builder := start
        wires := fun i => Fin.elim0 i
        extension := Extends.refl start
        valid := fun i => Fin.elim0 i
        gate_delta := by simp
        eval := fun _ i => Fin.elim0 i }
  | n + 1, whenTrue, whenFalse, hselector, hselectorNot, htrue, hfalse => by
      let previous := muxFinBody start selector selectorNot n
        (fun i => whenTrue i.castSucc) (fun i => whenFalse i.castSucc)
        hselector hselectorNot (fun i => htrue i.castSucc)
        (fun i => hfalse i.castSucc)
      have hselectorPrevious := previous.extension.wireValid hselector
      have htrueLast := previous.extension.wireValid (htrue (Fin.last n))
      let trueArm := previous.builder.and selector (whenTrue (Fin.last n))
        hselectorPrevious htrueLast
      let hextTrue := and_extends previous.builder selector
        (whenTrue (Fin.last n)) hselectorPrevious htrueLast
      have hselectorNotTrue := hextTrue.wireValid
        (previous.extension.wireValid hselectorNot)
      have hfalseLast := hextTrue.wireValid
        (previous.extension.wireValid (hfalse (Fin.last n)))
      let falseArm := trueArm.1.and selectorNot (whenFalse (Fin.last n))
        hselectorNotTrue hfalseLast
      let hextFalse := and_extends trueArm.1 selectorNot
        (whenFalse (Fin.last n)) hselectorNotTrue hfalseLast
      have htrueArm := hextFalse.wireValid
        (and_wireValid previous.builder selector (whenTrue (Fin.last n))
          hselectorPrevious htrueLast)
      have hfalseArm := and_wireValid trueArm.1 selectorNot
        (whenFalse (Fin.last n)) hselectorNotTrue hfalseLast
      let output := falseArm.1.or trueArm.2 falseArm.2 htrueArm hfalseArm
      let hextOutput := or_extends falseArm.1 trueArm.2 falseArm.2
        htrueArm hfalseArm
      let stepExtension := hextTrue.trans (hextFalse.trans hextOutput)
      let extension := previous.extension.trans stepExtension
      let wires : Fin (n + 1) → Wire := fun i =>
        if hi : i.val < n then previous.wires ⟨i.val, hi⟩ else output.2
      refine
        { builder := output.1
          wires := wires
          extension := extension
          valid := ?_
          gate_delta := ?_
          eval := ?_ }
      · intro i
        simp only [wires]
        split
        next hi => exact stepExtension.wireValid (previous.valid ⟨i.val, hi⟩)
        next =>
          simpa only [output] using
            (or_wireValid falseArm.1 trueArm.2 falseArm.2 htrueArm hfalseArm)
      · dsimp only [output, falseArm, trueArm]
        rw [or_gate_delta, and_gate_delta, and_gate_delta,
          previous.gate_delta]
        omega
      · intro inputs i
        simp only [wires]
        split
        next hi =>
          rw [stepExtension.evalWire_eq inputs (previous.valid ⟨i.val, hi⟩)]
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
          dsimp only [output, falseArm, trueArm]
          rw [or_eval]
          rw [and_eval trueArm.1 selectorNot (whenFalse (Fin.last n))
            hselectorNotTrue hfalseLast]
          rw [hextTrue.evalWire_eq inputs
            (previous.extension.wireValid hselectorNot)]
          rw [hextTrue.evalWire_eq inputs
            (previous.extension.wireValid (hfalse (Fin.last n)))]
          rw [hextFalse.evalWire_eq inputs
            (and_wireValid previous.builder selector (whenTrue (Fin.last n))
              hselectorPrevious htrueLast)]
          rw [and_eval previous.builder selector (whenTrue (Fin.last n))
            hselectorPrevious htrueLast]
          rw [previous.extension.evalWire_eq inputs hselector]
          rw [previous.extension.evalWire_eq inputs (htrue (Fin.last n))]
          rw [previous.extension.evalWire_eq inputs hselectorNot]
          rw [previous.extension.evalWire_eq inputs (hfalse (Fin.last n))]

/-- The selected output for coordinate `i` is the third fresh body gate for
that coordinate. -/
private theorem muxFinBody_wires_eq (start : CircuitBuilder)
    (selector selectorNot : Wire) :
    ∀ (n : Nat) (whenTrue whenFalse : Fin n → Wire)
      (hselector : start.WireValid selector)
      (hselectorNot : start.WireValid selectorNot)
      (htrue : ∀ i, start.WireValid (whenTrue i))
      (hfalse : ∀ i, start.WireValid (whenFalse i)) (i : Fin n),
      (muxFinBody start selector selectorNot n whenTrue whenFalse
        hselector hselectorNot htrue hfalse).wires i =
        start.gates.length + 2 + 3 * i.val := by
  intro n
  induction n with
  | zero =>
      intro whenTrue whenFalse hselector hselectorNot htrue hfalse i
      exact Fin.elim0 i
  | succ n ih =>
      intro whenTrue whenFalse hselector hselectorNot htrue hfalse i
      simp only [muxFinBody]
      split
      next hi =>
        rw [ih (fun j => whenTrue j.castSucc)
          (fun j => whenFalse j.castSucc) hselector hselectorNot
          (fun j => htrue j.castSucc) (fun j => hfalse j.castSucc)
          ⟨i.val, hi⟩]
      next hi =>
        have hilast : i = Fin.last n := by
          apply Fin.ext
          simp
          omega
        subst i
        rw [or_wire_eq, and_gate_delta, and_gate_delta]
        rw [(muxFinBody start selector selectorNot n
          (fun j => whenTrue j.castSucc) (fun j => whenFalse j.castSucc)
          hselector hselectorNot (fun j => htrue j.castSucc)
          (fun j => hfalse j.castSucc)).gate_delta]
        simp
        ring

private theorem muxFinBody_gates_eq (start : CircuitBuilder)
    (selector selectorNot : Wire) :
    (n : Nat) → (whenTrue whenFalse : Fin n → Wire) →
      (hselector : start.WireValid selector) →
      (hselectorNot : start.WireValid selectorNot) →
      (htrue : ∀ i, start.WireValid (whenTrue i)) →
      (hfalse : ∀ i, start.WireValid (whenFalse i)) →
      (muxFinBody start selector selectorNot n whenTrue whenFalse
        hselector hselectorNot htrue hfalse).builder.gates =
        start.gates ++ muxFinBodyGateTrace start.gates.length selector
          selectorNot n whenTrue whenFalse := by
  intro n
  induction n with
  | zero =>
      intro whenTrue whenFalse hselector hselectorNot htrue hfalse
      simp [muxFinBody, muxFinBodyGateTrace]
  | succ n ih =>
      intro whenTrue whenFalse hselector hselectorNot htrue hfalse
      simp only [muxFinBody]
      have hprevious := ih (fun i => whenTrue i.castSucc)
        (fun i => whenFalse i.castSucc) hselector hselectorNot
        (fun i => htrue i.castSucc) (fun i => hfalse i.castSucc)
      rw [or_gates, and_gates, and_gates, hprevious]
      simp only [and_wire_eq]
      have hpreviousLength := congrArg List.length hprevious
      simp only [List.length_append] at hpreviousLength
      simp [muxFinBodyGateTrace, List.append_assoc, hpreviousLength]

/-- Multiplex two finite wire families using one shared selector negation.

The construction follows the same one-negation path when {lean}`n = 0`, so its
exact cost remains {lean}`3 * n + 1` without a zero-size special case. -/
def muxFin (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) :
    MuxFinResult base selector whenTrue whenFalse := by
  let selectorNot := base.not selector hselector
  let hextNot := not_extends base selector hselector
  let body := muxFinBody selectorNot.1 selector selectorNot.2 n whenTrue whenFalse
    (hextNot.wireValid hselector) (not_wireValid base selector hselector)
    (fun i => hextNot.wireValid (htrue i))
    (fun i => hextNot.wireValid (hfalse i))
  refine
    { builder := body.builder
      wires := body.wires
      extension := hextNot.trans body.extension
      valid := body.valid
      gate_delta := ?_
      eval := ?_ }
  · rw [body.gate_delta, not_gate_delta]
    omega
  · intro inputs i
    rw [body.eval]
    rw [hextNot.evalWire_eq inputs hselector]
    rw [not_eval base selector hselector inputs]
    rw [hextNot.evalWire_eq inputs (htrue i)]
    rw [hextNot.evalWire_eq inputs (hfalse i)]
    cases base.evalWire inputs selector <;>
      cases base.evalWire inputs (whenTrue i) <;>
        cases base.evalWire inputs (whenFalse i) <;> rfl

/-- A finite-family multiplexer preserves the complete input prefix. -/
theorem muxFin_extends (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) :
    base.Extends (muxFin base selector whenTrue whenFalse hselector htrue hfalse).builder :=
  (muxFin base selector whenTrue whenFalse hselector htrue hfalse).extension

/-- Every finite-family multiplexer output is valid in its result builder. -/
theorem muxFin_wireValid (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) (i : Fin n) :
    (muxFin base selector whenTrue whenFalse hselector htrue hfalse).builder.WireValid
      ((muxFin base selector whenTrue whenFalse hselector htrue hfalse).wires i) :=
  (muxFin base selector whenTrue whenFalse hselector htrue hfalse).valid i

/-- A finite-family multiplexer emits exactly one shared negation and three
gates per coordinate. -/
theorem muxFin_gate_delta (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) :
    (muxFin base selector whenTrue whenFalse hselector htrue hfalse).builder.gates.length =
      base.gates.length + (3 * n + 1) :=
  (muxFin base selector whenTrue whenFalse hselector htrue hfalse).gate_delta

/-- Exact global wire number of every finite-family multiplexer output. -/
theorem muxFin_wire_eq (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) (i : Fin n) :
    (muxFin base selector whenTrue whenFalse hselector htrue hfalse).wires i =
      base.gates.length + 3 + 3 * i.val := by
  unfold muxFin
  dsimp only
  rw [muxFinBody_wires_eq]
  rw [not_gate_delta]

/-- Every finite-family multiplexer coordinate evaluates to the selected arm. -/
theorem muxFin_eval (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) (inputs : Nat → Bool)
    (i : Fin n) :
    (muxFin base selector whenTrue whenFalse hselector htrue hfalse).builder.evalWire
        inputs ((muxFin base selector whenTrue whenFalse hselector htrue hfalse).wires i) =
      if base.evalWire inputs selector then
        base.evalWire inputs (whenTrue i)
      else
      base.evalWire inputs (whenFalse i) :=
  (muxFin base selector whenTrue whenFalse hselector htrue hfalse).eval inputs i

/-- The finite-family multiplexer appends exactly its public gate trace, not
merely the same number of gates. -/
theorem muxFin_gates_eq (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire) (hselector : base.WireValid selector)
    (htrue : ∀ i, base.WireValid (whenTrue i))
    (hfalse : ∀ i, base.WireValid (whenFalse i)) :
    (muxFin base selector whenTrue whenFalse hselector htrue hfalse).builder.gates =
      base.gates ++ muxFinGateTrace base.gates.length selector
        whenTrue whenFalse := by
  unfold muxFin muxFinGateTrace
  dsimp only
  rw [muxFinBody_gates_eq, not_gates]
  simp [not_wire_eq, List.append_assoc]

/-- The finite-family multiplexer result is independent of validity-proof
choices. -/
theorem muxFin_proof_irrel (base : CircuitBuilder) {n : Nat} (selector : Wire)
    (whenTrue whenFalse : Fin n → Wire)
    (hselector₁ hselector₂ : base.WireValid selector)
    (htrue₁ htrue₂ : ∀ i, base.WireValid (whenTrue i))
    (hfalse₁ hfalse₂ : ∀ i, base.WireValid (whenFalse i)) :
    muxFin base selector whenTrue whenFalse hselector₁ htrue₁ hfalse₁ =
      muxFin base selector whenTrue whenFalse hselector₂ htrue₂ hfalse₂ := by
  rfl

/-! ## Streaming finite-family equality -/

/-- Pure trace package for the streaming body of {lit}`eqFin`. -/
structure EqFinGateTrace where
  /-- Gates emitted after the caller-supplied seed. -/
  gates : List CircuitGate
  /-- Wire containing the aggregate equality result. -/
  wire : Wire
deriving DecidableEq, Repr

/-- Exact recursive trace of the equality body.  Each coordinate emits the
five-gate Boolean equality followed immediately by one aggregate AND. -/
def eqFinBodyGateTrace (start seed : Nat) :
    (n : Nat) → (left right : Fin n → Wire) → EqFinGateTrace
  | 0, _, _ => { gates := [], wire := seed }
  | n + 1, left, right =>
      let previous := eqFinBodyGateTrace start seed n
        (fun i => left i.castSucc) (fun i => right i.castSucc)
      let matched := boolEqGateTrace (start + previous.gates.length)
        (left (Fin.last n)) (right (Fin.last n))
      { gates := previous.gates ++ matched.gates ++
          [.and previous.wire matched.wire]
        wire := start + previous.gates.length + matched.gates.length }

/-- Exact gate trace of {lit}`eqFin`, including its initial true seed. -/
def eqFinGateTrace (start : Nat) {n : Nat}
    (left right : Fin n → Wire) : EqFinGateTrace :=
  let body := eqFinBodyGateTrace (start + 1) start n left right
  { gates := .const true :: body.gates
    wire := body.wire }

/-- The streaming equality body emits five XNOR gates and one aggregate AND
per coordinate. -/
@[simp] theorem eqFinBodyGateTrace_length (start seed : Nat) (n : Nat)
    (left right : Fin n → Wire) :
    (eqFinBodyGateTrace start seed n left right).gates.length = 6 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [eqFinBodyGateTrace, ih]
      omega

/-- The complete family-equality trace has one true seed and six gates per
coordinate. -/
@[simp] theorem eqFinGateTrace_length (start : Nat) {n : Nat}
    (left right : Fin n → Wire) :
    (eqFinGateTrace start left right).gates.length = 6 * n + 1 := by
  simp [eqFinGateTrace]

/-- Proof-carrying result of comparing two finite wire families pointwise. -/
structure EqFinResult (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) where
  /-- Builder after the true seed and streaming equality aggregate. -/
  builder : CircuitBuilder
  /-- Output wire asserting pointwise equality. -/
  wire : Wire
  /-- The result preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- The equality output belongs to the result builder. -/
  valid : builder.WireValid wire
  /-- One true seed and six gates per coordinate are emitted. -/
  gate_delta : builder.gates.length = base.gates.length + (6 * n + 1)
  /-- The output is true exactly when every pair of source values agrees. -/
  eval : ∀ inputs, builder.evalWire inputs wire = true ↔
    ∀ i, base.evalWire inputs (left i) = base.evalWire inputs (right i)

private structure EqFinBodyResult (start : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (seed : Wire) where
  builder : CircuitBuilder
  wire : Wire
  extension : start.Extends builder
  valid : builder.WireValid wire
  gate_delta : builder.gates.length = start.gates.length + 6 * n
  eval : ∀ inputs, builder.evalWire inputs wire = true ↔
    start.evalWire inputs seed = true ∧
      ∀ i, start.evalWire inputs (left i) = start.evalWire inputs (right i)

private def eqFinBody (start : CircuitBuilder) (seed : Wire) :
    (n : Nat) → (left right : Fin n → Wire) → start.WireValid seed →
      (∀ i, start.WireValid (left i)) →
      (∀ i, start.WireValid (right i)) →
      EqFinBodyResult start left right seed
  | 0, left, right, hseed, _, _ =>
      { builder := start
        wire := seed
        extension := Extends.refl start
        valid := hseed
        gate_delta := by simp
        eval := by
          intro inputs
          simp }
  | n + 1, left, right, hseed, hleft, hright => by
      let previous := eqFinBody start seed n (fun i => left i.castSucc)
        (fun i => right i.castSucc) hseed (fun i => hleft i.castSucc)
        (fun i => hright i.castSucc)
      have hleftLast := previous.extension.wireValid (hleft (Fin.last n))
      have hrightLast := previous.extension.wireValid (hright (Fin.last n))
      let matched := previous.builder.eq (left (Fin.last n)) (right (Fin.last n))
        hleftLast hrightLast
      let hextMatched := eq_extends previous.builder (left (Fin.last n))
        (right (Fin.last n)) hleftLast hrightLast
      have hprevious := hextMatched.wireValid previous.valid
      have hmatched := eq_wireValid previous.builder (left (Fin.last n))
        (right (Fin.last n)) hleftLast hrightLast
      let aggregate := matched.1.and previous.wire matched.2 hprevious hmatched
      let hextAggregate := and_extends matched.1 previous.wire matched.2
        hprevious hmatched
      let stepExtension := hextMatched.trans hextAggregate
      refine
        { builder := aggregate.1
          wire := aggregate.2
          extension := previous.extension.trans stepExtension
          valid := and_wireValid matched.1 previous.wire matched.2
            hprevious hmatched
          gate_delta := ?_
          eval := ?_ }
      · dsimp only [aggregate, matched]
        rw [and_gate_delta, eq_gate_delta, previous.gate_delta]
        omega
      · intro inputs
        dsimp only [aggregate, matched]
        rw [and_eval]
        rw [hextMatched.evalWire_eq inputs previous.valid]
        rw [eq_eval]
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        rw [previous.eval]
        rw [previous.extension.evalWire_eq inputs (hleft (Fin.last n))]
        rw [previous.extension.evalWire_eq inputs (hright (Fin.last n))]
        rw [Fin.forall_fin_succ']
        simp only [and_assoc]

private theorem eqFinBody_trace_eq (start : CircuitBuilder) (seed : Wire) :
    (n : Nat) → (left right : Fin n → Wire) →
      (hseed : start.WireValid seed) →
      (hleft : ∀ i, start.WireValid (left i)) →
      (hright : ∀ i, start.WireValid (right i)) →
      let built := eqFinBody start seed n left right hseed hleft hright
      let trace := eqFinBodyGateTrace start.gates.length seed n left right
      built.builder.gates = start.gates ++ trace.gates ∧
        built.wire = trace.wire := by
  intro n
  induction n with
  | zero =>
      intro left right hseed hleft hright
      simp [eqFinBody, eqFinBodyGateTrace]
  | succ n ih =>
      intro left right hseed hleft hright
      simp only [eqFinBody]
      have hprevious := ih (fun i => left i.castSucc)
        (fun i => right i.castSucc) hseed
        (fun i => hleft i.castSucc) (fun i => hright i.castSucc)
      rcases hprevious with ⟨hpreviousGates, hpreviousWire⟩
      rw [and_gates, eq_gates_eq, hpreviousGates]
      simp only [eq_wire_eq_trace, and_wire_eq, List.length_append]
      constructor
      · simp [eqFinBodyGateTrace, hpreviousWire, hpreviousGates,
          List.append_assoc]
      · rw [eq_gates_eq, hpreviousGates]
        simp [eqFinBodyGateTrace]
        simp [Nat.add_assoc]

/-- Compare two finite wire families with a streaming true-seeded aggregate.

The empty family still allocates its true seed, yielding the uniform exact
cost {lean}`6 * n + 1`. -/
def eqFin (base : CircuitBuilder) {n : Nat} (left right : Fin n → Wire)
    (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) : EqFinResult base left right := by
  let seed := base.const true
  let hextSeed := const_extends base true
  let body := eqFinBody seed.1 seed.2 n left right (const_wireValid base true)
    (fun i => hextSeed.wireValid (hleft i))
    (fun i => hextSeed.wireValid (hright i))
  refine
    { builder := body.builder
      wire := body.wire
      extension := hextSeed.trans body.extension
      valid := body.valid
      gate_delta := ?_
      eval := ?_ }
  · rw [body.gate_delta, const_gate_delta]
    omega
  · intro inputs
    rw [body.eval]
    rw [const_eval base true inputs]
    simp only [true_and]
    constructor
    · intro hall i
      have hi := hall i
      rwa [hextSeed.evalWire_eq inputs (hleft i),
        hextSeed.evalWire_eq inputs (hright i)] at hi
    · intro hall i
      rw [hextSeed.evalWire_eq inputs (hleft i),
        hextSeed.evalWire_eq inputs (hright i)]
      exact hall i

/-- Finite-family equality preserves the complete input prefix. -/
theorem eqFin_extends (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) :
    base.Extends (eqFin base left right hleft hright).builder :=
  (eqFin base left right hleft hright).extension

/-- The finite-family equality output is valid in its result builder. -/
theorem eqFin_wireValid (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) :
    (eqFin base left right hleft hright).builder.WireValid
      (eqFin base left right hleft hright).wire :=
  (eqFin base left right hleft hright).valid

/-- Finite-family equality emits exactly one true seed and six gates per
coordinate. -/
theorem eqFin_gate_delta (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) :
    (eqFin base left right hleft hright).builder.gates.length =
      base.gates.length + (6 * n + 1) :=
  (eqFin base left right hleft hright).gate_delta

/-- The finite-family equality output is true exactly when both evaluated
families agree pointwise. -/
theorem eqFin_eval_iff (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) (inputs : Nat → Bool) :
    (eqFin base left right hleft hright).builder.evalWire inputs
        (eqFin base left right hleft hright).wire = true ↔
      ∀ i, base.evalWire inputs (left i) = base.evalWire inputs (right i) :=
  (eqFin base left right hleft hright).eval inputs

/-- The streaming family equality appends exactly its public interleaved gate
trace, including both the true seed and every aggregate AND. -/
theorem eqFin_gates_eq (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) :
    (eqFin base left right hleft hright).builder.gates =
      base.gates ++ (eqFinGateTrace base.gates.length left right).gates := by
  unfold eqFin eqFinGateTrace
  dsimp only
  have hbody := eqFinBody_trace_eq (base.const true).1
    (base.const true).2 n left right (const_wireValid base true)
    (fun i => (const_extends base true).wireValid (hleft i))
    (fun i => (const_extends base true).wireValid (hright i))
  rw [hbody.1, const_gates]
  simp [const_wire_eq, List.append_assoc]

/-- The streaming family equality's output wire is the one named by its
public trace. -/
theorem eqFin_wire_eq_trace (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire) (hleft : ∀ i, base.WireValid (left i))
    (hright : ∀ i, base.WireValid (right i)) :
    (eqFin base left right hleft hright).wire =
      (eqFinGateTrace base.gates.length left right).wire := by
  unfold eqFin eqFinGateTrace
  dsimp only
  simpa [const_wire_eq] using
    (eqFinBody_trace_eq (base.const true).1
      (base.const true).2 n left right (const_wireValid base true)
      (fun i => (const_extends base true).wireValid (hleft i))
      (fun i => (const_extends base true).wireValid (hright i))).2

/-- The finite-family equality result is independent of validity-proof
choices. -/
theorem eqFin_proof_irrel (base : CircuitBuilder) {n : Nat}
    (left right : Fin n → Wire)
    (hleft₁ hleft₂ : ∀ i, base.WireValid (left i))
    (hright₁ hright₂ : ∀ i, base.WireValid (right i)) :
    eqFin base left right hleft₁ hright₁ =
      eqFin base left right hleft₂ hright₂ := by
  rfl

end CircuitBuilder

end CLRS.Chapter34.Turing.CookLevin
