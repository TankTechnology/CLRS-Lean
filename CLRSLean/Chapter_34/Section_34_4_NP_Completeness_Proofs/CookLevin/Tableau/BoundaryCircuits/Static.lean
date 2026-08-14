import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ControlCircuits
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder.ConstantPool

/-!
# CLRS Section 34.4 - Pool-backed static tableau rows

Boundary constraints compare a public tableau row with a fixed canonical row.
This file realizes every Boolean coordinate through one shared true/false wire
pool, so the fixed row itself emits no gates and leaves no SAT-free wires.

Main results:

- Definition {lit}`staticCfgWires`: a zero-gate complete-row encoding.
- Theorem {lit}`staticCfgWires_eval`: exact evaluation to the supplied bits.
- Theorems {lit}`staticCfgWires_mono` and
  {lit}`staticCfgWires_proof_irrel`: stable pool transport.
- Definition {lit}`staticBoundedCfgWires`: canonical raw bounded-row encoding.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Complete Boolean rows from one shared pool -/

/-- Map a complete Boolean row to one shared true/false wire pool.

No gate is allocated: every true coordinate aliases the pool's true wire and
every false coordinate aliases its false wire. -/
def staticCfgWires {tm : _root_.Turing.FinTM2} {H : Nat}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (bits : CfgBits tm H) : CfgWires tm H :=
  fun slot => if bits slot then pool.trueWire else pool.falseWire

/-- A pool-backed static complete row is valid without allocating gates. -/
theorem staticCfgWires_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (bits : CfgBits tm H) : (staticCfgWires pool bits).ValidIn builder := by
  intro slot
  cases hbit : bits slot <;>
    simp [staticCfgWires, hbit, pool.falseValid, pool.trueValid]

/-- Static complete-row wires evaluate exactly to their supplied Boolean row. -/
theorem staticCfgWires_eval {tm : _root_.Turing.FinTM2} {H : Nat}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (bits : CfgBits tm H) :
    evalCfgBits builder inputs (staticCfgWires pool bits) = bits := by
  funext slot
  cases hbit : bits slot <;>
    simp [evalCfgBits, staticCfgWires, hbit, pool.false_eval, pool.true_eval]

/-- Transporting the shared pool leaves every static row wire unchanged. -/
theorem staticCfgWires_mono {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext : base.Extends next) (bits : CfgBits tm H) :
    staticCfgWires (pool.mono hext) bits = staticCfgWires pool bits := by
  rfl

/-- Static complete-row encoding is independent of the extension proof used
to transport the pool. -/
theorem staticCfgWires_proof_irrel {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext₁ hext₂ : base.Extends next) (bits : CfgBits tm H) :
    staticCfgWires (pool.mono hext₁) bits =
      staticCfgWires (pool.mono hext₂) bits := by
  rfl

/-! ## Canonical bounded rows -/

/-- Pool-backed one-hot encoding of one complete raw bounded configuration. -/
def staticBoundedCfgWires {tm : _root_.Turing.FinTM2} {H : Nat}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (code : BoundedCfg tm H) : CfgWires tm H :=
  staticCfgWires pool (encodeRawCfgBits code)

/-- A static bounded row is valid in the builder that owns its shared pool. -/
theorem staticBoundedCfgWires_valid {tm : _root_.Turing.FinTM2} {H : Nat}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (code : BoundedCfg tm H) :
    (staticBoundedCfgWires pool code).ValidIn builder :=
  staticCfgWires_valid pool _

/-- A static bounded row evaluates to its exact canonical one-hot encoding. -/
theorem staticBoundedCfgWires_eval {tm : _root_.Turing.FinTM2} {H : Nat}
    {builder : CircuitBuilder} (pool : builder.BoolWirePool)
    (inputs : Nat → Bool) (code : BoundedCfg tm H) :
    evalCfgBits builder inputs (staticBoundedCfgWires pool code) =
      encodeRawCfgBits code :=
  staticCfgWires_eval pool inputs _

/-- Pool transport leaves a static bounded row unchanged. -/
theorem staticBoundedCfgWires_mono {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext : base.Extends next) (code : BoundedCfg tm H) :
    staticBoundedCfgWires (pool.mono hext) code =
      staticBoundedCfgWires pool code := by
  rfl

/-- Static bounded-row encoding is independent of proof-valued pool transport. -/
theorem staticBoundedCfgWires_proof_irrel
    {tm : _root_.Turing.FinTM2} {H : Nat}
    {base next : CircuitBuilder} (pool : base.BoolWirePool)
    (hext₁ hext₂ : base.Extends next) (code : BoundedCfg tm H) :
    staticBoundedCfgWires (pool.mono hext₁) code =
      staticBoundedCfgWires (pool.mono hext₂) code := by
  rfl

/-! ## Shared boundary-result shell -/

/-- Proof-carrying Boolean boundary constraint.  Concrete constructors expose
their exact gate delta as a theorem rather than indexing this reusable shell
by a proof-sensitive arithmetic expression. -/
structure BoundaryCircuitResult (base : CircuitBuilder) where
  /-- Builder after the boundary constraint. -/
  builder : CircuitBuilder
  /-- Final Boolean boundary output. -/
  wire : CircuitBuilder.Wire
  /-- The complete input builder is preserved. -/
  extension : base.Extends builder
  /-- The final output belongs to the result builder. -/
  valid : builder.WireValid wire
  /-- Exact number of emitted gates, recorded by this construction. -/
  gateCost : Nat
  /-- The result builder realizes the recorded gate cost exactly. -/
  gate_delta : builder.gates.length = base.gates.length + gateCost

/-- Return the shared false wire as a zero-gate rejecting constraint. -/
def falseBoundaryCircuit (base : CircuitBuilder)
    (pool : base.BoolWirePool) : BoundaryCircuitResult base where
  builder := base
  wire := pool.falseWire
  extension := CircuitBuilder.Extends.refl base
  valid := pool.falseValid
  gateCost := 0
  gate_delta := by omega

/-- The zero-gate rejecting boundary output always evaluates to false. -/
theorem falseBoundaryCircuit_eval (base : CircuitBuilder)
    (pool : base.BoolWirePool) (inputs : Nat → Bool) :
    (falseBoundaryCircuit base pool).builder.evalWire inputs
      (falseBoundaryCircuit base pool).wire = false :=
  pool.false_eval inputs

/-- Package complete-row equality as a boundary result. -/
def cfgEqBoundaryCircuit {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base) :
    BoundaryCircuitResult base := by
  let equal := cfgEq base left right hleft hright
  exact
    { builder := equal.builder
      wire := equal.wire
      extension := equal.extension
      valid := equal.valid
      gateCost := 6 * cfgBitCount tm H + 1
      gate_delta := equal.gate_delta }

/-- Packaged boundary equality has exact complete-row semantics. -/
theorem cfgEqBoundaryCircuit_eval_iff
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base)
    (inputs : Nat → Bool) :
    (cfgEqBoundaryCircuit base left right hleft hright).builder.evalWire inputs
        (cfgEqBoundaryCircuit base left right hleft hright).wire = true ↔
      evalCfgBits base inputs left = evalCfgBits base inputs right :=
  cfgEq_eval_iff base left right hleft hright inputs

/-- Complete-row boundary equality agrees exactly with equality of two
successfully decoded machine configurations. -/
theorem cfgEqBoundaryCircuit_eval_iff_decoded
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (left right : CfgWires tm H)
    (hleft : left.ValidIn base) (hright : right.ValidIn base)
    (inputs : Nat → Bool) {c d : tm.Cfg}
    (hleftDecoded : evalBundle base inputs left hleft = some c)
    (hrightDecoded : evalBundle base inputs right hright = some d) :
    (cfgEqBoundaryCircuit base left right hleft hright).builder.evalWire inputs
        (cfgEqBoundaryCircuit base left right hleft hright).wire = true ↔
      c = d := by
  rw [cfgEqBoundaryCircuit_eval_iff]
  constructor
  · intro hbits
    have hsame : evalBundle base inputs left hleft =
        evalBundle base inputs right hright := by
      unfold evalBundle evalRawBundle
      rw [hbits]
    rw [hleftDecoded, hrightDecoded] at hsame
    exact Option.some.inj hsame
  · intro hcfg
    subst d
    rcases evalBundle_eq_some_canonical base inputs left hleft c
        hleftDecoded with ⟨hleftAlphabet, hleftHeight, hleftBits⟩
    rcases evalBundle_eq_some_canonical base inputs right hright c
        hrightDecoded with ⟨hrightAlphabet, hrightHeight, hrightBits⟩
    have halphabet : hleftAlphabet = hrightAlphabet := Subsingleton.elim _ _
    subst hrightAlphabet
    have hheight : hleftHeight = hrightHeight := Subsingleton.elim _ _
    subst hrightHeight
    rw [hleftBits, hrightBits]

end

end CLRS.Chapter34.Turing.CookLevin
