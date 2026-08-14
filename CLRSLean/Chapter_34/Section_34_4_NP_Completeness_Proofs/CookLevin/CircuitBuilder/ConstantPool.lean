import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.CircuitBuilder

/-!
# CLRS Section 34.4 - Shared Boolean wire constants

Cook--Levin row transformations repeatedly need Boolean constants.  This
module allocates one canonical false wire and one canonical true wire, then
packages their validity and exact evaluation laws for reuse by later builder
extensions.

Main results:

- Structure {lit}`CircuitBuilder.BoolWirePool`: two valid constant wires with
  exact false/true evaluation contracts.
- Definition {lit}`CircuitBuilder.BoolWirePool.mono`: reuse a pool under any
  append-only builder extension without allocating gates.
- Definition {lit}`CircuitBuilder.allocateBoolWirePool`: allocate a complete
  pool in exactly two gates, with extension and proof-irrelevance theorems.

Current gaps:

- Deduplicating an already allocated but unbundled pair of constant gates is
  intentionally outside this append-only interface.
- Higher-level row and stack operations decide where one allocated pool is
  threaded and reused.
-/

namespace CLRS.Chapter34.Turing.CookLevin

namespace CircuitBuilder

/-- A reusable false/true wire pair in one circuit-builder prefix. -/
structure BoolWirePool (b : CircuitBuilder) where
  /-- Wire evaluating exactly to false. -/
  falseWire : Wire
  /-- Wire evaluating exactly to true. -/
  trueWire : Wire
  /-- The false wire belongs to the builder. -/
  falseValid : b.WireValid falseWire
  /-- The true wire belongs to the builder. -/
  trueValid : b.WireValid trueWire
  /-- Exact evaluation contract for the false wire. -/
  false_eval : ∀ inputs, b.evalWire inputs falseWire = false
  /-- Exact evaluation contract for the true wire. -/
  true_eval : ∀ inputs, b.evalWire inputs trueWire = true

namespace BoolWirePool

/-- Reuse both constant wires under an append-only builder extension without
allocating any new gates. -/
def mono {base next : CircuitBuilder} (pool : BoolWirePool base)
    (hext : base.Extends next) : BoolWirePool next where
  falseWire := pool.falseWire
  trueWire := pool.trueWire
  falseValid := hext.wireValid pool.falseValid
  trueValid := hext.wireValid pool.trueValid
  false_eval := fun inputs => (hext.evalWire_eq inputs pool.falseValid).trans
    (pool.false_eval inputs)
  true_eval := fun inputs => (hext.evalWire_eq inputs pool.trueValid).trans
    (pool.true_eval inputs)

/-- Monotone pool reuse keeps the original false wire. -/
@[simp] theorem mono_falseWire {base next : CircuitBuilder}
    (pool : BoolWirePool base) (hext : base.Extends next) :
    (pool.mono hext).falseWire = pool.falseWire := rfl

/-- Monotone pool reuse keeps the original true wire. -/
@[simp] theorem mono_trueWire {base next : CircuitBuilder}
    (pool : BoolWirePool base) (hext : base.Extends next) :
    (pool.mono hext).trueWire = pool.trueWire := rfl

/-- Pool reuse is independent of the chosen proof of builder extension. -/
theorem mono_proof_irrel {base next : CircuitBuilder}
    (pool : BoolWirePool base) (hext₁ hext₂ : base.Extends next) :
    pool.mono hext₁ = pool.mono hext₂ := by
  rfl

end BoolWirePool

/-- Proof-carrying result of allocating both Boolean constants. -/
structure BoolWirePoolAllocation (base : CircuitBuilder) where
  /-- Builder after appending false and true constant gates. -/
  builder : CircuitBuilder
  /-- The allocated constant pool in the result builder. -/
  pool : BoolWirePool builder
  /-- The allocation preserves the complete input builder prefix. -/
  extension : base.Extends builder
  /-- Exactly two constant gates are appended. -/
  gate_delta : builder.gates.length = base.gates.length + 2

/-- Allocate one false gate followed by one true gate. -/
def allocateBoolWirePool (base : CircuitBuilder) :
    BoolWirePoolAllocation base := by
  let falseGate := base.const false
  let hextFalse := const_extends base false
  let trueGate := falseGate.1.const true
  let hextTrue := const_extends falseGate.1 true
  let extension := hextFalse.trans hextTrue
  refine
    { builder := trueGate.1
      pool :=
        { falseWire := falseGate.2
          trueWire := trueGate.2
          falseValid := hextTrue.wireValid (const_wireValid base false)
          trueValid := const_wireValid falseGate.1 true
          false_eval := ?_
          true_eval := ?_ }
      extension := extension
      gate_delta := ?_ }
  · intro inputs
    rw [hextTrue.evalWire_eq inputs (const_wireValid base false)]
    exact const_eval base false inputs
  · intro inputs
    exact const_eval falseGate.1 true inputs
  · dsimp only [trueGate, falseGate]
    rw [const_gate_delta, const_gate_delta]

/-- Allocating a Boolean wire pool preserves the complete input prefix. -/
theorem allocateBoolWirePool_extends (base : CircuitBuilder) :
    base.Extends (allocateBoolWirePool base).builder :=
  (allocateBoolWirePool base).extension

/-- The allocated false constant occupies the first fresh wire position. -/
@[simp] theorem allocateBoolWirePool_falseWire (base : CircuitBuilder) :
    (allocateBoolWirePool base).pool.falseWire = base.gates.length := by
  rfl

/-- The allocated true constant immediately follows the false constant. -/
@[simp] theorem allocateBoolWirePool_trueWire (base : CircuitBuilder) :
    (allocateBoolWirePool base).pool.trueWire = base.gates.length + 1 := by
  change (base.const false).1.gates.length = base.gates.length + 1
  exact const_gate_delta base false

/-- The allocated false wire belongs to the result builder. -/
theorem allocateBoolWirePool_false_wireValid (base : CircuitBuilder) :
    (allocateBoolWirePool base).builder.WireValid
      (allocateBoolWirePool base).pool.falseWire :=
  (allocateBoolWirePool base).pool.falseValid

/-- The allocated true wire belongs to the result builder. -/
theorem allocateBoolWirePool_true_wireValid (base : CircuitBuilder) :
    (allocateBoolWirePool base).builder.WireValid
      (allocateBoolWirePool base).pool.trueWire :=
  (allocateBoolWirePool base).pool.trueValid

/-- Allocating a Boolean wire pool appends exactly two gates. -/
theorem allocateBoolWirePool_gate_delta (base : CircuitBuilder) :
    (allocateBoolWirePool base).builder.gates.length =
      base.gates.length + 2 :=
  (allocateBoolWirePool base).gate_delta

/-- The allocated false wire evaluates exactly to false. -/
theorem allocateBoolWirePool_false_eval (base : CircuitBuilder)
    (inputs : Nat → Bool) :
    (allocateBoolWirePool base).builder.evalWire inputs
      (allocateBoolWirePool base).pool.falseWire = false :=
  (allocateBoolWirePool base).pool.false_eval inputs

/-- The allocated true wire evaluates exactly to true. -/
theorem allocateBoolWirePool_true_eval (base : CircuitBuilder)
    (inputs : Nat → Bool) :
    (allocateBoolWirePool base).builder.evalWire inputs
      (allocateBoolWirePool base).pool.trueWire = true :=
  (allocateBoolWirePool base).pool.true_eval inputs

/-- Replacing only the stored builder-validity proof does not change Boolean
pool allocation. -/
theorem allocateBoolWirePool_proof_irrel (base : CircuitBuilder)
    (hvalid : ∀ i (hi : i < base.gates.length),
      (base.gates.get ⟨i, hi⟩).ValidAt base.inputCount i) :
    allocateBoolWirePool { base with valid := hvalid } =
      allocateBoolWirePool base := by
  rfl

end CircuitBuilder

end CLRS.Chapter34.Turing.CookLevin
