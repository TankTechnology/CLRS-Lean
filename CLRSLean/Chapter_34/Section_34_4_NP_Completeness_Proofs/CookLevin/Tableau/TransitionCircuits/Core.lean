import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Dispatch.Core

/-!
# CLRS Section 34.4 - Local transition-circuit core

The local Cook--Levin transition circuit widens the current public row to a
bounded workspace, dispatches every finite program label, narrows back to the
public height with an explicit fit bit, compares the complete narrowed row to
the public next row, and finally conjoins fit with equality.

Main results:

- Structure {lit}`TransitionCircuitResult`: proof-carrying final builder and
  transition wire.
- Definition {lit}`transitionCircuit`: the complete local circuit pipeline.
- Definition {lit}`transitionCircuitGateCost`: exact primitive gate total.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Exact local-circuit cost -/

/-- Exact gate cost of one local transition circuit.

The summands are respectively: two widening constants, finite label dispatch,
overflow fit, complete public-row equality, and the final conjunction. -/
def transitionCircuitGateCost (tm : _root_.Turing.FinTM2) (H : Nat) : Nat :=
  2 + dispatchGateCost tm H +
    (Fintype.card tm.K * maxPushesPerStep tm + 2) +
    (6 * cfgBitCount tm H + 1) + 1

/-! ## Proof-carrying construction -/

/-- Proof-carrying result of building one local transition constraint. -/
structure TransitionCircuitResult (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H) where
  /-- Builder after all internal transition gates. -/
  builder : CircuitBuilder
  /-- Final output wire asserting fit and complete-row equality. -/
  wire : CircuitBuilder.Wire
  /-- The result builder preserves the complete public input prefix. -/
  extension : base.Extends builder
  /-- The final transition output belongs to the result builder. -/
  valid : builder.WireValid wire
  /-- The builder emits exactly the advertised primitive gate total. -/
  gate_delta : builder.gates.length =
    base.gates.length + transitionCircuitGateCost tm H

/-- Build the local transition circuit from two already allocated public rows.

Only {lit}`current` and {lit}`next` are public inputs.  Every workspace, statement,
selector, fit, equality, and conjunction wire is constructed internally by the
returned builder; the pipeline introduces no additional external inputs. -/
def transitionCircuit (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    TransitionCircuitResult tm H base current next := by
  let widened := widenCfg base current hcurrent
  let dispatched := dispatchLabels tm H widened.builder widened.constants
    widened.wires widened.valid
  let narrowed := narrowCfg dispatched.builder dispatched.wires dispatched.valid
  let prefixExtension := widened.extension.trans
    (dispatched.extension.trans narrowed.extension)
  have hnextNarrowed : next.ValidIn narrowed.builder :=
    hnext.mono prefixExtension
  let equal := cfgEq narrowed.builder narrowed.wires next narrowed.valid
    hnextNarrowed
  have hfitEqual : equal.builder.WireValid narrowed.fit :=
    equal.extension.wireValid narrowed.fitValid
  let final := equal.builder.and narrowed.fit equal.wire hfitEqual equal.valid
  let finalExtension := prefixExtension.trans
    (equal.extension.trans
      (CircuitBuilder.and_extends equal.builder narrowed.fit equal.wire
        hfitEqual equal.valid))
  refine
    { builder := final.1
      wire := final.2
      extension := finalExtension
      valid := CircuitBuilder.and_wireValid equal.builder narrowed.fit
        equal.wire hfitEqual equal.valid
      gate_delta := ?_ }
  rw [CircuitBuilder.and_gate_delta, equal.gate_delta, narrowed.gate_delta,
    dispatched.gate_delta, widened.gate_delta]
  simp only [transitionCircuitGateCost, dispatchGateCost]
  omega

/-! ## Public structural wrappers -/

/-- The local transition builder preserves the public input prefix. -/
theorem transitionCircuit_extends (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    base.Extends
      (transitionCircuit tm H base current next hcurrent hnext).builder :=
  (transitionCircuit tm H base current next hcurrent hnext).extension

/-- The local transition output belongs to its final builder. -/
theorem transitionCircuit_wireValid (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuit tm H base current next hcurrent hnext).builder.WireValid
      (transitionCircuit tm H base current next hcurrent hnext).wire :=
  (transitionCircuit tm H base current next hcurrent hnext).valid

/-- The local transition circuit has the exact primitive gate delta. -/
theorem transitionCircuit_gate_delta (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuit tm H base current next hcurrent hnext).builder.gates.length =
      base.gates.length + transitionCircuitGateCost tm H :=
  (transitionCircuit tm H base current next hcurrent hnext).gate_delta

/-- Local transition construction is independent of public validity proofs. -/
theorem transitionCircuit_proof_irrel (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent₁ hcurrent₂ : current.ValidIn base)
    (hnext₁ hnext₂ : next.ValidIn base) :
    transitionCircuit tm H base current next hcurrent₁ hnext₁ =
      transitionCircuit tm H base current next hcurrent₂ hnext₂ := by
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
