import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.Validity
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.TransitionCircuits.Core

/-!
# CLRS Section 34.4 - Finished row and transition circuits

These wrappers expose actual {lit}`Circuit` values at the two principal internal
predicate wires.  They preserve the builder semantics and carry public
well-formedness theorems, so later tableau assembly need not reopen the
proof-carrying builder records.
-/

namespace CLRS.Chapter34.Turing.CookLevin

noncomputable section

/-! ## Canonical row validity -/

/-- Close the canonical row-validity builder at its predicate wire. -/
def validCfgCircuitFinished
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) : Circuit :=
  let result := validCfgCircuit base wires hvalid
  result.builder.finish result.wire result.valid

/-- A finished canonical row-validity circuit is well formed. -/
theorem validCfgCircuit_finish_wellFormed
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) :
    (validCfgCircuitFinished base wires hvalid).WellFormed := by
  unfold validCfgCircuitFinished
  exact CircuitBuilder.finish_wellFormed _ _ _

/-- Finishing preserves the canonical row-validity wire's evaluation. -/
theorem validCfgCircuit_finish_eval
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid : wires.ValidIn base) (inputs : Nat → Bool) :
    (validCfgCircuitFinished base wires hvalid).eval inputs =
      (validCfgCircuit base wires hvalid).builder.evalWire inputs
        (validCfgCircuit base wires hvalid).wire := by
  unfold validCfgCircuitFinished
  exact CircuitBuilder.finish_eval _ _ _ inputs

/-- The finished validity circuit is independent of the validity proof term. -/
theorem validCfgCircuitFinished_proof_irrel
    {tm : _root_.Turing.FinTM2} {H : Nat}
    (base : CircuitBuilder) (wires : CfgWires tm H)
    (hvalid₁ hvalid₂ : wires.ValidIn base) :
    validCfgCircuitFinished base wires hvalid₁ =
      validCfgCircuitFinished base wires hvalid₂ := by
  rfl

/-! ## Local transition -/

/-- Close the local transition builder at its predicate wire. -/
def transitionCircuitFinished
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) : Circuit :=
  let result := transitionCircuit tm H base current next hcurrent hnext
  result.builder.finish result.wire result.valid

/-- A finished local transition circuit is well formed. -/
theorem transitionCircuit_finish_wellFormed
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base) :
    (transitionCircuitFinished tm H base current next hcurrent hnext).WellFormed := by
  unfold transitionCircuitFinished
  exact CircuitBuilder.finish_wellFormed _ _ _

/-- Finishing preserves the local transition predicate wire's evaluation. -/
theorem transitionCircuit_finish_eval
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent : current.ValidIn base) (hnext : next.ValidIn base)
    (inputs : Nat → Bool) :
    (transitionCircuitFinished tm H base current next hcurrent hnext).eval inputs =
      (transitionCircuit tm H base current next hcurrent hnext).builder.evalWire inputs
        (transitionCircuit tm H base current next hcurrent hnext).wire := by
  unfold transitionCircuitFinished
  exact CircuitBuilder.finish_eval _ _ _ inputs

/-- The finished transition circuit is independent of both validity proofs. -/
theorem transitionCircuitFinished_proof_irrel
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (base : CircuitBuilder) (current next : CfgWires tm H)
    (hcurrent₁ hcurrent₂ : current.ValidIn base)
    (hnext₁ hnext₂ : next.ValidIn base) :
    transitionCircuitFinished tm H base current next hcurrent₁ hnext₁ =
      transitionCircuitFinished tm H base current next hcurrent₂ hnext₂ := by
  rfl

end

end CLRS.Chapter34.Turing.CookLevin
