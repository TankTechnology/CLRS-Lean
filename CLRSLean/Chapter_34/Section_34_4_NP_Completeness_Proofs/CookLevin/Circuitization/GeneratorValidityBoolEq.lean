import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityOneHot
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.BoolEq

/-!
# Halted/none-label equality in the validity generator

This module advances the concrete row-validity boundary through the first
post-one-hot primitive.  All indices are closed arithmetic functions of the
fixed machine, runtime height, row base, and current gate index.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open StateTransition

noncomputable section

/-- Closed gate count of all raw one-hot groups in one row. -/
noncomputable def arithmeticRawOneHotGateCount
    (tm : _root_.Turing.FinTM2) (H : Nat) : Nat := by
  letI : Fintype tm.K := tm.kFin
  exact (3 * (labelCount tm + 1) + 4) + (3 * stateCount tm + 4) +
    ∑ k : tm.K, ((3 * (H + 1) + 4) +
      H * (3 * ((reachableAlphabet tm k).card + 1) + 4))

/-- The closed arithmetic count is the semantic raw trace length. -/
@[simp] theorem rawOneHotGateTrace_length_eq_arithmetic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    (rawOneHotGateTrace start
      (arithmeticCfgWires tm H rowBase)).gates.length =
        arithmeticRawOneHotGateCount tm H := by
  letI : Fintype tm.K := tm.kFin
  simp [arithmeticRawOneHotGateCount]

/-- First fresh gate index of halted/none-label Boolean equality. -/
noncomputable def arithmeticHaltedMatchStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) : Nat :=
  start + arithmeticRawOneHotGateCount tm H

/-- Closed arithmetic wire of the distinguished none-label bit. -/
def arithmeticNoneLabelWire
    (tm : _root_.Turing.FinTM2) (rowBase : Nat) : Nat :=
  rowBase + labelCount tm + 1

/-- Explicit encoded stream of halted/none-label Boolean equality. -/
noncomputable def arithmeticHaltedMatchGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List CircuitSym :=
  affineBoolEqGateStream (arithmeticHaltedMatchStart tm H start)
    rowBase (arithmeticNoneLabelWire tm rowBase)

/-- The closed arithmetic stream is exactly the equality trace used by
canonical row validity. -/
theorem arithmeticHaltedMatchGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticHaltedMatchGateStream tm H start rowBase =
      let wires := arithmeticCfgWires tm H rowBase
      let raw := rawOneHotGateTrace start wires
      (CircuitBuilder.boolEqGateTrace (start + raw.gates.length)
        wires.halted (wires.label (Fin.last (labelCount tm)))).gates.flatMap
          encodeCircuitGate := by
  simp only [arithmeticHaltedMatchGateStream, affineBoolEqGateStream]
  rw [arithmeticCfgWires_halted, arithmeticCfgWires_label,
    rawOneHotGateTrace_length_eq_arithmetic]
  simp [arithmeticHaltedMatchStart, arithmeticNoneLabelWire]
  rw [show rowBase + labelCount tm + 1 =
    rowBase + (1 + labelCount tm) by omega]

/-- Exact encoded suffix after both raw one-hot groups and halted agreement. -/
noncomputable def arithmeticValidityPostHaltedMatchGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List CircuitSym :=
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  let full := canonicalValidityGateTrace start wires
  (full.gates.drop (raw.gates.length + 5)).flatMap encodeCircuitGate

/-- Advance the exact row-validity boundary through halted/none-label
agreement. -/
theorem arithmeticValidityPostOneHot_eq_haltedMatch_append_post
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticValidityPostOneHotGateStream tm H start rowBase =
      arithmeticHaltedMatchGateStream tm H start rowBase ++
        arithmeticValidityPostHaltedMatchGateStream tm H start rowBase := by
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  let halted := CircuitBuilder.boolEqGateTrace
    (start + raw.gates.length) wires.halted
    (wires.label (Fin.last (labelCount tm)))
  let full := canonicalValidityGateTrace start wires
  have hprefix : raw.gates ++ halted.gates <+: full.gates := by
    unfold full halted raw wires canonicalValidityGateTrace
    simp
  rcases hprefix with ⟨tail, htail⟩
  have hhalted := arithmeticHaltedMatchGateStream_eq_semantic
    tm H start rowBase
  unfold arithmeticValidityPostOneHotGateStream
  unfold arithmeticValidityPostHaltedMatchGateStream
  change (full.gates.drop raw.gates.length).flatMap encodeCircuitGate =
    arithmeticHaltedMatchGateStream tm H start rowBase ++
      (full.gates.drop (raw.gates.length + 5)).flatMap encodeCircuitGate
  change arithmeticHaltedMatchGateStream tm H start rowBase =
    halted.gates.flatMap encodeCircuitGate at hhalted
  rw [hhalted, ← htail]
  rw [show 5 = halted.gates.length by simp [halted]]
  simp [List.flatMap_append]

/-- Concrete contextual run for the actual halted/none-label equality of an
arithmetic row. -/
def arithmeticHaltedMatchRev_runFrom
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineBoolEqBodyCfg (arithmeticHaltedMatchStart tm H start)
        rowBase (arithmeticNoneLabelWire tm rowBase) output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((arithmeticHaltedMatchGateStream tm H start rowBase).reverse ++
          output)))
      (affineBoolEqRevSteps (arithmeticHaltedMatchStart tm H start)
        rowBase (arithmeticNoneLabelWire tm rowBase)) :=
  affineBoolEqRev_runFrom _ _ _ output

/-- The concrete halted-match invocation inherits the contextual polynomial
bound. -/
theorem arithmeticHaltedMatchRev_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineBoolEqRevSteps (arithmeticHaltedMatchStart tm H start)
        rowBase (arithmeticNoneLabelWire tm rowBase) ≤
      100 * (arithmeticHaltedMatchStart tm H start + rowBase +
        arithmeticNoneLabelWire tm rowBase + 1) ^ 2 :=
  affineBoolEqRev_steps_le _ _ _

end

end CLRS.Chapter34.Turing.CookLevin
