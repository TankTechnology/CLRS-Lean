import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityBoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityIndices

/-!
# Arithmetic stack-cell equality in the validity generator

This module fixes one machine stack and one bounded cell, closes every wire
index used by its canonicality constraint, and instantiates the contextual
five-gate Boolean-equality serializer at those indices.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open StateTransition

noncomputable section

/-- Ordinal of a fixed machine stack in the canonical finite stack order. -/
noncomputable def arithmeticStackOrdinal
    (tm : _root_.Turing.FinTM2) (k : tm.K) : Nat := by
  letI : Fintype tm.K := tm.kFin
  exact (Fintype.equivFin tm.K k).val

/-- First fresh gate index of the complete stack-validity family. -/
noncomputable def arithmeticStackValidityStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) : Nat :=
  arithmeticHaltedMatchStart tm H start + 5

/-- First fresh gate index of one fixed stack's active-mask block. -/
noncomputable def arithmeticStackBlockStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K) : Nat :=
  arithmeticStackValidityStart tm H start +
    (H + 1 + 6 * H) * arithmeticStackOrdinal tm k

/-- Closed output wire of the suffix-OR active mask at one cell. -/
noncomputable def arithmeticStackMaskOutputWire
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K)
    (i : Fin H) : Nat :=
  arithmeticStackBlockStart tm H start k + H - i.val

/-- First fresh gate of the per-cell family following one stack's mask. -/
noncomputable def arithmeticStackCellTraceStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K) : Nat :=
  arithmeticStackBlockStart tm H start k + (H + 1)

/-- Output wire of the cell's leading negation of the blank bit. -/
noncomputable def arithmeticStackCellNotWire
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K)
    (i : Fin H) : Nat :=
  arithmeticStackCellTraceStart tm H start k + 6 * i.val

/-- First fresh gate of the cell's five-gate active/nonblank equality. -/
noncomputable def arithmeticStackCellBoolEqStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K)
    (i : Fin H) : Nat :=
  arithmeticStackCellNotWire tm H start k i + 1

/-- Closed row wire of the distinguished blank symbol in one stack cell. -/
def arithmeticStackBlankWire
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K)
    (i : Fin H) : Nat :=
  rowBase + (1 + (labelCount tm + 1) + stateCount tm +
    cfgStackBitOffset tm H k + (H + 1) +
      ((reachableAlphabet tm k).card +
        ((reachableAlphabet tm k).card + 1) * i.val))

/-- Ordered stack-height sources of one semantic suffix-OR mask. -/
def arithmeticStackMaskWires
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K) :
    List CircuitBuilder.Wire :=
  List.ofFn fun i : Fin H =>
    (arithmeticCfgWires tm H rowBase).stackHeight k i.succ

/-- Semantic suffix-OR trace whose outputs are the active masks of a fixed
stack. -/
def arithmeticStackMaskTrace
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    SuffixOrGateTrace (arithmeticStackMaskWires tm H rowBase k).length :=
  suffixOrGateTrace (arithmeticStackBlockStart tm H start k)
    (arithmeticStackMaskWires tm H rowBase k)

/-- The closed active-mask wire is exactly the semantic suffix-OR output. -/
theorem arithmeticStackMaskOutputWire_eq_trace
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    arithmeticStackMaskOutputWire tm H start k i =
      (arithmeticStackMaskTrace tm H start rowBase k).outputs
        (Fin.cast (by simp [arithmeticStackMaskWires]) i) := by
  unfold arithmeticStackMaskOutputWire arithmeticStackMaskTrace
  rw [suffixOrGateTrace_output_eq]
  simp [arithmeticStackMaskWires]

/-- The closed blank wire is exactly the last alphabet coordinate in the
arithmetic row bundle. -/
theorem arithmeticStackBlankWire_eq_row
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    arithmeticStackBlankWire tm H rowBase k i =
      (arithmeticCfgWires tm H rowBase).stackCell k i
        (Fin.last (reachableAlphabet tm k).card) := by
  rw [arithmeticCfgWires_stackCell]
  simp [arithmeticStackBlankWire]

/-- Encoded five-gate equality stream for one fixed stack cell.  Its left
operand is the semantic active-mask output, and its right operand is the
fresh result of the immediately preceding blank-bit negation. -/
noncomputable def arithmeticStackCellBoolEqGateStream
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K)
    (i : Fin H) : List CircuitSym :=
  affineBoolEqGateStream (arithmeticStackCellBoolEqStart tm H start k i)
    (arithmeticStackMaskOutputWire tm H start k i)
    (arithmeticStackCellNotWire tm H start k i)

/-- The closed stream is the exact Boolean-equality subtrace used by the
semantic stack-validity construction. -/
theorem arithmeticStackCellBoolEqGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    arithmeticStackCellBoolEqGateStream tm H start k i =
      (CircuitBuilder.boolEqGateTrace
        (arithmeticStackCellBoolEqStart tm H start k i)
        ((arithmeticStackMaskTrace tm H start rowBase k).outputs
          (Fin.cast (by simp [arithmeticStackMaskWires]) i))
        (arithmeticStackCellNotWire tm H start k i)).gates.flatMap
          encodeCircuitGate := by
  unfold arithmeticStackCellBoolEqGateStream affineBoolEqGateStream
  rw [arithmeticStackMaskOutputWire_eq_trace]

/-- Concrete contextual run for one arithmetic stack-cell equality. -/
def arithmeticStackCellBoolEqRev_runFrom
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K)
    (i : Fin H) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineBoolEqBodyCfg (arithmeticStackCellBoolEqStart tm H start k i)
        (arithmeticStackMaskOutputWire tm H start k i)
        (arithmeticStackCellNotWire tm H start k i) output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((arithmeticStackCellBoolEqGateStream tm H start k i).reverse ++
          output)))
      (affineBoolEqRevSteps (arithmeticStackCellBoolEqStart tm H start k i)
        (arithmeticStackMaskOutputWire tm H start k i)
        (arithmeticStackCellNotWire tm H start k i)) :=
  affineBoolEqRev_runFrom _ _ _ output

/-- Every fixed stack-cell invocation inherits the contextual quadratic
running-time envelope. -/
theorem arithmeticStackCellBoolEqRev_steps_le
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K)
    (i : Fin H) :
    affineBoolEqRevSteps (arithmeticStackCellBoolEqStart tm H start k i)
        (arithmeticStackMaskOutputWire tm H start k i)
        (arithmeticStackCellNotWire tm H start k i) ≤
      100 * (arithmeticStackCellBoolEqStart tm H start k i +
        arithmeticStackMaskOutputWire tm H start k i +
        arithmeticStackCellNotWire tm H start k i + 1) ^ 2 :=
  affineBoolEqRev_steps_le _ _ _

end

end CLRS.Chapter34.Turing.CookLevin
