import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityBoolEq
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Tableau.ValidityIndices
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.SuffixOr
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Not

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

/-- Number of stacks of the fixed machine, using its bundled finite instance. -/
def arithmeticStackCount (tm : _root_.Turing.FinTM2) : Nat :=
  @Fintype.card tm.K tm.kFin

/-- Canonical fixed-machine stack enumeration used by validity traces. -/
noncomputable def arithmeticStackEquiv (tm : _root_.Turing.FinTM2) :
    tm.K ≃ Fin (arithmeticStackCount tm) :=
  @Fintype.equivFin tm.K tm.kFin

/-- Enumerating a stack and then taking its arithmetic ordinal returns the
original finite index. -/
@[simp] theorem arithmeticStackOrdinal_equiv_symm
    (tm : _root_.Turing.FinTM2) (j : Fin (arithmeticStackCount tm)) :
    arithmeticStackOrdinal tm ((arithmeticStackEquiv tm).symm j) = j.val := by
  change ((@Fintype.equivFin tm.K tm.kFin)
    ((@Fintype.equivFin tm.K tm.kFin).symm j)).val = j.val
  exact congrArg Fin.val
    ((@Fintype.equivFin tm.K tm.kFin).apply_symm_apply j)

/-- First fresh gate index of the complete stack-validity family. -/
noncomputable def arithmeticStackValidityStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) : Nat :=
  arithmeticHaltedMatchStart tm H start + 5

/-- First fresh gate index of one fixed stack's active-mask block. -/
noncomputable def arithmeticStackBlockStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) (k : tm.K) : Nat :=
  arithmeticStackValidityStart tm H start +
    (H + 1 + 6 * H) * arithmeticStackOrdinal tm k

/-- First stack-height source wire scanned by one active-mask suffix OR. -/
def arithmeticStackMaskWireBase
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K) : Nat :=
  rowBase + (1 + (labelCount tm + 1) + stateCount tm +
    cfgStackBitOffset tm H k + 1)

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

/-- The semantic stack-height sources form one literal affine interval. -/
theorem arithmeticStackMaskWires_eq_range'
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K) :
    arithmeticStackMaskWires tm H rowBase k =
      List.range' (arithmeticStackMaskWireBase tm H rowBase k) H := by
  have hwires : ∀ i : Fin H,
      (arithmeticCfgWires tm H rowBase).stackHeight k i.succ =
        arithmeticStackMaskWireBase tm H rowBase k + i.val := by
    intro i
    rw [arithmeticCfgWires_stackHeight]
    simp only [arithmeticStackMaskWireBase, Fin.val_succ]
    ring
  apply List.ext_getElem
  · simp [arithmeticStackMaskWires]
  · intro i hleft hright
    have hi : i < H := by
      simpa [arithmeticStackMaskWires] using hleft
    simpa [arithmeticStackMaskWires] using hwires ⟨i, hi⟩

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

/-- Explicit encoded stream of one arithmetic stack's complete active mask. -/
noncomputable def arithmeticStackMaskGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    List CircuitSym :=
  affineSuffixOrGateStream (arithmeticStackBlockStart tm H start k)
    (arithmeticStackMaskWireBase tm H rowBase k) H

/-- The affine active-mask stream is exactly the semantic suffix-OR trace. -/
theorem arithmeticStackMaskGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    arithmeticStackMaskGateStream tm H start rowBase k =
      (arithmeticStackMaskTrace tm H start rowBase k).gates.flatMap
        encodeCircuitGate := by
  unfold arithmeticStackMaskGateStream arithmeticStackMaskTrace
  rw [affineSuffixOrGateStream_eq_trace,
    ← arithmeticStackMaskWires_eq_range']

/-- Concrete contextual run for one arithmetic stack's active mask. -/
def arithmeticStackMaskRev_runFrom
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineSuffixOrBodyCfg (arithmeticStackBlockStart tm H start k)
        (arithmeticStackMaskWireBase tm H rowBase k) H output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((arithmeticStackMaskGateStream tm H start rowBase k).reverse ++
          output)))
      (affineSuffixOrRevSteps (arithmeticStackBlockStart tm H start k)
        (arithmeticStackMaskWireBase tm H rowBase k) H) :=
  affineSuffixOrRev_runFrom _ _ _ output

/-- The arithmetic active-mask invocation inherits the affine quadratic
running-time bound. -/
theorem arithmeticStackMaskRev_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineSuffixOrRevSteps (arithmeticStackBlockStart tm H start k)
        (arithmeticStackMaskWireBase tm H rowBase k) H ≤
      25 * (arithmeticStackBlockStart tm H start k +
        arithmeticStackMaskWireBase tm H rowBase k + H + 1) ^ 2 :=
  affineSuffixOrRev_steps_le _ _ _

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

/-- Encoded leading negation of the blank bit for one fixed stack cell. -/
def arithmeticStackCellNotGateStream
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K)
    (i : Fin H) : List CircuitSym :=
  affineNotGateStream (arithmeticStackBlankWire tm H rowBase k i)

/-- The closed source index makes the single-NOT stream exactly the semantic
leading gate of this cell-validity block. -/
theorem arithmeticStackCellNotGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    arithmeticStackCellNotGateStream tm H rowBase k i =
      ([CircuitGate.not
        ((arithmeticCfgWires tm H rowBase).stackCell k i
          (Fin.last (reachableAlphabet tm k).card))]).flatMap
        encodeCircuitGate := by
  unfold arithmeticStackCellNotGateStream
  rw [arithmeticStackBlankWire_eq_row,
    affineNotGateStream_eq_trace]

/-- Concrete contextual run for the leading blank-bit negation. -/
def arithmeticStackCellNotRev_runFrom
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K)
    (i : Fin H) (output : List CircuitSym) :
    EvalsToInTime (step sequentialExactlyOneRevProgram)
      (affineNotBodyCfg (arithmeticStackBlankWire tm H rowBase k i) output)
      (some (haltCfg sequentialExactlyOneRevProgram
        ((arithmeticStackCellNotGateStream tm H rowBase k i).reverse ++
          output)))
      (affineNotRevSteps (arithmeticStackBlankWire tm H rowBase k i)) :=
  affineNotRev_runFrom _ output

/-- The arithmetic cell-NOT invocation inherits the generic quadratic bound. -/
theorem arithmeticStackCellNotRev_steps_le
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    affineNotRevSteps (arithmeticStackBlankWire tm H rowBase k i) ≤
      10 * (arithmeticStackBlankWire tm H rowBase k i + 1) ^ 2 :=
  affineNotRev_steps_le _

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

/-- Complete encoded six-gate canonicality block of one arithmetic stack
cell: one blank-bit negation followed by active/nonblank equality. -/
noncomputable def arithmeticStackCellGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (i : Fin H) : List CircuitSym :=
  arithmeticStackCellNotGateStream tm H rowBase k i ++
    arithmeticStackCellBoolEqGateStream tm H start k i

/-- The closed arithmetic stream is exactly the semantic six-gate cell block. -/
theorem arithmeticStackCellGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    arithmeticStackCellGateStream tm H start rowBase k i =
      let mask := arithmeticStackMaskTrace tm H start rowBase k
      let blank := (arithmeticCfgWires tm H rowBase).stackCell k i
        (Fin.last (reachableAlphabet tm k).card)
      ([CircuitGate.not blank] ++
        (CircuitBuilder.boolEqGateTrace
          (arithmeticStackCellBoolEqStart tm H start k i)
          (mask.outputs (Fin.cast
            (by simp [arithmeticStackMaskWires]) i))
          (arithmeticStackCellNotWire tm H start k i)).gates).flatMap
            encodeCircuitGate := by
  unfold arithmeticStackCellGateStream
  rw [arithmeticStackCellNotGateStream_eq_semantic tm H rowBase k i,
    arithmeticStackCellBoolEqGateStream_eq_semantic
      tm H start rowBase k i]
  simp

/-- The arithmetic six-gate stream is one literal `cellValidityGateBlock`. -/
theorem arithmeticStackCellGateStream_eq_block
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (i : Fin H) :
    arithmeticStackCellGateStream tm H start rowBase k i =
      (cellValidityGateBlock
        (arithmeticStackCellTraceStart tm H start k) H
        (fun j => (arithmeticStackMaskTrace tm H start rowBase k).outputs
          (Fin.cast (by simp [arithmeticStackMaskWires]) j))
        (fun j => (arithmeticCfgWires tm H rowBase).stackCell k j
          (Fin.last (reachableAlphabet tm k).card)) i).flatMap
            encodeCircuitGate := by
  rw [arithmeticStackCellGateStream_eq_semantic]
  simp [cellValidityGateBlock, arithmeticStackCellBoolEqStart,
    arithmeticStackCellNotWire]

/-- Encoded ordered family of every six-gate cell block of one stack. -/
noncomputable def arithmeticStackCellFamilyGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    List CircuitSym :=
  (List.ofFn fun i : Fin H =>
    arithmeticStackCellGateStream tm H start rowBase k i).flatten

private theorem flatten_encoded_blocks (blocks : List (List CircuitGate)) :
    (blocks.map fun block => block.flatMap encodeCircuitGate).flatten =
      blocks.flatten.flatMap encodeCircuitGate := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih => simp [ih]

/-- The ordered arithmetic family is exactly the semantic `6H` cell-validity
trace after the active mask. -/
theorem arithmeticStackCellFamilyGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    arithmeticStackCellFamilyGateStream tm H start rowBase k =
      let mask := arithmeticStackMaskTrace tm H start rowBase k
      let active : Fin H → CircuitBuilder.Wire := fun i =>
        mask.outputs (Fin.cast (by simp [arithmeticStackMaskWires]) i)
      let blank : Fin H → CircuitBuilder.Wire := fun i =>
        (arithmeticCfgWires tm H rowBase).stackCell k i
          (Fin.last (reachableAlphabet tm k).card)
      (cellValidityGateTrace
        (arithmeticStackCellTraceStart tm H start k) H active blank).gates.flatMap
          encodeCircuitGate := by
  unfold arithmeticStackCellFamilyGateStream
  simp_rw [arithmeticStackCellGateStream_eq_block]
  rw [cellValidityGateTrace_gates_eq_blocks]
  simpa [Function.comp_def] using flatten_encoded_blocks
    (List.ofFn fun i : Fin H =>
      cellValidityGateBlock (arithmeticStackCellTraceStart tm H start k) H
        (fun j => (arithmeticStackMaskTrace tm H start rowBase k).outputs
          (Fin.cast (by simp [arithmeticStackMaskWires]) j))
        (fun j => (arithmeticCfgWires tm H rowBase).stackCell k j
          (Fin.last (reachableAlphabet tm k).card)) i)

/-- Complete encoded canonicality stream of one fixed stack: its active mask
followed by every ordered six-gate cell block. -/
noncomputable def arithmeticStackGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    List CircuitSym :=
  arithmeticStackMaskGateStream tm H start rowBase k ++
    arithmeticStackCellFamilyGateStream tm H start rowBase k

/-- The arithmetic one-stack stream is exactly the semantic mask-plus-cells
trace of length `H + 1 + 6H`. -/
theorem arithmeticStackGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    arithmeticStackGateStream tm H start rowBase k =
      let mask := arithmeticStackMaskTrace tm H start rowBase k
      let active : Fin H → CircuitBuilder.Wire := fun i =>
        mask.outputs (Fin.cast (by simp [arithmeticStackMaskWires]) i)
      let blank : Fin H → CircuitBuilder.Wire := fun i =>
        (arithmeticCfgWires tm H rowBase).stackCell k i
          (Fin.last (reachableAlphabet tm k).card)
      let cells := cellValidityGateTrace
        (arithmeticStackCellTraceStart tm H start k) H active blank
      (mask.gates ++ cells.gates).flatMap encodeCircuitGate := by
  unfold arithmeticStackGateStream
  rw [arithmeticStackMaskGateStream_eq_semantic,
    arithmeticStackCellFamilyGateStream_eq_semantic]
  simp

/-- A fixed arithmetic stack stream is the corresponding literal block in the
canonical finite stack order. -/
theorem arithmeticStackGateStream_eq_block
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (j : Fin (arithmeticStackCount tm)) :
    arithmeticStackGateStream tm H start rowBase
        ((arithmeticStackEquiv tm).symm j) =
      (stackValidityGateBlock (arithmeticStackValidityStart tm H start)
        (arithmeticCfgWires tm H rowBase)
        (fun q => (arithmeticStackEquiv tm).symm q) j).flatMap
          encodeCircuitGate := by
  rw [arithmeticStackGateStream_eq_semantic]
  unfold stackValidityGateBlock arithmeticStackMaskTrace
    arithmeticStackMaskWires arithmeticStackCellTraceStart
    arithmeticStackBlockStart
  rw [arithmeticStackOrdinal_equiv_symm]

/-- Complete encoded stack-validity family in the fixed machine-stack order. -/
noncomputable def arithmeticStackFamilyGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) : List CircuitSym :=
  (List.ofFn fun j : Fin (arithmeticStackCount tm) =>
    arithmeticStackGateStream tm H start rowBase
      ((arithmeticStackEquiv tm).symm j)).flatten

/-- The arithmetic family stream is exactly the semantic ordered-stack trace. -/
theorem arithmeticStackFamilyGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticStackFamilyGateStream tm H start rowBase =
      (stackValidityFamilyGateTrace
        (arithmeticStackValidityStart tm H start)
        (arithmeticCfgWires tm H rowBase) (arithmeticStackCount tm)
        (fun j => (arithmeticStackEquiv tm).symm j)).gates.flatMap
          encodeCircuitGate := by
  unfold arithmeticStackFamilyGateStream
  simp_rw [arithmeticStackGateStream_eq_block]
  rw [stackValidityFamilyGateTrace_gates_eq_blocks]
  simpa [Function.comp_def] using flatten_encoded_blocks
    (List.ofFn fun j : Fin (arithmeticStackCount tm) =>
      stackValidityGateBlock (arithmeticStackValidityStart tm H start)
        (arithmeticCfgWires tm H rowBase)
        (fun q => (arithmeticStackEquiv tm).symm q) j)

/-- The complete arithmetic stack-family stream is a literal prefix of the
remaining row-validity stream after halted/none-label agreement. -/
theorem arithmeticStackFamilyGateStream_prefix_postHalted
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticStackFamilyGateStream tm H start rowBase <+:
      arithmeticValidityPostHaltedMatchGateStream tm H start rowBase := by
  letI : Fintype tm.K := tm.kFin
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  let halted := CircuitBuilder.boolEqGateTrace
    (start + raw.gates.length) wires.halted
    (wires.label (Fin.last (labelCount tm)))
  let stack := stackValidityFamilyGateTrace
    (start + raw.gates.length + halted.gates.length) wires
    (Fintype.card tm.K) (fun j => (Fintype.equivFin tm.K).symm j)
  let full := canonicalValidityGateTrace start wires
  have hprefix : raw.gates ++ halted.gates ++ stack.gates <+: full.gates := by
    unfold full stack halted raw wires canonicalValidityGateTrace
    simp
  rcases hprefix with ⟨tail, htail⟩
  have hfamily := arithmeticStackFamilyGateStream_eq_semantic
    tm H start rowBase
  have hstackStart : arithmeticStackValidityStart tm H start =
      start + raw.gates.length + halted.gates.length := by
    simp [arithmeticStackValidityStart, arithmeticHaltedMatchStart,
      arithmeticRawOneHotGateCount, raw, halted, wires]
  rw [hstackStart] at hfamily
  change arithmeticStackFamilyGateStream tm H start rowBase =
    stack.gates.flatMap encodeCircuitGate at hfamily
  unfold arithmeticValidityPostHaltedMatchGateStream
  change arithmeticStackFamilyGateStream tm H start rowBase <+:
    (full.gates.drop (raw.gates.length + 5)).flatMap encodeCircuitGate
  rw [hfamily, ← htail]
  rw [show 5 = halted.gates.length by simp [halted]]
  simp [List.flatMap_append]

/-- Ordered output wires consumed by the final conjunction of one arithmetic
row.  This is the exact public constraint order: raw one-hot outputs, halted
agreement, then every stack-cell canonicality output in stack-major order. -/
noncomputable def arithmeticValidityConstraintWires
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List CircuitBuilder.Wire := by
  letI : Fintype tm.K := tm.kFin
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  let halted := CircuitBuilder.boolEqGateTrace
    (start + raw.gates.length) wires.halted
    (wires.label (Fin.last (labelCount tm)))
  let stack := stackValidityFamilyGateTrace
    (start + raw.gates.length + halted.gates.length) wires
    (Fintype.card tm.K) (fun j => (Fintype.equivFin tm.K).symm j)
  let groupEquiv := cfgOneHotGroupEquivFin tm H
  let rawConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun j : Fin (cfgOneHotGroupCount tm H) =>
      raw.outputs (groupEquiv.symm j)
  let stackConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * H) =>
      let q := (finProdFinEquiv
        (m := Fintype.card tm.K) (n := H)).symm p
      stack.outputs q.1 q.2
  exact rawConstraints ++ halted.wire :: stackConstraints

/-- First fresh gate of the final row-validity conjunction, after every
stack mask and cell block. -/
noncomputable def arithmeticValidityFinalStart
    (tm : _root_.Turing.FinTM2) (H start : Nat) : Nat :=
  arithmeticStackValidityStart tm H start +
    arithmeticStackCount tm * (H + 1 + 6 * H)

/-- Exact serialized tail after all stack-validity blocks; semantically this
is the row-validity final conjunction and nothing else. -/
noncomputable def arithmeticValidityFinalConjunctionGateStream
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) : List CircuitSym :=
  (arithmeticValidityPostHaltedMatchGateStream tm H start rowBase).drop
    (arithmeticStackFamilyGateStream tm H start rowBase).length

/-- The formerly opaque post-stack suffix is exactly the encoded tail-first
conjunction over the canonical ordered constraint wires. -/
theorem arithmeticValidityFinalConjunctionGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticValidityFinalConjunctionGateStream tm H start rowBase =
      (CircuitBuilder.conjunctionGateTrace
        (arithmeticValidityFinalStart tm H start)
        (arithmeticValidityConstraintWires tm H start rowBase)).gates.flatMap
          encodeCircuitGate := by
  letI : Fintype tm.K := tm.kFin
  let wires := arithmeticCfgWires tm H rowBase
  let raw := rawOneHotGateTrace start wires
  let halted := CircuitBuilder.boolEqGateTrace
    (start + raw.gates.length) wires.halted
    (wires.label (Fin.last (labelCount tm)))
  let stack := stackValidityFamilyGateTrace
    (start + raw.gates.length + halted.gates.length) wires
    (Fintype.card tm.K) (fun j => (Fintype.equivFin tm.K).symm j)
  let groupEquiv := cfgOneHotGroupEquivFin tm H
  let rawConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun j : Fin (cfgOneHotGroupCount tm H) =>
      raw.outputs (groupEquiv.symm j)
  let stackConstraints : List CircuitBuilder.Wire :=
    List.ofFn fun p : Fin (Fintype.card tm.K * H) =>
      let q := (finProdFinEquiv
        (m := Fintype.card tm.K) (n := H)).symm p
      stack.outputs q.1 q.2
  let constraints := rawConstraints ++ halted.wire :: stackConstraints
  let final := CircuitBuilder.conjunctionGateTrace
    (start + raw.gates.length + halted.gates.length + stack.gates.length)
    constraints
  have hstack := arithmeticStackFamilyGateStream_eq_semantic
    tm H start rowBase
  have hstackStart : arithmeticStackValidityStart tm H start =
      start + raw.gates.length + halted.gates.length := by
    simp [arithmeticStackValidityStart, arithmeticHaltedMatchStart,
      arithmeticRawOneHotGateCount, raw, halted, wires]
  rw [hstackStart] at hstack
  change arithmeticStackFamilyGateStream tm H start rowBase =
    stack.gates.flatMap encodeCircuitGate at hstack
  have hpost : arithmeticValidityPostHaltedMatchGateStream
      tm H start rowBase =
      stack.gates.flatMap encodeCircuitGate ++
        final.gates.flatMap encodeCircuitGate := by
    unfold arithmeticValidityPostHaltedMatchGateStream
    change ((raw.gates ++ halted.gates ++ stack.gates ++ final.gates).drop
      (raw.gates.length + 5)).flatMap encodeCircuitGate = _
    rw [show 5 = halted.gates.length by simp [halted]]
    simp [List.flatMap_append]
  unfold arithmeticValidityFinalConjunctionGateStream
  rw [hpost, hstack]
  simp only [List.drop_left]
  change final.gates.flatMap encodeCircuitGate =
    (CircuitBuilder.conjunctionGateTrace
      (arithmeticValidityFinalStart tm H start)
      (arithmeticValidityConstraintWires tm H start rowBase)).gates.flatMap
        encodeCircuitGate
  congr 2
  · unfold final
    congr 2
    · exact hstackStart.symm
    · simp [stack, arithmeticStackCount]

/-- Advance the exact row-validity boundary through the entire stack family,
leaving only the final conjunction tail. -/
theorem arithmeticValidityPostHaltedMatch_eq_stack_append_final
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticValidityPostHaltedMatchGateStream tm H start rowBase =
      arithmeticStackFamilyGateStream tm H start rowBase ++
        arithmeticValidityFinalConjunctionGateStream tm H start rowBase := by
  rcases arithmeticStackFamilyGateStream_prefix_postHalted
    tm H start rowBase with ⟨tail, htail⟩
  unfold arithmeticValidityFinalConjunctionGateStream
  rw [← htail]
  simp

end

end CLRS.Chapter34.Turing.CookLevin
