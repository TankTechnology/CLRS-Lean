import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowOneHotOperands
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineValidityTailStackFamilySource

/-!
# Canonical tail operands for every Cook--Levin validity row

This module fixes the semantic target of the remaining validity-row source
compiler.  It expands the already compiled `(height, start, rowBase)` seeds
to the exact stack/cell and final-conjunction frames consumed after halted
agreement, then identifies the resulting row-major byte stream with the
canonical validity-row family.

The concrete fixed source machine is deliberately kept in the accompanying
`AffineValidityTailRowFamilySource` layer.  Keeping this equality independent
of the machine proof prevents the source controller from defining its own
weaker notion of the intended output.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open StateTransition

/-- Initial blank-coordinate wire for the runtime cell progression.  This
closed expression remains meaningful when the horizon is zero. -/
def arithmeticStackCellBlankBase
    (tm : _root_.Turing.FinTM2) (H rowBase : Nat) (k : tm.K) : Nat :=
  rowBase + (1 + (labelCount tm + 1) + stateCount tm +
    cfgStackBitOffset tm H k + (H + 1) +
      (reachableAlphabet tm k).card)

/-- The mixed-progression source target is exactly the canonical ordered
cell-frame family for one Cook--Levin stack, including `H = 0`. -/
theorem affineCellProgressionFrames_eq_arithmeticStackCellFrames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineCellProgressionFrames ((reachableAlphabet tm k).card + 1) H
        (arithmeticStackCellTraceStart tm H start k)
        (arithmeticStackBlockStart tm H start k + H)
        (arithmeticStackCellBlankBase tm H rowBase k) =
      arithmeticStackCellFrames tm H start rowBase k := by
  rw [affineCellProgressionFrames_eq_ofFn]
  unfold arithmeticStackCellFrames
  apply List.ofFn_inj.mpr
  funext index
  simp only [AffineCellFrame.mk.injEq]
  constructor
  · simp [arithmeticStackCellNotWire]
  constructor
  · simp [arithmeticStackMaskOutputWire]
  · simp [arithmeticStackCellBlankBase, arithmeticStackBlankWire]
    ring

/-- Exact six runtime operands needed by the continuous source for one
canonical Cook--Levin stack frame. -/
noncomputable def arithmeticRuntimeStackSourceSeed
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    AffineRuntimeStackSourceSeed :=
  { maskStart := arithmeticStackBlockStart tm H start k
    maskBase := arithmeticStackMaskWireBase tm H rowBase k
    count := H
    cellRight := arithmeticStackCellTraceStart tm H start k
    cellLeft := arithmeticStackBlockStart tm H start k + H
    cellBlank := arithmeticStackCellBlankBase tm H rowBase k }

/-- The source seed denotes the exact existing arithmetic stack frame, not a
parallel approximation of its operands. -/
theorem arithmeticRuntimeStackSourceFrame_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineRuntimeStackSourceFrame ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k) =
      arithmeticStackFrame tm H start rowBase k := by
  unfold affineRuntimeStackSourceFrame arithmeticRuntimeStackSourceSeed
    arithmeticStackFrame
  simp only
  congr 1
  exact affineCellProgressionFrames_eq_arithmeticStackCellFrames
    tm H start rowBase k

/-- Contextual exact run for one complete canonical Cook--Levin stack input
frame, through its outer `frameEnd`. -/
noncomputable def arithmeticRuntimeStackSource_runToFinish
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineRuntimeStackSourceRevProgram
        ((reachableAlphabet tm k).card + 1)))
      (affineRuntimeStackSourceLoadedCfg ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k) output)
      (some (affineRuntimeStackSourceFinishCfg
        ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k)
        ((encodeAffineStackFrame
          (arithmeticStackFrame tm H start rowBase k)).reverse ++ output)))
      (affineRuntimeStackSourceSteps ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k)) := by
  simpa [arithmeticRuntimeStackSourceFrame_eq] using
    affineRuntimeStackSource_runToFinish
      ((reachableAlphabet tm k).card + 1)
      (arithmeticRuntimeStackSourceSeed tm H start rowBase k) output

/-- The canonical one-stack contextual run inherits the generic quadratic
payload bound. -/
theorem arithmeticRuntimeStackSource_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineRuntimeStackSourceSteps ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k) ≤
      70 * (((reachableAlphabet tm k).card + 1) + 1) *
        ((encodeUnaryFrame [
            (arithmeticRuntimeStackSourceSeed tm H start rowBase k).count,
            (arithmeticRuntimeStackSourceSeed tm H start rowBase k).maskStart,
            (arithmeticRuntimeStackSourceSeed tm H start rowBase k).maskBase +
              (arithmeticRuntimeStackSourceSeed tm H start rowBase k).count]
          ).length +
          (arithmeticRuntimeStackSourceSeed tm H start rowBase k).count +
          (arithmeticRuntimeStackSourceSeed tm H start rowBase k).cellRight +
          (arithmeticRuntimeStackSourceSeed tm H start rowBase k).cellLeft +
          (arithmeticRuntimeStackSourceSeed tm H start rowBase k).cellBlank +
          1) ^ 2 :=
  affineRuntimeStackSourceSteps_le _ _

/-- Contextual self-contained run for one canonical arithmetic stack: its
three cell-coordinate bases are loaded from the explicit input and all local
counters are empty again at the public exit. -/
noncomputable def arithmeticRuntimeStackStandalone_runToFinish
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineRuntimeStackStandaloneRevProgram
        ((reachableAlphabet tm k).card + 1)))
      (affineRuntimeStackStandaloneLoopCfg
        ((reachableAlphabet tm k).card + 1)
        (encodeAffineRuntimeStackStandaloneInvocation
          (arithmeticRuntimeStackSourceSeed tm H start rowBase k) ++ tail)
        output)
      (some (affineRuntimeStackStandaloneFinishCfg
        ((reachableAlphabet tm k).card + 1) tail
        ((encodeAffineStackFrame
          (arithmeticStackFrame tm H start rowBase k)).reverse ++ output)))
      (affineRuntimeStackStandaloneSteps
        ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k)) := by
  simpa [arithmeticRuntimeStackSourceFrame_eq] using
    affineRuntimeStackStandalone_runToFinish
      ((reachableAlphabet tm k).card + 1)
      (arithmeticRuntimeStackSourceSeed tm H start rowBase k) tail output

/-- The self-contained arithmetic stack run is quadratic in its explicit
unary invocation length. -/
theorem arithmeticRuntimeStackStandalone_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineRuntimeStackStandaloneSteps ((reachableAlphabet tm k).card + 1)
        (arithmeticRuntimeStackSourceSeed tm H start rowBase k) ≤
      100 * (((reachableAlphabet tm k).card + 1) + 1) *
        (encodeAffineRuntimeStackStandaloneInvocation
          (arithmeticRuntimeStackSourceSeed tm H start rowBase k)).length ^ 2 :=
  affineRuntimeStackStandaloneSteps_le_encoding _ _

/-- Canonical fixed stack indices used by both the source controller and the
existing arithmetic stack-frame family. -/
def arithmeticRuntimeStackSourceIndices
    (tm : _root_.Turing.FinTM2) : List (Fin (arithmeticStackCount tm)) :=
  List.finRange (arithmeticStackCount tm)

/-- Fixed blank strides stored in the family controller's finite control. -/
noncomputable def arithmeticRuntimeStackSourceBlankSteps
    (tm : _root_.Turing.FinTM2) : List Nat :=
  (arithmeticRuntimeStackSourceIndices tm).map fun j =>
    (reachableAlphabet tm ((arithmeticStackEquiv tm).symm j)).card + 1

/-- Runtime source seeds for every stack in canonical finite order. -/
noncomputable def arithmeticRuntimeStackSourceSeeds
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List AffineRuntimeStackSourceSeed :=
  (arithmeticRuntimeStackSourceIndices tm).map fun j =>
    arithmeticRuntimeStackSourceSeed tm H start rowBase
      ((arithmeticStackEquiv tm).symm j)

theorem arithmeticRuntimeStackSourceSeeds_length
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    (arithmeticRuntimeStackSourceSeeds tm H start rowBase).length =
      (arithmeticRuntimeStackSourceBlankSteps tm).length := by
  simp [arithmeticRuntimeStackSourceSeeds,
    arithmeticRuntimeStackSourceBlankSteps]

private theorem map_finRange_eq_ofFn {alpha : Type} {n : Nat}
    (f : Fin n → alpha) :
    (List.finRange n).map f = List.ofFn f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.finRange_succ, List.ofFn_succ]
      simp only [List.map_cons, List.map_map]
      congr 1
      exact ih (f ∘ Fin.succ)

/-- Interpreting the paired fixed strides and runtime seeds recovers exactly
the established arithmetic stack-frame list. -/
theorem arithmeticRuntimeStackSourceFamilyFrames_eq
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineRuntimeStackSourceFamilyFrames
        (arithmeticRuntimeStackSourceBlankSteps tm)
        (arithmeticRuntimeStackSourceSeeds tm H start rowBase) =
      arithmeticStackFrames tm H start rowBase := by
  rw [arithmeticRuntimeStackSourceBlankSteps,
    arithmeticRuntimeStackSourceSeeds,
    affineRuntimeStackSourceFamilyFrames_map]
  simp_rw [arithmeticRuntimeStackSourceFrame_eq]
  unfold arithmeticRuntimeStackSourceIndices arithmeticStackFrames
  exact map_finRange_eq_ofFn _

/-- One fixed family controller emits every canonical arithmetic stack frame
and its outer family terminator, while preserving the following invocation. -/
noncomputable def arithmeticRuntimeStackFamilySource_runToFinish
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime
      (step (affineRuntimeStackFamilySourceRevProgram
        (arithmeticRuntimeStackSourceBlankSteps tm)))
      (affineRuntimeStackFamilySourceLoopCfg
        (arithmeticRuntimeStackSourceBlankSteps tm)
        (encodeAffineRuntimeStackStandaloneInvocationFamily
          (arithmeticRuntimeStackSourceSeeds tm H start rowBase) ++ tail)
        output)
      (some (affineRuntimeStackFamilySourceFinishCfg
        (arithmeticRuntimeStackSourceBlankSteps tm) tail
        ((encodeAffineStackFamily
          (arithmeticStackFrames tm H start rowBase) ++
            [UnaryFrameSym.frameEnd]).reverse ++ output)))
      (affineRuntimeStackFamilySourceSteps
        (arithmeticRuntimeStackSourceBlankSteps tm)
        (arithmeticRuntimeStackSourceSeeds tm H start rowBase)) := by
  simpa [arithmeticRuntimeStackSourceFamilyFrames_eq] using
    affineRuntimeStackFamilySource_runToFinish
      (arithmeticRuntimeStackSourceBlankSteps tm)
      (arithmeticRuntimeStackSourceSeeds tm H start rowBase)
      tail output
      (arithmeticRuntimeStackSourceSeeds_length tm H start rowBase)

/-- The complete canonical stack-family source is quadratic in its explicit
runtime seed stream, with a coefficient fixed by the verifier machine. -/
theorem arithmeticRuntimeStackFamilySource_steps_le
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineRuntimeStackFamilySourceSteps
        (arithmeticRuntimeStackSourceBlankSteps tm)
        (arithmeticRuntimeStackSourceSeeds tm H start rowBase) ≤
      affineRuntimeStackFamilySourceStepCoeff
          (arithmeticRuntimeStackSourceBlankSteps tm) *
        ((encodeAffineRuntimeStackStandaloneInvocationFamily
          (arithmeticRuntimeStackSourceSeeds tm H start rowBase)).length +
            1) ^ 2 :=
  affineRuntimeStackFamilySourceSteps_le _ _
    (arithmeticRuntimeStackSourceSeeds_length tm H start rowBase)

/-! ## Closed operands of the final validity conjunction -/

/-- Raw one-hot outputs in their canonical public order, obtained directly
from the already structured runtime frames. -/
noncomputable def arithmeticFinalConjunctionRawWires
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) : List Nat :=
  (arithmeticRawOneHotFrames tm H start rowBase).map
    affineExactlyOneFrameOutputWire

/-- Stack-cell canonicality outputs in stack-major/cell-major order.  The
formula is independent of the source wires and names the last gate of each
six-gate cell block. -/
noncomputable def arithmeticFinalConjunctionStackWires
    (tm : _root_.Turing.FinTM2) (H start : Nat) : List Nat :=
  List.ofFn fun position : Fin (arithmeticStackCount tm * H) =>
    let pair := (finProdFinEquiv
      (m := arithmeticStackCount tm) (n := H)).symm position
    arithmeticStackValidityStart tm H start +
      (H + 1 + 6 * H) * pair.1.val + (H + 1) +
        6 * pair.2.val + 5

/-- Fully arithmetic public wire list of the final conjunction: structured
one-hot frame outputs, halted agreement, then the affine stack-cell family. -/
noncomputable def arithmeticFinalConjunctionWires
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) : List Nat :=
  arithmeticFinalConjunctionRawWires tm H start rowBase ++
    (arithmeticHaltedMatchStart tm H start + 4) ::
      arithmeticFinalConjunctionStackWires tm H start

/-- The closed arithmetic list is exactly the semantic constraint list used
by the established Cook--Levin validity circuit. -/
theorem arithmeticFinalConjunctionWires_eq_semantic
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticFinalConjunctionWires tm H start rowBase =
      arithmeticValidityConstraintWires tm H start rowBase := by
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
  have hraw : arithmeticFinalConjunctionRawWires tm H start rowBase =
      rawConstraints := by
    unfold arithmeticFinalConjunctionRawWires
    rw [arithmeticRawOneHotFrames_eq_groupFrames, List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext index
    exact (arithmeticRawOneHot_output_eq_frame tm H start rowBase
      (groupEquiv.symm index)).symm
  have hrawLength : raw.gates.length =
      arithmeticRawOneHotGateCount tm H := by
    simpa [raw, wires] using
      rawOneHotGateTrace_length_eq_arithmetic tm H start rowBase
  have hhalted : halted.wire =
      arithmeticHaltedMatchStart tm H start + 4 := by
    simp [halted, CircuitBuilder.boolEqGateTrace,
      arithmeticHaltedMatchStart, hrawLength]
  have hstackStart : start + raw.gates.length + halted.gates.length =
      arithmeticStackValidityStart tm H start := by
    simp [halted, arithmeticStackValidityStart,
      arithmeticHaltedMatchStart, hrawLength]
  have hstack : arithmeticFinalConjunctionStackWires tm H start =
      stackConstraints := by
    unfold arithmeticFinalConjunctionStackWires
    apply List.ofFn_inj.mpr
    funext position
    let pair := (finProdFinEquiv
      (m := Fintype.card tm.K) (n := H)).symm position
    change arithmeticStackValidityStart tm H start +
        (H + 1 + 6 * H) * pair.1.val + (H + 1) +
          6 * pair.2.val + 5 =
      stack.outputs pair.1 pair.2
    rw [stackValidityFamilyGateTrace_output_eq]
    rw [hstackStart]
  unfold arithmeticFinalConjunctionWires
    arithmeticValidityConstraintWires
  change arithmeticFinalConjunctionRawWires tm H start rowBase ++
      (arithmeticHaltedMatchStart tm H start + 4) ::
        arithmeticFinalConjunctionStackWires tm H start =
    rawConstraints ++ halted.wire :: stackConstraints
  rw [hraw, hhalted, hstack]

/-- Expand one row seed to precisely the post-halted runtime frame of the
complete arithmetic validity-row frame. -/
noncomputable def validityRowSeedTailFrame
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    AffineValidityTailFrame :=
  arithmeticValidityTailFrame tm seed.height seed.start seed.rowBase

/-- Seed expansion agrees definitionally with the tail field of the complete
canonical row-frame expansion. -/
theorem validityRowSeedTailFrame_eq_expand
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    validityRowSeedTailFrame tm seed =
      (expandValidityRowSeed tm seed).tailFrame := by
  rfl

/-- Row-major family of all post-halted stack/cell and conjunction frames. -/
noncomputable def validityRowSeedTailFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineValidityTailFrame :=
  (verifierValidityRowSeeds W input).map
    (validityRowSeedTailFrame W.machine.tm)

/-- Expanding the compiled row seeds recovers exactly the tail fields of the
canonical verifier validity-row family, in the same row order. -/
theorem validityRowSeedTailFamily_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    validityRowSeedTailFamily W input =
      (verifierValidityRowFramesByLength W input.length).map
        (fun frame => frame.tailFrame) := by
  unfold validityRowSeedTailFamily
  rw [← verifierValidityRowSeeds_expand_eq_frames W input]
  rw [List.map_map]
  rfl

/-- Delimiter-bearing target stream for the remaining raw-input source
compiler.  Each row retains both the stack-family terminator and the final
conjunction terminator owned by `encodeAffineValidityTailFrame`. -/
noncomputable def verifierValidityRowTailOperandFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  (validityRowSeedTailFamily W input).flatMap
    encodeAffineValidityTailFrame

/-- The target stream is byte-for-byte the canonical row-major flattening;
in particular, this equality preserves the public conjunction wire order. -/
theorem verifierValidityRowTailOperandFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowTailOperandFrames W input =
      (verifierValidityRowFramesByLength W input.length).flatMap
        (fun frame => encodeAffineValidityTailFrame frame.tailFrame) := by
  unfold verifierValidityRowTailOperandFrames
  rw [validityRowSeedTailFamily_eq_canonical]
  simp [List.flatMap_map]

end CLRS.Chapter34.Turing.CookLevin
