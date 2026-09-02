import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRow
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ValidityRowFamily

/-!
# Runtime generation of every Cook--Levin validity row

This module closes the height-dependent iteration gap left by the one-row
controller. A single finite controller consumes an explicit list of arithmetic
row frames and emits exactly the canonical row-major validity stream.
-/

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder
open StateTransition

noncomputable section

/-- Exact runtime frames for every arithmetic tableau row. -/
noncomputable def arithmeticValidityRowFrames
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    List AffineValidityRowFrame :=
  List.ofFn fun row : Fin (tableauRowCount T) =>
    arithmeticValidityRowFrame tm H
      (tableauInputCount tm H T + 2 +
        row.val * validCfgGateCost tm H)
      (row.val * cfgBitCount tm H)

/-- The runtime family emits byte-for-byte the full semantic validity stream. -/
theorem arithmeticValidityRowsGateStream_eq_semantic
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    affineValidityRowFamilyGateStream
        (arithmeticValidityRowFrames tm H T) =
      validityGateStreamAt tm H T := by
  rw [validityGateStreamAt_rows_eq,
    affineValidityRowFamilyGateStream_eq_flatMap]
  unfold arithmeticValidityRowFrames
  rw [List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext row
  exact arithmeticValidityRowGateStream_eq_semantic tm H
    (tableauInputCount tm H T + 2 + row.val * validCfgGateCost tm H)
    (row.val * cfgBitCount tm H)

/-- One fixed program executes every canonical validity row at the supplied
height and horizon dimensions. -/
noncomputable def arithmeticValidityRowsRev_runFrom
    (tm : _root_.Turing.FinTM2) (H T : Nat)
    (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (encodeAffineValidityRowFamilyInput
          (arithmeticValidityRowFrames tm H T)) output)
      (some (haltCfg affineValidityRowFamilyRevProgram
        ((validityGateStreamAt tm H T).reverse ++ output)))
      (affineValidityRowFamilyRevSteps
        (arithmeticValidityRowFrames tm H T)) := by
  simpa [arithmeticValidityRowsGateStream_eq_semantic] using
    affineValidityRowFamily_run
      (arithmeticValidityRowFrames tm H T) output

/-- The concrete all-row execution inherits the explicit quadratic bound in
its exact delimiter-bearing runtime input. -/
theorem arithmeticValidityRowsRev_steps_le
    (tm : _root_.Turing.FinTM2) (H T : Nat) :
    affineValidityRowFamilyRevSteps
        (arithmeticValidityRowFrames tm H T) ≤
      2600 * (encodeAffineValidityRowFamilyInput
        (arithmeticValidityRowFrames tm H T)).length ^ 2 + 2 :=
  affineValidityRowFamilyRev_steps_le _

/-- Verifier-specialized all-row frames, depending on the source instance
only through its encoded length. -/
noncomputable def verifierValidityRowFramesByLength
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (inputLength : Nat) : List AffineValidityRowFrame :=
  arithmeticValidityRowFrames W.machine.tm
    ((verifierHeight W).eval inputLength)
    ((verifierHorizon W).eval inputLength)

/-- Exact all-row execution at a verifier input length. -/
noncomputable def verifierValidityRowsRev_runFromByLength
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (inputLength : Nat) (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (encodeAffineValidityRowFamilyInput
          (verifierValidityRowFramesByLength W inputLength)) output)
      (some (haltCfg affineValidityRowFamilyRevProgram
        ((verifierValidityGateStreamByLength W inputLength).reverse ++
          output)))
      (affineValidityRowFamilyRevSteps
        (verifierValidityRowFramesByLength W inputLength)) := by
  exact arithmeticValidityRowsRev_runFrom W.machine.tm
    ((verifierHeight W).eval inputLength)
    ((verifierHorizon W).eval inputLength) output

/-- Exact all-row execution for a concrete verifier input. -/
noncomputable def verifierValidityRowsRev_runFrom
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (output : List CircuitSym) :
    EvalsToInTime (step affineValidityRowFamilyRevProgram)
      (affineValidityRowFamilyLoopCfg
        (encodeAffineValidityRowFamilyInput
          (verifierValidityRowFramesByLength W input.length)) output)
      (some (haltCfg affineValidityRowFamilyRevProgram
        ((verifierValidityGateStream W input).reverse ++ output)))
      (affineValidityRowFamilyRevSteps
        (verifierValidityRowFramesByLength W input.length)) := by
  simpa [verifierValidityGateStream_eq_byLength] using
    verifierValidityRowsRev_runFromByLength W input.length output

end

end CLRS.Chapter34.Turing.CookLevin
