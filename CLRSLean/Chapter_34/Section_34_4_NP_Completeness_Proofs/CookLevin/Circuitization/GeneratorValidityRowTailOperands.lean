import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds

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
