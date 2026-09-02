import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInputCompiler
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionSeedRowSource

/-!
# Transition-seed prefixes through the uniform row-source interface

The raw-input compiler already emits the canonical transition seed triples.
This module exposes that machine as one frame-end-free row per transition
seed, so later descriptor sources can carry their own runtime coordinates.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem seedPrefix_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  cases symbol with
  | tick => decide
  | separator => decide
  | frameEnd =>
      simp [encodeUnaryFrame, encodeUnaryFrameBlock] at hsymbol

/-- Canonical seed coordinates as a marked-row family. -/
def verifierTransitionSeedPrefixFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily where
  rows := (verifierTransitionRowSeeds W input).map fun seed =>
    encodeUnaryFrame [seed.height, seed.start, seed.rowBase]
  frameEnd_free := by
    intro row hrow symbol hsymbol
    rw [List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    exact seedPrefix_encodeUnaryFrame_frameEnd_free _ symbol hsymbol

/-- The pre-existing raw seed compiler has exactly the marked-family target. -/
theorem encode_verifierTransitionSeedPrefixFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionSeedPrefixFamily W input) =
      verifierTransitionRowMarkedSeedFrames W input := by
  rw [verifierTransitionRowMarkedSeedFrames_eq_seeds]
  unfold encodeUnaryFrameMarkedRowFamily verifierTransitionSeedPrefixFamily
  rw [List.flatMap_map]

/-- The canonical seed triple as a uniform one-row-per-transition-seed
source, backed by the concrete raw-input seed compiler. -/
noncomputable def verifierTransitionSeedPrefixRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierTransitionSeedRowSource W where
  row seed := encodeUnaryFrame [seed.height, seed.start, seed.rowBase]
  family := verifierTransitionSeedPrefixFamily W
  rows_eq _ := rfl
  computableInPolyTime := by
    let source :=
      verifierTransitionRowMarkedSeedFrames_computableInPolyTime W
    exact
      { tm := source.tm
        inputAlphabet := source.inputAlphabet
        outputAlphabet := source.outputAlphabet
        time := source.time
        outputsFun := fun input => by
          have run := source.outputsFun input
          rw [encode_verifierTransitionSeedPrefixFamily W input]
          simpa only [id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin
