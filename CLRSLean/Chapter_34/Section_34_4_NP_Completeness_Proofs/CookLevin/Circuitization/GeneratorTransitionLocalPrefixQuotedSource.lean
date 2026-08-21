import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchQuotedLabelProgramSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameUnquoteCore

/-!
# Concrete quoted source for complete local-transition prefixes

The complete recursive dispatch source is extended here by the outer-family
start marker and the fixed dispatch/tail boundary.  Keeping the entire local
prefix quoted preserves the one-row-per-seed invariant needed for the final
pointwise join with the post-dispatch tail.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- One delimiter-safe row containing the outer family marker, the complete
dispatch controller input, and its transition-tail boundary. -/
noncomputable def verifierTransitionLocalPrefixQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierTransitionSeedRowSource W :=
  ((verifierTransitionConstantQuotedSeedRowSource W [.frameEnd]).append
      (verifierTransitionDispatchQuotedSeedRowSource W)).append
    (verifierTransitionConstantQuotedSeedRowSource W
      affineStmtTransitionBoundaryCode)

/-- Exact canonical local-prefix row emitted for every verifier transition
seed. -/
theorem verifierTransitionLocalPrefixQuotedSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionLocalPrefixQuotedSeedRowSource W).row seed =
      quoteUnaryFrameStream
        (.frameEnd ::
          (encodeAffineStmtControllerScript
            (transitionDispatchScriptFromSeed W.machine.tm seed) ++
          affineStmtTransitionBoundaryCode)) := by
  simp only [verifierTransitionLocalPrefixQuotedSeedRowSource,
    VerifierTransitionSeedRowSource.append_row]
  rw [verifierTransitionDispatchQuotedSeedRowSource_row_eq_script W input
    seed hseed]
  simp [verifierTransitionConstantQuotedSeedRowSource,
    quoteUnaryFrameStream_cons, quoteUnaryFrameStream_append]

/-- Public marked family for all complete local prefixes. -/
noncomputable def verifierTransitionLocalPrefixQuotedFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : UnaryFrameMarkedRowFamily :=
  (verifierTransitionLocalPrefixQuotedSeedRowSource W).family input

/-- The family remains aligned byte-for-byte with the canonical transition
seed list. -/
theorem verifierTransitionLocalPrefixQuotedFamily_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    (verifierTransitionLocalPrefixQuotedFamily W input).rows =
      (verifierTransitionRowSeeds W input).map fun seed =>
        quoteUnaryFrameStream
          (.frameEnd ::
            (encodeAffineStmtControllerScript
              (transitionDispatchScriptFromSeed W.machine.tm seed) ++
            affineStmtTransitionBoundaryCode)) := by
  rw [verifierTransitionLocalPrefixQuotedFamily,
    (verifierTransitionLocalPrefixQuotedSeedRowSource W).rows_eq]
  apply List.map_congr_left
  intro seed hseed
  exact verifierTransitionLocalPrefixQuotedSeedRowSource_row_eq W input seed
    hseed

/-- One fixed polynomial-time TM2 produces all quoted local prefixes directly
from the raw verifier input. -/
noncomputable def
    verifierTransitionLocalPrefixQuotedFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionLocalPrefixQuotedFamily W) :=
  (verifierTransitionLocalPrefixQuotedSeedRowSource W).computableInPolyTime

end CLRS.Chapter34.Turing.CookLevin
