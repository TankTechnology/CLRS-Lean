import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionInitialStatementQuotedRowSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionDispatchQuotedMuxLabelSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionConstantQuotedRowSource

/-!
# Complete quoted controller source folded over program labels

For every fixed label position, the source concatenates the complete
recursive statement row, the outer mux phase tag, and the selected outer mux
invocation row.  Folding these sources in canonical label order preserves one
physical row per transition seed and the exact statement/mux interleaving.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Explicit quoted-row semantics for a suffix of canonical program labels.
The mux row is read from the independently generated complete artifact family
at the fixed global label position. -/
def transitionDispatchQuotedControllerRowForLabels
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed) :
    Nat → TransitionAffineNat → List tm.Λ → List UnaryFrameSym
  | _, _, [] => []
  | position, labelOffset, label :: labels =>
      quoteUnaryFrameStream
          (encodeAffineStmtControllerScript
            (transitionStmtScript tm (workHeight tm seed.height)
              seed.start (seed.start + 1)
              (seed.start + labelOffset.eval seed.height)
              (arithmeticWidenedCfgWires tm seed.height seed.start
                seed.rowBase)
              (tm.m label) (stmtPushSet_program_subset tm label))) ++
        quoteUnaryFrameStream (transitionStmtPhaseKindTagCode .mux) ++
        (transitionDispatchQuotedMuxRowsFromSeed tm seed).getD position [] ++
        transitionDispatchQuotedControllerRowForLabels tm seed
          (position + 1)
          ((labelOffset.add (transitionDispatchStmtGateAffine tm label)).add
            (transitionDispatchMuxGateAffine tm)) labels

/-- Concrete source for a label suffix.  The length invariant turns the
current natural position into the fixed finite-control mux selector. -/
noncomputable def verifierTransitionLabelListQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    ∀ (position : Nat) (_labelOffset : TransitionAffineNat)
      (labels : List W.machine.tm.Λ),
      position + labels.length = labelCount W.machine.tm →
        VerifierTransitionSeedRowSource W
  | _, _, [], _ => verifierTransitionAffineHeadQuotedSeedRowSource W []
  | position, labelOffset, label :: labels, hinvariant =>
      let labelPosition : Fin (labelCount W.machine.tm) :=
        ⟨position, by
          simp only [List.length_cons] at hinvariant
          omega⟩
      let statement :=
        verifierTransitionInitialStmtQuotedSeedRowSource W labelOffset label
      let muxTag := verifierTransitionConstantQuotedSeedRowSource W
        (transitionStmtPhaseKindTagCode .mux)
      let mux := verifierTransitionDispatchQuotedMuxLabelSeedRowSource W
        labelPosition
      let nextOffset :=
        ((labelOffset.add
          (transitionDispatchStmtGateAffine W.machine.tm label)).add
            (transitionDispatchMuxGateAffine W.machine.tm))
      let tail := verifierTransitionLabelListQuotedSeedRowSource W
        (position + 1) nextOffset labels (by
          simp only [List.length_cons] at hinvariant
          omega)
      (((statement.append muxTag).append mux).append tail)

/-- The physical suffix source has exactly the explicit statement/tag/mux
row semantics on every canonical transition seed. -/
theorem verifierTransitionLabelListQuotedSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    ∀ (position : Nat) (labelOffset : TransitionAffineNat)
      (labels : List W.machine.tm.Λ)
      (hinvariant : position + labels.length = labelCount W.machine.tm),
      (verifierTransitionLabelListQuotedSeedRowSource W position labelOffset
          labels hinvariant).row seed =
        transitionDispatchQuotedControllerRowForLabels W.machine.tm seed
          position labelOffset labels := by
  intro position labelOffset labels
  induction labels generalizing position labelOffset with
  | nil =>
      intro hinvariant
      rfl
  | cons label labels ih =>
      intro hinvariant
      simp only [verifierTransitionLabelListQuotedSeedRowSource,
        transitionDispatchQuotedControllerRowForLabels,
        VerifierTransitionSeedRowSource.append_row]
      rw [verifierTransitionInitialStmtQuotedSeedRowSource_row_eq_script W
        labelOffset label input seed hseed]
      rw [ih (position + 1)
        ((labelOffset.add
          (transitionDispatchStmtGateAffine W.machine.tm label)).add
            (transitionDispatchMuxGateAffine W.machine.tm)) (by
          simp only [List.length_cons] at hinvariant
          omega)]
      rfl

/-- Concrete complete quoted dispatch source for every verifier transition
seed. -/
noncomputable def verifierTransitionDispatchQuotedSeedRowSource
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    VerifierTransitionSeedRowSource W :=
  verifierTransitionLabelListQuotedSeedRowSource W 0
    (TransitionAffineNat.const 2) (programLabels W.machine.tm) (by
      simp [programLabels])

/-- Exact row emitted by the complete physical label fold. -/
theorem verifierTransitionDispatchQuotedSeedRowSource_row_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) (seed : TransitionRowSeed)
    (hseed : seed ∈ verifierTransitionRowSeeds W input) :
    (verifierTransitionDispatchQuotedSeedRowSource W).row seed =
      transitionDispatchQuotedControllerRowForLabels W.machine.tm seed 0
        (TransitionAffineNat.const 2) (programLabels W.machine.tm) := by
  unfold verifierTransitionDispatchQuotedSeedRowSource
  exact verifierTransitionLabelListQuotedSeedRowSource_row_eq W input seed
    hseed 0 (TransitionAffineNat.const 2) (programLabels W.machine.tm) _

end CLRS.Chapter34.Turing.CookLevin
