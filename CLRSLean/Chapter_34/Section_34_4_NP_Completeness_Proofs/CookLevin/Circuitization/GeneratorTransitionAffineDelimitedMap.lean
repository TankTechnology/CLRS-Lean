import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameDelimiterMapCycle

/-!
# Fixed-delimiter affine transition sources

The basic transition affine-map source emits every numeric operand with an
ordinary unary separator.  Statement-controller payloads instead use fixed
mixtures of `tick`, `separator`, and `frameEnd`.  This module composes the
affine source with the verified cyclic delimiter transducer and proves that
one complete delimiter table is consumed for every transition row.

Literal control bytes can be represented by a zero affine operand followed
by that byte.  Consequently this compiler is the common source layer for the
fixed-layout statement phases without placing any runtime dimension in finite
control.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem flatMap_eq_map_flatten {α β : Type}
    (values : List α) (f : α → List β) :
    values.flatMap f = (values.map f).flatten := by
  induction values with
  | nil => rfl
  | cons value values ih => simp [ih]

/-- Evaluate a fixed affine form table on one transition seed and serialize
the resulting row with the verifier-fixed delimiter table. -/
def transitionAffineDelimitedMapRow
    (forms : List AffineUnaryTripleForm)
    (delimiters : List UnaryFrameSym) (seed : TransitionRowSeed) :
    List UnaryFrameSym :=
  encodeUnaryFrameWithFixedDelimiters
    (affineUnaryTripleMap forms (transitionTailAffineSeed seed)) delimiters

/-- Concrete raw-input target for a fixed delimiter-bearing affine row at
every adjacent tableau-row pair. -/
noncomputable def verifierTransitionAffineDelimitedMapFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (input : List Γ) : List UnaryFrameSym :=
  rewriteUnaryFrameDelimiters delimiters hnonempty
    (verifierTransitionAffineMapFrames W forms input)

/-- The physical delimiter transducer resets after each fixed-width affine
row, so its output is literally the row-major fixed-delimiter target. -/
theorem verifierTransitionAffineDelimitedMapFrames_eq_rows
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length)
    (haligned : forms.length = delimiters.length)
    (input : List Γ) :
    verifierTransitionAffineDelimitedMapFrames W forms delimiters hnonempty
        input =
      (verifierTransitionRowSeeds W input).flatMap
        (transitionAffineDelimitedMapRow forms delimiters) := by
  unfold verifierTransitionAffineDelimitedMapFrames
    verifierTransitionAffineMapFrames verifierTransitionTailAffineSeeds
  rw [rewriteUnaryFrameDelimiters_encodeUnaryFrame]
  let rows :=
    ((verifierTransitionRowSeeds W input).map transitionTailAffineSeed).map
      (affineUnaryTripleMap forms)
  have hrowsLength : ∀ row ∈ rows, row.length = delimiters.length := by
    intro row hrow
    simp only [rows, List.mem_map] at hrow
    rcases hrow with ⟨seed, _, rfl⟩
    simpa [affineUnaryTripleMap] using haligned
  rw [show affineUnaryTripleMapFamily forms
          ((verifierTransitionRowSeeds W input).map transitionTailAffineSeed) =
        rows.flatten by
      unfold affineUnaryTripleMapFamily rows
      exact flatMap_eq_map_flatten _ _]
  rw [encodeUnaryFrameWithDelimiterCycle_eq_fixedRows delimiters hnonempty
    rows hrowsLength]
  unfold rows
  rw [List.flatMap_map]
  rw [List.flatMap_map]
  rfl

/-- One fixed polynomial-time TM2 emits the complete delimiter-bearing
affine row family directly from the original verifier word. -/
noncomputable def
    verifierTransitionAffineDelimitedMapFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm)
    (delimiters : List UnaryFrameSym)
    (hnonempty : 0 < delimiters.length) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierTransitionAffineDelimitedMapFrames W forms delimiters
        hnonempty) := by
  let source := verifierTransitionAffineMapFrames_computableInPolyTime W forms
  let delimited := unaryFrameDelimiterMap_computableInPolyTime delimiters
    hnonempty
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch source
      delimited
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => rewriteUnaryFrameDelimiters delimiters hnonempty
      (verifierTransitionAffineMapFrames W forms input))
  simpa only [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
