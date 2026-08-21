import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailAffine
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedFieldRowMark
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowDuplicate

/-!
# Marked descriptor rows for fixed affine form tables

A nonempty verifier-fixed affine form table evaluates to one numeric row per
transition seed.  The generic fixed-field row marker preserves every ordinary
unary field separator and appends one outer marker, exposing the result as a
typed row family suitable for same-input row-wise concatenation.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

private theorem affineFormDescriptor_encodeUnaryFrame_frameEnd_free
    (values : List Nat) :
    ∀ symbol ∈ encodeUnaryFrame values,
      symbol ≠ UnaryFrameSym.frameEnd := by
  intro symbol hsymbol
  rw [encodeUnaryFrame, List.mem_flatMap] at hsymbol
  rcases hsymbol with ⟨value, _, hblock⟩
  simp [encodeUnaryFrameBlock] at hblock
  rcases hblock with ⟨_, rfl⟩ | rfl <;> simp

/-- One delimiter-free numeric affine image row per transition seed. -/
noncomputable def verifierTransitionAffineFormDescriptorFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm) (input : List Γ) :
    UnaryFrameMarkedRowFamily :=
  { rows := (verifierTransitionRowSeeds W input).map fun seed =>
      encodeUnaryFrame
        (affineUnaryTripleMap forms (transitionTailAffineSeed seed))
    frameEnd_free := by
      intro row hrow symbol hsymbol
      rw [List.mem_map] at hrow
      rcases hrow with ⟨seed, hseed, rfl⟩
      exact affineFormDescriptor_encodeUnaryFrame_frameEnd_free _ symbol
        hsymbol }

/-- Marking the ordinary affine-map output yields exactly the typed numeric
descriptor family. -/
theorem verifierTransitionAffineFormDescriptorFamily_encoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm) (hnonempty : forms ≠ [])
    (input : List Γ) :
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionAffineFormDescriptorFamily W forms input) =
      markUnaryFrameFixedFieldRows forms.length
        (verifierTransitionAffineMapFrames W forms input) := by
  let rows := (verifierTransitionRowSeeds W input).map fun seed =>
    affineUnaryTripleMap forms (transitionTailAffineSeed seed)
  have hpositive : 0 < forms.length := List.length_pos_iff.mpr hnonempty
  have hlength : ∀ row ∈ rows, row.length = forms.length := by
    intro row hrow
    simp only [rows, List.mem_map] at hrow
    rcases hrow with ⟨seed, hseed, rfl⟩
    simp [affineUnaryTripleMap]
  have hmark := markUnaryFrameFixedFieldRows_encode forms.length hpositive
    rows hlength
  calc
    encodeUnaryFrameMarkedRowFamily
        (verifierTransitionAffineFormDescriptorFamily W forms input) =
        encodeUnaryFrameFixedFieldMarkedRows rows := by
      simp [verifierTransitionAffineFormDescriptorFamily,
        encodeUnaryFrameMarkedRowFamily,
        encodeUnaryFrameFixedFieldMarkedRows, rows, List.flatMap_map,
        ]
    _ = markUnaryFrameFixedFieldRows forms.length
        (encodeUnaryFrame rows.flatten) := hmark.symm
    _ = markUnaryFrameFixedFieldRows forms.length
        (verifierTransitionAffineMapFrames W forms input) := by
      congr 1
      simp [rows, verifierTransitionAffineMapFrames,
        verifierTransitionTailAffineSeeds, affineUnaryTripleMapFamily,
        List.flatten_eq_flatMap, List.flatMap_map]

/-- Every fixed nonempty affine form table has a concrete polynomial-time
raw-input descriptor-family source. -/
noncomputable def
    verifierTransitionAffineFormDescriptorFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (forms : List AffineUnaryTripleForm) (hnonempty : forms ≠ []) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeUnaryFrameMarkedRowFamily
      (verifierTransitionAffineFormDescriptorFamily W forms) := by
  let affineSource := verifierTransitionAffineMapFrames_computableInPolyTime
    W forms
  let markedExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch affineSource
      (markUnaryFrameFixedFieldRows_computableInPolyTime forms.length)
  let marked := Classical.choice markedExists
  exact
    { tm := marked.tm
      inputAlphabet := marked.inputAlphabet
      outputAlphabet := marked.outputAlphabet
      time := marked.time
      outputsFun := fun input => by
        have run := marked.outputsFun input
        rw [verifierTransitionAffineFormDescriptorFamily_encoding_eq W forms
          hnonempty input]
        simpa only [Function.comp_def, id_eq] using run }

end CLRS.Chapter34.Turing.CookLevin
