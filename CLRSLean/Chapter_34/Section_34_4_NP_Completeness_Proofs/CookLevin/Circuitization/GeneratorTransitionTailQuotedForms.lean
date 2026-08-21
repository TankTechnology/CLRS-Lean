import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionTailPhaseForms
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleQuotedFixedDelimiters

/-!
# Affine form tables for delimiter-safe transition tails

Every selected tail fragment is emitted directly in two-symbol quotation.
The suffix's final field is the only exception: it remains one literal
`frameEnd`, serving as the outer boundary of the complete transition row.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Suffix fields before the outer local-row terminator. -/
noncomputable def transitionTailSuffixInnerPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionZeroForm ::
    transitionTailPhaseLiftForms (transitionFinalAndInvocationForms tm)

/-- Suffix delimiters before the outer local-row terminator. -/
def transitionTailSuffixInnerPhaseDelimiters
    (_tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  [.tick] ++ transitionFinalAndInvocationDelimiterTable

/-- Fully quoted narrowing-prefix form table. -/
noncomputable def transitionTailQuotedPrefixPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  quoteAffineUnaryTripleForms (transitionTailPrefixPhaseForms tm)

def transitionTailQuotedPrefixPhaseDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  quoteFixedDelimiterTable (transitionTailPrefixPhaseDelimiters tm)

/-- Quoted equality-to-AND suffix followed by one literal outer boundary
field. -/
noncomputable def transitionTailQuotedSuffixPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  quoteAffineUnaryTripleForms (transitionTailSuffixInnerPhaseForms tm) ++
    [affineUnaryTripleZeroForm]

def transitionTailQuotedSuffixPhaseDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  quoteFixedDelimiterTable
      (transitionTailSuffixInnerPhaseDelimiters tm) ++ [.frameEnd]

/-- Fully quoted ordinary equality-frame form table. -/
noncomputable def transitionTailQuotedEqPhaseForms :
    List AffineUnaryTripleForm :=
  quoteAffineUnaryTripleForms transitionEqInvocationForms

def transitionTailQuotedEqPhaseDelimiters : List UnaryFrameSym :=
  quoteFixedDelimiterTable transitionEqInvocationDelimiterTable

@[simp] theorem transitionTailSuffixInnerPhase_lengths
    (tm : _root_.Turing.FinTM2) :
    (transitionTailSuffixInnerPhaseForms tm).length =
      (transitionTailSuffixInnerPhaseDelimiters tm).length := by
  simp [transitionTailSuffixInnerPhaseForms,
    transitionTailSuffixInnerPhaseDelimiters,
    transitionTailPhaseLiftForms,
    transitionFinalAndInvocationForms,
    transitionFinalAndInvocationDelimiterTable]

@[simp] theorem transitionTailQuotedPrefixPhase_lengths
    (tm : _root_.Turing.FinTM2) :
    (transitionTailQuotedPrefixPhaseForms tm).length =
      (transitionTailQuotedPrefixPhaseDelimiters tm).length := by
  simp [transitionTailQuotedPrefixPhaseForms,
    transitionTailQuotedPrefixPhaseDelimiters]

@[simp] theorem transitionTailQuotedSuffixPhase_lengths
    (tm : _root_.Turing.FinTM2) :
    (transitionTailQuotedSuffixPhaseForms tm).length =
      (transitionTailQuotedSuffixPhaseDelimiters tm).length := by
  simp [transitionTailQuotedSuffixPhaseForms,
    transitionTailQuotedSuffixPhaseDelimiters]

@[simp] theorem transitionTailQuotedEqPhase_lengths :
    transitionTailQuotedEqPhaseForms.length =
      transitionTailQuotedEqPhaseDelimiters.length := by
  simp [transitionTailQuotedEqPhaseForms,
    transitionTailQuotedEqPhaseDelimiters,
    transitionEqInvocationForms, transitionEqInvocationDelimiterTable]

theorem transitionTailQuotedPrefixPhase_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailQuotedPrefixPhaseForms tm)
        coordinate =
      quoteAffineUnaryValues
        (affineUnaryTripleMap (transitionTailPrefixPhaseForms tm)
          coordinate) := by
  exact affineUnaryTripleMap_quoteForms _ _

theorem transitionTailQuotedSuffixPhase_value
    (tm : _root_.Turing.FinTM2) (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailQuotedSuffixPhaseForms tm)
        coordinate =
      quoteAffineUnaryValues
          (affineUnaryTripleMap
            (transitionTailSuffixInnerPhaseForms tm) coordinate) ++ [0] := by
  unfold transitionTailQuotedSuffixPhaseForms affineUnaryTripleMap
  rw [List.map_append]
  simp only [List.map_singleton, affineUnaryTripleZeroForm_value]
  rw [show List.map (fun form => affineUnaryTripleFormValue form coordinate)
          (quoteAffineUnaryTripleForms
            (transitionTailSuffixInnerPhaseForms tm)) =
        quoteAffineUnaryValues
          (List.map (fun form => affineUnaryTripleFormValue form coordinate)
            (transitionTailSuffixInnerPhaseForms tm)) by
    simpa only [affineUnaryTripleMap] using
      affineUnaryTripleMap_quoteForms
        (transitionTailSuffixInnerPhaseForms tm) coordinate]

theorem transitionTailQuotedEqPhase_value
    (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap transitionTailQuotedEqPhaseForms coordinate =
      quoteAffineUnaryValues
        (affineUnaryTripleMap transitionEqInvocationForms coordinate) := by
  exact affineUnaryTripleMap_quoteForms _ _

end CLRS.Chapter34.Turing.CookLevin
