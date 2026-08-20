import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionEqPhaseSentinels
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionNarrowNotFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionFinalAndFrames
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixSplice
import Mathlib.Tactic

/-!
# Affine fields carried by transition-tail phase sentinels

The prefix and suffix sentinels store `(tag, height, start)` rather than the
ordinary transition seed `(height, start, rowBase)`.  This module transports
all row-base-free narrowing and final-conjunction form tables to that layout,
and fixes delimiter tables of the same lengths for the forthcoming finite
three-way router.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Reindex a transition-seed form onto `(tag, height, start)`.  The original
row-base coefficient is evaluated at zero. -/
def transitionTailPhaseLiftForm
    (form : AffineUnaryTripleForm) : AffineUnaryTripleForm :=
  { constant := form.constant
    first := 0
    second := form.first
    third := form.second }

def transitionTailPhaseLiftForms
    (forms : List AffineUnaryTripleForm) : List AffineUnaryTripleForm :=
  forms.map transitionTailPhaseLiftForm

/-- Synthetic ordinary transition seed denoted by a phase coordinate. -/
def transitionTailPhaseRowSeed
    (coordinate : AffineUnaryTripleSeed) : TransitionRowSeed :=
  { height := coordinate.second
    start := coordinate.third
    rowBase := 0 }

@[simp] theorem transitionTailPhaseLiftForms_value
    (forms : List AffineUnaryTripleForm)
    (coordinate : AffineUnaryTripleSeed) :
    affineUnaryTripleMap (transitionTailPhaseLiftForms forms) coordinate =
      affineUnaryTripleMap forms
        (transitionTailAffineSeed
          (transitionTailPhaseRowSeed coordinate)) := by
  unfold transitionTailPhaseLiftForms affineUnaryTripleMap
  rw [List.map_map]
  apply List.map_congr_left
  intro form _
  simp [transitionTailPhaseLiftForm, transitionTailPhaseRowSeed,
    transitionTailAffineSeed, affineUnaryTripleFormValue]

/-- Prefix selected by tag zero: all narrowing OR fields, the final NOT
fields, and one zero field whose delimiter becomes the equality-phase tick. -/
noncomputable def transitionTailPrefixPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionTailPhaseLiftForms
      (transitionNarrowInvocationForms tm ++
        transitionNarrowNotInvocationForms tm) ++
    [transitionZeroForm]

/-- Suffix selected by tag one: equality-phase tick, final AND fields, and
the local-transition row terminator. -/
noncomputable def transitionTailSuffixPhaseForms
    (tm : _root_.Turing.FinTM2) : List AffineUnaryTripleForm :=
  transitionZeroForm ::
    (transitionTailPhaseLiftForms
      (transitionFinalAndInvocationForms tm) ++ [transitionZeroForm])

/-- Exact ordinary prefix values on the tag-zero sentinel. -/
theorem transitionTailPrefixPhaseForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionTailPrefixPhaseForms tm)
        (transitionEqPrefixSentinelCoordinateSeed seed) =
      transitionNarrowInvocationValues tm seed ++
        transitionNarrowNotInvocationValues tm seed ++ [0] := by
  let phaseSeed : TransitionRowSeed :=
    { height := seed.height, start := seed.start, rowBase := 0 }
  have hnarrow := transitionNarrowInvocationForms_value tm phaseSeed hwork
  have hnot := transitionNarrowNotInvocationForms_value tm phaseSeed hwork
  unfold transitionTailPrefixPhaseForms
  rw [show affineUnaryTripleMap
          (transitionTailPhaseLiftForms
              (transitionNarrowInvocationForms tm ++
                transitionNarrowNotInvocationForms tm) ++
            [transitionZeroForm])
          (transitionEqPrefixSentinelCoordinateSeed seed) =
        affineUnaryTripleMap
            (transitionTailPhaseLiftForms
              (transitionNarrowInvocationForms tm ++
                transitionNarrowNotInvocationForms tm))
            (transitionEqPrefixSentinelCoordinateSeed seed) ++
          affineUnaryTripleMap [transitionZeroForm]
            (transitionEqPrefixSentinelCoordinateSeed seed) by
      simp [affineUnaryTripleMap, List.map_append]]
  rw [transitionTailPhaseLiftForms_value]
  change affineUnaryTripleMap
      (transitionNarrowInvocationForms tm ++
        transitionNarrowNotInvocationForms tm)
      (transitionTailAffineSeed phaseSeed) ++ _ = _
  rw [show affineUnaryTripleMap
          (transitionNarrowInvocationForms tm ++
            transitionNarrowNotInvocationForms tm)
          (transitionTailAffineSeed phaseSeed) =
        affineUnaryTripleMap (transitionNarrowInvocationForms tm)
            (transitionTailAffineSeed phaseSeed) ++
          affineUnaryTripleMap (transitionNarrowNotInvocationForms tm)
            (transitionTailAffineSeed phaseSeed) by
      simp [affineUnaryTripleMap, List.map_append]]
  rw [hnarrow, hnot]
  simp [phaseSeed, transitionNarrowInvocationValues,
    transitionNarrowNotInvocationValues, transitionZeroForm,
    affineUnaryTripleMap, affineUnaryTripleFormValue,
    transitionEqPrefixSentinelCoordinateSeed]
  congr 1
  rw [transitionDispatchOutputWires_eq_finalMux,
    transitionDispatchOutputWires_eq_finalMux]

/-- Exact ordinary suffix values on the tag-one sentinel. -/
theorem transitionTailSuffixPhaseForms_value
    (tm : _root_.Turing.FinTM2) (seed : TransitionRowSeed)
    (hwork : 0 < workHeight tm seed.height) :
    affineUnaryTripleMap (transitionTailSuffixPhaseForms tm)
        (transitionEqSuffixSentinelCoordinateSeed seed) =
      [0] ++ transitionFinalAndInvocationValues tm seed ++ [0] := by
  let phaseSeed : TransitionRowSeed :=
    { height := seed.height, start := seed.start, rowBase := 0 }
  have hfinal := transitionFinalAndInvocationForms_value tm phaseSeed hwork
  unfold transitionTailSuffixPhaseForms
  change affineUnaryTripleFormValue transitionZeroForm
        (transitionEqSuffixSentinelCoordinateSeed seed) ::
      (affineUnaryTripleMap
          (transitionTailPhaseLiftForms
            (transitionFinalAndInvocationForms tm))
          (transitionEqSuffixSentinelCoordinateSeed seed) ++
        [affineUnaryTripleFormValue transitionZeroForm
          (transitionEqSuffixSentinelCoordinateSeed seed)]) = _
  rw [transitionTailPhaseLiftForms_value]
  change affineUnaryTripleFormValue transitionZeroForm
        (transitionEqSuffixSentinelCoordinateSeed seed) ::
      (affineUnaryTripleMap
          (transitionFinalAndInvocationForms tm)
          (transitionTailAffineSeed phaseSeed) ++
        [affineUnaryTripleFormValue transitionZeroForm
          (transitionEqSuffixSentinelCoordinateSeed seed)]) = _
  rw [hfinal]
  simp [phaseSeed, transitionFinalAndInvocationValues,
    transitionZeroForm, affineUnaryTripleFormValue,
    transitionEqSuffixSentinelCoordinateSeed]

private theorem zipWith_const_of_lengths {alpha beta : Type}
    (constant count : Nat) (left : List alpha) (right : List beta)
    (hleft : left.length = count) (hright : right.length = count) :
    List.zipWith (fun _ _ => constant) left right =
      List.replicate count constant := by
  induction count generalizing left right with
  | zero =>
      cases left <;> cases right <;> simp_all
  | succ count ih =>
      cases left with
      | nil => simp at hleft
      | cons first left =>
          cases right with
          | nil => simp at hright
          | cons second right =>
              simp only [List.length_cons, Nat.succ.injEq] at hleft hright
              simp only [List.zipWith_cons_cons, List.replicate_succ,
                List.cons.injEq, true_and]
              exact ih left right hleft hright

theorem transitionNarrowInvocationForms_length
    (tm : _root_.Turing.FinTM2) :
    (transitionNarrowInvocationForms tm).length =
      5 * (Fintype.card tm.K * maxPushesPerStep tm) := by
  unfold transitionNarrowInvocationForms
  rw [List.length_flatten]
  simp only [List.map_zipWith, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  rw [zipWith_const_of_lengths 5
    (Fintype.card tm.K * maxPushesPerStep tm)]
  · simp
    ring
  · simp [transitionNarrowLeftForms,
      transitionNarrowOverflowWireForms]
  · simp [transitionNarrowRightSuccForms]

/-- Fixed delimiter table materializing the complete narrowing input and the
following equality-phase tick. -/
def transitionTailPrefixPhaseDelimiters
    (tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  (List.replicate (Fintype.card tm.K * maxPushesPerStep tm)
      transitionNarrowInvocationDelimiterTable).flatten ++
    transitionNarrowNotInvocationDelimiterTable ++ [.tick]

/-- Fixed delimiter table materializing equality-to-AND tick, final AND, and
the local row terminator. -/
def transitionTailSuffixPhaseDelimiters
    (_tm : _root_.Turing.FinTM2) : List UnaryFrameSym :=
  [.tick] ++ transitionFinalAndInvocationDelimiterTable ++ [.frameEnd]

@[simp] theorem transitionTailPrefixPhaseForms_delimiters_length
    (tm : _root_.Turing.FinTM2) :
    (transitionTailPrefixPhaseForms tm).length =
      (transitionTailPrefixPhaseDelimiters tm).length := by
  rw [show (transitionTailPrefixPhaseForms tm).length =
      (transitionNarrowInvocationForms tm).length +
        (transitionNarrowNotInvocationForms tm).length + 1 by
    simp [transitionTailPrefixPhaseForms, transitionTailPhaseLiftForms,
      Nat.add_assoc]]
  rw [transitionNarrowInvocationForms_length]
  simp [transitionTailPrefixPhaseDelimiters,
    transitionNarrowNotInvocationForms,
    transitionNarrowInvocationDelimiterTable,
    transitionNarrowNotInvocationDelimiterTable]
  omega

@[simp] theorem transitionTailSuffixPhaseForms_delimiters_length
    (tm : _root_.Turing.FinTM2) :
    (transitionTailSuffixPhaseForms tm).length =
      (transitionTailSuffixPhaseDelimiters tm).length := by
  simp [transitionTailSuffixPhaseForms,
    transitionTailSuffixPhaseDelimiters, transitionTailPhaseLiftForms,
    transitionFinalAndInvocationForms,
    transitionFinalAndInvocationDelimiterTable]

end CLRS.Chapter34.Turing.CookLevin
