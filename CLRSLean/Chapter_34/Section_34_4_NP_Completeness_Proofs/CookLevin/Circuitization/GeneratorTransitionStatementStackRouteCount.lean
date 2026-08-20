import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineUnaryTripleProgression
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedFieldSubtract

/-!
# Runtime count subtraction for terminal stack routes

Push and pop routes reuse affine triple progressions for consecutive source
wires.  Their bases and strides are unchanged, while a verifier-fixed prefix
or suffix removal changes only the seventh descriptor field, the row count.
This module connects that operation to the concrete fixed-field unary TM2.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Keep all affine coordinates and saturating-subtract a fixed number of
rows from the progression count. -/
def transitionStackRouteSubtractCount (amount : Nat)
    (progression : AffineUnaryTripleProgression) :
    AffineUnaryTripleProgression :=
  { progression with count := progression.count - amount }

/-- Row view exposing the seventh progression-descriptor field. -/
def transitionStackRouteCountRow
    (progression : AffineUnaryTripleProgression) :
    UnaryFrameFixedFieldSubtractRow 6 :=
  { leading :=
      [progression.base₁, progression.base₂, progression.base₃,
        progression.step₁, progression.step₂, progression.step₃]
    leading_length := by simp
    selected := progression.count
    suffix := [] }

/-- Marked descriptor family accepted by the fixed-field streaming pass. -/
def encodeTransitionStackRouteCountInput
    (progressions : List AffineUnaryTripleProgression) :
    List UnaryFrameSym :=
  progressions.flatMap fun progression =>
    encodeAffineUnaryTripleProgression progression ++ [.frameEnd]

/-- The same marked family after changing only each row count. -/
def encodeTransitionStackRouteCountOutput (amount : Nat)
    (progressions : List AffineUnaryTripleProgression) :
    List UnaryFrameSym :=
  progressions.flatMap fun progression =>
    encodeAffineUnaryTripleProgression
        (transitionStackRouteSubtractCount amount progression) ++
      [.frameEnd]

private theorem encodeTransitionStackRouteCountInput_eq_rows
    (progressions : List AffineUnaryTripleProgression) :
    encodeTransitionStackRouteCountInput progressions =
      encodeUnaryFrameFixedFieldSubtractInput 6
        (progressions.map transitionStackRouteCountRow) := by
  unfold encodeTransitionStackRouteCountInput
    encodeUnaryFrameFixedFieldSubtractInput
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro progression hprogression
  rfl

private theorem encodeTransitionStackRouteCountOutput_eq_rows
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    encodeTransitionStackRouteCountOutput amount progressions =
      encodeUnaryFrameFixedFieldSubtractOutput 6 amount
        (progressions.map transitionStackRouteCountRow) := by
  unfold encodeTransitionStackRouteCountOutput
    encodeUnaryFrameFixedFieldSubtractOutput
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro progression hprogression
  rfl

/-- The concrete unary pass preserves every base and stride and changes
exactly the runtime progression counts to `count - amount`. -/
theorem rewriteTransitionStackRouteCounts
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    rewriteUnaryFrameFixedFieldSubtract 6 amount
        (encodeTransitionStackRouteCountInput progressions) =
      encodeTransitionStackRouteCountOutput amount progressions := by
  rw [encodeTransitionStackRouteCountInput_eq_rows,
    rewriteUnaryFrameFixedFieldSubtract_rows,
    ← encodeTransitionStackRouteCountOutput_eq_rows]

/-- The count-adjustment pass is one fixed polynomial-time TM2 for each
verifier-fixed removal amount. -/
noncomputable def transitionStackRouteCountCompiler_computableInPolyTime
    (amount : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (rewriteUnaryFrameFixedFieldSubtract 6 amount) :=
  unaryFrameFixedFieldSubtract_computableInPolyTime 6 amount

end CLRS.Chapter34.Turing.CookLevin
