import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDropSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameFixedPrefixDrop

/-!
# Prefix dropping across affine progression families

A stack source is piecewise affine: public coordinates, overflow height bits,
and blank-cell constants occupy separate progression descriptors.  A pop can
cross one of those boundaries at small tableau heights.  The carried-drop
normalizer below handles that case uniformly.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Drop a fixed number of generated rows across a descriptor family.  Empty
segments consume no budget; a partial final segment is shifted and shortened. -/
def transitionStackRouteDropFamily :
    Nat → List AffineUnaryTripleProgression →
      List AffineUnaryTripleProgression
  | _, [] => []
  | amount, progression :: rest =>
      if amount < progression.count then
        transitionStackRouteDropPrefix amount progression :: rest
      else
        transitionStackRouteDropFamily
          (amount - progression.count) rest

/-- The carried descriptor normalization denotes exactly dropping the same
prefix from the concatenated generated row stream. -/
theorem transitionStackRouteDropFamily_rows
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    (transitionStackRouteDropFamily amount progressions).flatMap
        affineUnaryTripleProgressionRows =
      (progressions.flatMap affineUnaryTripleProgressionRows).drop amount := by
  induction progressions generalizing amount with
  | nil => simp [transitionStackRouteDropFamily]
  | cons progression rest ih =>
      have hlength :
          (affineUnaryTripleProgressionRows progression).length =
            progression.count := by
        rw [affineUnaryTripleProgressionRows_eq_ofFn]
        simp
      unfold transitionStackRouteDropFamily
      by_cases hpartial : amount < progression.count
      · simp only [if_pos hpartial, List.flatMap_cons]
        rw [transitionStackRouteDropPrefix_rows]
        rw [List.drop_append_of_le_length]
        simpa [hlength] using Nat.le_of_lt hpartial
      · simp only [if_neg hpartial]
        rw [ih]
        have hle : progression.count ≤ amount :=
          Nat.le_of_not_gt hpartial
        have hsplit :
            amount = progression.count + (amount - progression.count) := by
          omega
        rw [List.flatMap_cons, hsplit, ← List.drop_drop]
        simp [hlength]

end CLRS.Chapter34.Turing.CookLevin
