import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteDropFamily
import Mathlib.Data.List.DropRight

/-!
# Prefix taking across affine progression families

Push routes retain a runtime prefix and discard the old bottom coordinates.
The retained prefix may end inside any piecewise-affine source segment, so the
normalizer carries the remaining row budget across the descriptor family.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Retain at most `amount` generated rows across a descriptor family.  A
partial final segment is shortened through the concrete count operation. -/
def transitionStackRouteTakeFamily :
    Nat → List AffineUnaryTripleProgression →
      List AffineUnaryTripleProgression
  | _, [] => []
  | amount, progression :: rest =>
      if progression.count ≤ amount then
        progression :: transitionStackRouteTakeFamily
          (amount - progression.count) rest
      else
        [transitionStackRouteSubtractCount
          (progression.count - amount) progression]

/-- The carried descriptor normalization denotes exactly taking the same
prefix from the concatenated generated row stream. -/
theorem transitionStackRouteTakeFamily_rows
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    (transitionStackRouteTakeFamily amount progressions).flatMap
        affineUnaryTripleProgressionRows =
      (progressions.flatMap affineUnaryTripleProgressionRows).take amount := by
  induction progressions generalizing amount with
  | nil => simp [transitionStackRouteTakeFamily]
  | cons progression rest ih =>
      have hlength :
          (affineUnaryTripleProgressionRows progression).length =
            progression.count := by
        rw [affineUnaryTripleProgressionRows_eq_ofFn]
        simp
      unfold transitionStackRouteTakeFamily
      by_cases hwhole : progression.count ≤ amount
      · simp only [if_pos hwhole, List.flatMap_cons]
        rw [ih]
        rw [List.take_append]
        simp [hlength, hwhole]
      · simp only [if_neg hwhole, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
        rw [transitionStackRouteSubtractCount_rows]
        have hpartial : amount < progression.count :=
          Nat.lt_of_not_ge hwhole
        rw [show progression.count -
            (progression.count - amount) = amount by omega]
        exact (List.take_append_of_le_length
          (l₁ := affineUnaryTripleProgressionRows progression)
          (l₂ := rest.flatMap affineUnaryTripleProgressionRows)
          (i := amount) (by
            simpa [hlength] using Nat.le_of_lt hpartial)).symm

/-- Total number of rows denoted by a progression family. -/
def transitionStackRouteFamilyCount
    (progressions : List AffineUnaryTripleProgression) : Nat :=
  (progressions.map AffineUnaryTripleProgression.count).sum

/-- The descriptor count sum is the exact length of its generated row stream. -/
theorem transitionStackRouteFamily_rows_length
    (progressions : List AffineUnaryTripleProgression) :
    (progressions.flatMap affineUnaryTripleProgressionRows).length =
      transitionStackRouteFamilyCount progressions := by
  induction progressions with
  | nil => rfl
  | cons progression rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        transitionStackRouteFamilyCount, List.map_cons, List.sum_cons]
      rw [affineUnaryTripleProgressionRows_eq_ofFn]
      simp [ih, transitionStackRouteFamilyCount]

/-- Remove a fixed suffix by retaining the complementary family prefix. -/
def transitionStackRouteTrimSuffix (amount : Nat)
    (progressions : List AffineUnaryTripleProgression) :
    List AffineUnaryTripleProgression :=
  transitionStackRouteTakeFamily
    (transitionStackRouteFamilyCount progressions - amount) progressions

/-- Family suffix trimming is exactly `List.rdrop` on generated rows. -/
theorem transitionStackRouteTrimSuffix_rows
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    (transitionStackRouteTrimSuffix amount progressions).flatMap
        affineUnaryTripleProgressionRows =
      (progressions.flatMap affineUnaryTripleProgressionRows).rdrop amount := by
  unfold transitionStackRouteTrimSuffix
  rw [transitionStackRouteTakeFamily_rows]
  unfold List.rdrop
  rw [transitionStackRouteFamily_rows_length]

end CLRS.Chapter34.Turing.CookLevin
