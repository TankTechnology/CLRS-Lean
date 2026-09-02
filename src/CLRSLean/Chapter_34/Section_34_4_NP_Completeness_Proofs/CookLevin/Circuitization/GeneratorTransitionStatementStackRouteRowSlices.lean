import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackRouteCellSource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorTransitionStatementStackValueShape
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Fixed-width row slices for stack routes

Cell routes are flattened for the affine source controller but grouped into
fixed-width symbol rows by the stack semantics.  These two generic lemmas
commute `take` and `drop` with that flattening at row boundaries.
-/

namespace List

/-- The length sum of a fixed-width row prefix is the requested row count
times the common width. -/
private theorem take_map_length_sum_eq_mul
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    ((rows.map length).take count).sum = count * width := by
  rw [← List.map_take]
  have hmap :
      (rows.take count).map length =
        (rows.take count).map (fun _ => width) := by
    apply List.map_congr_left
    intro row hrow
    exact hrows row (List.mem_of_mem_take hrow)
  rw [hmap]
  simp [hcount]

/-- Taking a whole number of fixed-width rows after flattening is the same as
taking those rows before flattening. -/
theorem flatten_take_fixedWidth
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.take (count * width) = (rows.take count).flatten := by
  rw [← take_map_length_sum_eq_mul rows count width hcount hrows]
  exact List.take_sum_flatten rows count

/-- Dropping a whole number of fixed-width rows after flattening is the same
as dropping those rows before flattening. -/
theorem flatten_drop_fixedWidth
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hcount : count ≤ rows.length)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.drop (count * width) = (rows.drop count).flatten := by
  rw [← take_map_length_sum_eq_mul rows count width hcount hrows]
  exact List.drop_sum_flatten rows count

/-- Flattening fixed-width rows multiplies the row count by their width. -/
theorem flatten_length_fixedWidth
    {α : Type} (rows : List (List α)) (width : Nat)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.length = rows.length * width := by
  rw [List.length_flatten]
  have hmap :
      rows.map length = rows.map (fun _ => width) := by
    apply List.map_congr_left
    intro row hrow
    exact hrows row hrow
  rw [hmap]
  simp

/-- Removing one fixed-width row from the flattened suffix retains exactly
the preceding grouped rows. -/
theorem flatten_rdrop_one_fixedWidth
    {α : Type} (rows : List (List α)) (count width : Nat)
    (hlength : rows.length = count + 1)
    (hrows : ∀ row ∈ rows, row.length = width) :
    rows.flatten.rdrop width = (rows.take count).flatten := by
  unfold List.rdrop
  rw [flatten_length_fixedWidth rows width hrows, hlength]
  have hsub : (count + 1) * width - width = count * width := by
    simp [Nat.add_mul]
  rw [hsub]
  exact flatten_take_fixedWidth rows count width (by omega) hrows

end List

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-- Descriptor-family prefix deletion commutes with projecting the first
coordinate of every generated row. -/
theorem transitionStackRouteFirstValues_drop
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    transitionStackRouteFirstValues
        (transitionStackRouteDropFamily amount progressions) =
      (transitionStackRouteFirstValues progressions).drop amount := by
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteDropFamily_rows, List.map_drop]

/-- Descriptor-family suffix trimming commutes with projecting the first
coordinate of every generated row. -/
theorem transitionStackRouteFirstValues_trimSuffix
    (amount : Nat) (progressions : List AffineUnaryTripleProgression) :
    transitionStackRouteFirstValues
        (transitionStackRouteTrimSuffix amount progressions) =
      (transitionStackRouteFirstValues progressions).rdrop amount := by
  unfold transitionStackRouteFirstValues
  rw [transitionStackRouteTrimSuffix_rows]
  unfold List.rdrop
  rw [List.map_take, List.length_map]

end CLRS.Chapter34.Turing.CookLevin
