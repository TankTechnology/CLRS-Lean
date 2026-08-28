import Mathlib.Data.Nat.Dist
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Local geometry for 3D-IC repair-window routing

This module records the first geometric bridge from sliding-window diversity to
repair-chain routing.  Two representatives chosen from horizontally or
vertically adjacent {lit}`M x M` windows are separated by at most {lit}`M` grid
steps in the direction of motion and at most {lit}`M - 1` in the other direction.  Their
squared Euclidean grid distance is therefore at most

{lit}`M^2 + (M - 1)^2`.

The result is independent of the affine coloring: it applies to any coloring
that supplies a representative of a given chain in every window.  A later
connectivity theorem can lift these local edges along the connected grid of
sliding windows.
-/

namespace CLRS.Research.ThreeDIC

/-- A grid point lies in the translated {lit}`M x M` window with top-left
coordinate {lit}`(p, q)`. -/
def inWindow (M p q : Nat) (x : Nat × Nat) : Prop :=
  p ≤ x.1 ∧ x.1 < p + M ∧ q ≤ x.2 ∧ x.2 < q + M

/-- Squared Euclidean distance between two points on the integer bump grid. -/
def gridDistSq (x y : Nat × Nat) : Nat :=
  Nat.dist x.1 y.1 ^ 2 + Nat.dist x.2 y.2 ^ 2

private theorem gridDistSq_comm (x y : Nat × Nat) :
    gridDistSq x y = gridDistSq y x := by
  simp only [gridDistSq, Nat.dist_comm]

/-- Representatives of horizontally adjacent {lit}`M x M` windows have squared
grid distance at most {lit}`M^2 + (M - 1)^2`. -/
theorem gridDistSq_horizontal_adjacent_windows_le
    {M p q : Nat} {x y : Nat × Nat} (hM : 0 < M)
    (hx : inWindow M p q x) (hy : inWindow M (p + 1) q y) :
    gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2 := by
  rcases hx with ⟨hxp, hxpM, hxq, hxqM⟩
  rcases hy with ⟨hyp, hypM, hyq, hyqM⟩
  have hfirst : Nat.dist x.1 y.1 ≤ M := by
    unfold Nat.dist
    omega
  have hsecond : Nat.dist x.2 y.2 ≤ M - 1 := by
    unfold Nat.dist
    omega
  unfold gridDistSq
  nlinarith

/-- Representatives of vertically adjacent {lit}`M x M` windows have squared
grid distance at most {lit}`M^2 + (M - 1)^2`. -/
theorem gridDistSq_vertical_adjacent_windows_le
    {M p q : Nat} {x y : Nat × Nat} (hM : 0 < M)
    (hx : inWindow M p q x) (hy : inWindow M p (q + 1) y) :
    gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2 := by
  rcases hx with ⟨hxp, hxpM, hxq, hxqM⟩
  rcases hy with ⟨hyp, hypM, hyq, hyqM⟩
  have hfirst : Nat.dist x.1 y.1 ≤ M - 1 := by
    unfold Nat.dist
    omega
  have hsecond : Nat.dist x.2 y.2 ≤ M := by
    unfold Nat.dist
    omega
  unfold gridDistSq
  nlinarith

/-- Two sliding-window origins are adjacent when one is obtained from the other
by one horizontal or vertical grid step. -/
def windowAdjacent (a b : Nat × Nat) : Prop :=
  b = (a.1 + 1, a.2) ∨ a = (b.1 + 1, b.2) ∨
  b = (a.1, a.2 + 1) ∨ a = (b.1, b.2 + 1)

/-- The local squared-distance bound holds for either orientation of a
horizontal or vertical window step. -/
theorem gridDistSq_adjacent_windows_le
    {M : Nat} {a b x y : Nat × Nat} (hM : 0 < M)
    (hx : inWindow M a.1 a.2 x) (hy : inWindow M b.1 b.2 y)
    (hab : windowAdjacent a b) :
    gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2 := by
  rcases hab with hab | hab | hab | hab
  · subst b
    simpa using gridDistSq_horizontal_adjacent_windows_le hM hx hy
  · subst a
    rw [gridDistSq_comm]
    simpa using gridDistSq_horizontal_adjacent_windows_le hM hy hx
  · subst b
    simpa using gridDistSq_vertical_adjacent_windows_le hM hx hy
  · subst a
    rw [gridDistSq_comm]
    simpa using gridDistSq_vertical_adjacent_windows_le hM hy hx

/-- Choosing one representative from every window turns any adjacent-window
path into a bounded-hop path of representatives. -/
theorem windowPath_representatives_bounded
    (M : Nat) (hM : 0 < M) (rep : Nat × Nat → Nat × Nat)
    (hrep : ∀ a, inWindow M a.1 a.2 (rep a))
    {path : List (Nat × Nat)} (hpath : path.IsChain windowAdjacent) :
    (path.map rep).IsChain
      (fun x y => gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2) := by
  exact List.isChain_map_of_isChain rep
    (fun a b hab => gridDistSq_adjacent_windows_le hM (hrep a) (hrep b) hab)
    hpath

end CLRS.Research.ThreeDIC
