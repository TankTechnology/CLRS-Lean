import CLRSLean.Research.ThreeDIC.WindowRouting

/-!
# Finite-grid geometry for 3D-IC repair windows

This module closes the boundary facts needed to lift translated-window
arguments to a finite bump grid.  Every grid point receives a canonical full
window, and points in one full window satisfy the same squared hop threshold
used by adjacent-window routing.
-/

namespace CLRS.Research.ThreeDIC

/-- A bump coordinate lies inside the finite {lit}`N x N` grid. -/
def inGrid (N : Nat) (x : Nat × Nat) : Prop :=
  x.1 < N ∧ x.2 < N

/-- A translated {lit}`M x M` window is wholly contained in the finite grid. -/
def validWindowOrigin (N M : Nat) (a : Nat × Nat) : Prop :=
  a.1 + M ≤ N ∧ a.2 + M ≤ N

/-- Canonical origin of a full length-{lit}`M` interval covering coordinate
{lit}`i` inside a length-{lit}`N` axis. -/
def coverOrigin (N M i : Nat) : Nat :=
  min i (N - M)

/-- A point in a valid full window lies in the finite grid. -/
theorem inWindow_of_validWindowOrigin_inGrid
    {N M : Nat} {a x : Nat × Nat}
    (ha : validWindowOrigin N M a) (hx : inWindow M a.1 a.2 x) :
    inGrid N x := by
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hx with ⟨hx₁, hx₁M, hx₂, hx₂M⟩
  exact ⟨by omega, by omega⟩

private theorem coverOrigin_axis
    {N M i : Nat} (hM : 0 < M) (hMN : M ≤ N) (hi : i < N) :
    coverOrigin N M i ≤ i ∧ i < coverOrigin N M i + M ∧
      coverOrigin N M i + M ≤ N := by
  unfold coverOrigin
  by_cases h : i ≤ N - M
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    omega

/-- Every finite-grid point lies in the canonical full window obtained by
clamping each coordinate to the last legal origin. -/
theorem inWindow_coverOrigin
    {N M : Nat} (hM : 0 < M) (hMN : M ≤ N) {x : Nat × Nat}
    (hx : inGrid N x) :
    inWindow M (coverOrigin N M x.1) (coverOrigin N M x.2) x ∧
    validWindowOrigin N M (coverOrigin N M x.1, coverOrigin N M x.2) := by
  obtain ⟨hx₁, hx₂⟩ := hx
  obtain ⟨hlo₁, hhi₁, hvalid₁⟩ := coverOrigin_axis hM hMN hx₁
  obtain ⟨hlo₂, hhi₂, hvalid₂⟩ := coverOrigin_axis hM hMN hx₂
  exact ⟨⟨hlo₁, hhi₁, hlo₂, hhi₂⟩, ⟨hvalid₁, hvalid₂⟩⟩

/-- Two points in the same target-size window satisfy the global local-hop
threshold used by the window-representative construction. -/
theorem gridDistSq_same_window_le
    {M p q : Nat} {x y : Nat × Nat} (hM : 0 < M)
    (hx : inWindow M p q x) (hy : inWindow M p q y) :
    gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2 := by
  rcases hx with ⟨hxp, hxpM, hxq, hxqM⟩
  rcases hy with ⟨hyp, hypM, hyq, hyqM⟩
  have hfirst : Nat.dist x.1 y.1 ≤ M - 1 := by
    unfold Nat.dist
    omega
  have hsecond : Nat.dist x.2 y.2 ≤ M - 1 := by
    unfold Nat.dist
    omega
  unfold gridDistSq
  exact Nat.add_le_add
    (Nat.pow_le_pow_left (hfirst.trans (Nat.sub_le M 1)) 2)
    (Nat.pow_le_pow_left hsecond 2)

end CLRS.Research.ThreeDIC
