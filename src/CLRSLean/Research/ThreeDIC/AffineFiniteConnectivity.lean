import CLRSLean.Research.ThreeDIC.AffineWindowRouting
import CLRSLean.Research.ThreeDIC.WindowOriginPath

/-!
# Finite-grid connectivity of affine repair-chain colors

This module closes the finite-boundary connectivity theorem.  Any two bumps of
the same affine repair-chain color inside an {lit}`N x N` grid are joined by a
finite same-color path.  Every hop satisfies the squared distance threshold
{lit}`M^2 + (M - 1)^2`.

The path is a connectivity witness and may repeat vertices.  No Hamiltonian or
total-wire-length claim is made here.
-/

namespace CLRS.Research.ThreeDIC

/-- Bundled contract for an endpoint-exact, finite-grid, same-color,
bounded-hop path. -/
structure BoundedColorPath
    (N M K c : Nat) (x y : Nat × Nat) where
  points : List (Nat × Nat)
  head?_eq : points.head? = some x
  getLast?_eq : points.getLast? = some y
  mem_inGrid : ∀ z ∈ points, inGrid N z
  mem_color : ∀ z ∈ points, affineChainColor M K z.1 z.2 = c
  isChain : points.IsChain
    (fun u v => gridDistSq u v ≤ M ^ 2 + (M - 1) ^ 2)

/-- **Finite-grid affine-chain connectivity.**

When {lit}`0 < K <= M^2` and {lit}`M <= N`, any two finite-grid bumps of color
{lit}`c` have an endpoint-exact same-color path whose every squared hop is at
most {lit}`M^2 + (M - 1)^2`. -/
theorem affineChainColor_finiteGrid_connected
    (N M K c : Nat) (hK : 0 < K) (hKM : K ≤ M * M) (hMN : M ≤ N)
    {x y : Nat × Nat} (hx : inGrid N x) (hy : inGrid N y)
    (hxc : affineChainColor M K x.1 x.2 = c)
    (hyc : affineChainColor M K y.1 y.2 = c) :
    Nonempty (BoundedColorPath N M K c x y) := by
  have hM : 0 < M := by nlinarith
  have hc : c < K := by
    rw [← hxc]
    exact affineChainColor_lt M x.1 x.2 hK
  let ax : Nat × Nat := (coverOrigin N M x.1, coverOrigin N M x.2)
  let ay : Nat × Nat := (coverOrigin N M y.1, coverOrigin N M y.2)
  have hxCover : inWindow M ax.1 ax.2 x ∧ validWindowOrigin N M ax := by
    simpa [ax] using inWindow_coverOrigin hM hMN hx
  have hyCover : inWindow M ay.1 ay.2 y ∧ validWindowOrigin N M ay := by
    simpa [ay] using inWindow_coverOrigin hM hMN hy
  let windows := windowOriginPath ax ay
  have hWindowsChain : windows.IsChain windowAdjacent := by
    simpa [windows] using windowOriginPath_isChain ax ay
  obtain ⟨rep, hrep, hRepChain⟩ :=
    affineChainColor_windowPath_bounded M K c hK hKM hc hWindowsChain
  let reps := windows.map rep
  have hRepChain' : reps.IsChain
      (fun u v => gridDistSq u v ≤ M ^ 2 + (M - 1) ^ 2) := by
    simpa [reps] using hRepChain
  have hRepsHead : reps.head? = some (rep ax) := by
    simp [reps, windows, windowOriginPath_head?]
  have hRepsLast : reps.getLast? = some (rep ay) := by
    simp [reps, windows, windowOriginPath_getLast?]
  have hRepsNe : reps ≠ [] := by
    intro hreps
    rw [hreps] at hRepsHead
    simp at hRepsHead
  have hStart : (x :: reps).IsChain
      (fun u v => gridDistSq u v ≤ M ^ 2 + (M - 1) ^ 2) := by
    apply hRepChain'.cons
    intro z hz
    rw [hRepsHead] at hz
    simp only [Option.mem_some_iff] at hz
    subst z
    exact gridDistSq_same_window_le hM hxCover.1 (hrep ax).1
  have hFull : ((x :: reps) ++ [y]).IsChain
      (fun u v => gridDistSq u v ≤ M ^ 2 + (M - 1) ^ 2) := by
    apply hStart.append (List.IsChain.singleton y)
    intro z hz w hw
    simp only [List.head?_singleton, Option.mem_some_iff] at hw
    subst w
    rw [List.getLast?_cons_of_ne_nil hRepsNe, hRepsLast] at hz
    simp only [Option.mem_some_iff] at hz
    subst z
    exact gridDistSq_same_window_le hM (hrep ay).1 hyCover.1
  refine ⟨{
    points := (x :: reps) ++ [y]
    head?_eq := by simp
    getLast?_eq := by
      rw [List.getLast?_append]
      simp
    mem_inGrid := ?_
    mem_color := ?_
    isChain := hFull
  }⟩
  · intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (rfl | hz) | rfl
    · exact hx
    · rw [show reps = windows.map rep by rfl, List.mem_map] at hz
      obtain ⟨a, ha, rfl⟩ := hz
      exact inWindow_of_validWindowOrigin_inGrid
        (windowOriginPath_mem_valid hxCover.2 hyCover.2 (by simpa [windows] using ha))
        (hrep a).1
    · exact hy
  · intro z hz
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with (rfl | hz) | rfl
    · exact hxc
    · rw [show reps = windows.map rep by rfl, List.mem_map] at hz
      obtain ⟨a, _, rfl⟩ := hz
      exact (hrep a).2
    · exact hyc

end CLRS.Research.ThreeDIC
