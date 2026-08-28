import CLRSLean.Research.ThreeDIC.WindowDiversity
import CLRSLean.Research.ThreeDIC.WindowRouting

/-!
# Bounded representative paths for affine repair-chain coloring

The affine coloring gives every translated target-size window a bump of any
requested repair-chain color.  The adjacent-window geometry theorem then lifts
an arbitrary path of sliding windows to a path of same-color representatives
whose squared hop length is at most {lit}`M^2 + (M - 1)^2`.

This is a bottleneck-connectivity bridge, not a complete physical routing
theorem.  It does not yet order every bump of a color class, minimize total
wire length, or encode mux and spare constraints.
-/

namespace CLRS.Research.ThreeDIC

/-- Along any adjacent path of translated windows, one can choose a bump of a
fixed affine-chain color in every window so that every consecutive squared hop
is bounded by {lit}`M^2 + (M - 1)^2`. -/
theorem affineChainColor_windowPath_bounded
    (M K c : Nat) (hK : 0 < K) (hKM : K ≤ M * M) (hc : c < K)
    {path : List (Nat × Nat)} (hpath : path.IsChain windowAdjacent) :
    ∃ rep : Nat × Nat → Nat × Nat,
      (∀ a, inWindow M a.1 a.2 (rep a) ∧
        affineChainColor M K (rep a).1 (rep a).2 = c) ∧
      (path.map rep).IsChain
        (fun x y => gridDistSq x y ≤ M ^ 2 + (M - 1) ^ 2) := by
  have hM : 0 < M := by nlinarith
  have hex : ∀ a : Nat × Nat, ∃ x : Nat × Nat,
      inWindow M a.1 a.2 x ∧ affineChainColor M K x.1 x.2 = c := by
    intro a
    obtain ⟨di, hdi, dj, hdj, hcolor⟩ :=
      affineChainColor_window_surjective M K a.1 a.2 c hK hKM hc
    refine ⟨(a.1 + di, a.2 + dj), ?_, ?_⟩
    · simp only [inWindow]
      omega
    · exact hcolor
  choose rep hrep using hex
  refine ⟨rep, hrep, ?_⟩
  exact windowPath_representatives_bounded M hM rep (fun a => (hrep a).1) hpath

end CLRS.Research.ThreeDIC
