import Mathlib.Tactic

/-!
# Affine repair-chain coloring for 3D-IC hybrid bonding

This module is a research baseline rather than part of the CLRS textbook
completion surface.  It isolates the local-diversity component of the repair
chain construction problem used by recent hybrid-bonding work.

For a target defect-window side length {lit}`M` and {lit}`K` repair chains,
color bump coordinate {lit}`(i, j)` by

{lit}`(i + M * j) % K`.

When {lit}`K ≤ M²`, every translated {lit}`M × M` window contains every chain
color.  The proof is constructive: an offset {lit}`t < K` selects the required
residue, and Euclidean division writes
{lit}`t = (t % M) + M * (t / M)` with both coordinates inside the window.

This theorem closes only the diversity objective.  Chain routing length,
finite-boundary effects, spare placement, and repairability under a concrete
fault model remain separate research questions.
-/

namespace CLRS.Research.ThreeDIC

/-- Deterministic repair-chain color assigned to bump coordinate
{lit}`(i, j)`.

The result is represented as a natural residue so the definition remains
executable without carrying a positivity proof for {lit}`K`.  The meaningful
research interface assumes {lit}`0 < K`; see {lit}`affineChainColor_lt` and
{lit}`affineChainColor_window_surjective`. -/
def affineChainColor (M K i j : Nat) : Nat :=
  (i + M * j) % K

/-- A repair-chain color is a valid residue whenever at least one chain is
available. -/
theorem affineChainColor_lt (M i j : Nat) {K : Nat} (hK : 0 < K) :
    affineChainColor M K i j < K := by
  exact Nat.mod_lt _ hK

/-- For any base value and target residue, there is an offset smaller than the
modulus that reaches the target after modular addition. -/
private lemma exists_offset_add_mod_eq (base c K : Nat) (hK : 0 < K) (hc : c < K) :
    ∃ t < K, (base + t) % K = c := by
  let b := base % K
  have hb : b < K := Nat.mod_lt base hK
  by_cases hbc : b ≤ c
  · refine ⟨c - b, by omega, ?_⟩
    rw [← Nat.mod_add_mod]
    change (b + (c - b)) % K = c
    rw [Nat.add_sub_of_le hbc, Nat.mod_eq_of_lt hc]
  · have hcb : c < b := Nat.lt_of_not_ge hbc
    refine ⟨K + c - b, by omega, ?_⟩
    rw [← Nat.mod_add_mod]
    change (b + (K + c - b)) % K = c
    rw [Nat.add_sub_of_le (by omega : b ≤ K + c)]
    simp [Nat.mod_eq_of_lt hc]

/-- **Window-surjectivity of affine repair-chain coloring.**

If {lit}`K ≤ M²`, every chain color {lit}`c < K` occurs at some coordinate in
every translated {lit}`M × M` window.  This gives a deterministic global
optimum for the local distinct-color objective: no window can contain more
than all {lit}`K`
available colors, and this construction contains all of them. -/
theorem affineChainColor_window_surjective
    (M K p q c : Nat) (hK : 0 < K) (hKM : K ≤ M * M) (hc : c < K) :
    ∃ di < M, ∃ dj < M,
      affineChainColor M K (p + di) (q + dj) = c := by
  have hM : 0 < M := by nlinarith
  obtain ⟨t, htK, htColor⟩ := exists_offset_add_mod_eq (p + M * q) c K hK hc
  have htMM : t < M * M := htK.trans_le hKM
  refine ⟨t % M, Nat.mod_lt t hM, t / M, Nat.div_lt_of_lt_mul htMM, ?_⟩
  unfold affineChainColor
  calc
    ((p + t % M) + M * (q + t / M)) % K =
        (p + M * q + (t % M + M * (t / M))) % K := by
          congr 1
          ring
    _ = (p + M * q + t) % K := by rw [Nat.mod_add_div]
    _ = c := htColor

end CLRS.Research.ThreeDIC
