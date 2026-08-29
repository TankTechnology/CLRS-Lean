import CLRSLean.Research.ThreeDIC.WindowDiversity
import CLRSLean.Research.ThreeDIC.WindowRouting
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Int.CardIntervalMod

/-!
# Balanced per-chain load in affine repair windows

This module strengthens translated-window color coverage into a quantitative
load certificate.  The canonical index {lit}`t < M^2` names the window offset
{lit}`(t % M, t / M)`.  This enumeration is bijective, and the affine color at
that point is the residue of one of {lit}`M^2` consecutive natural numbers.

Consequently, each repair-chain color receives either
{lit}`floor(M^2 / K)` or {lit}`ceil(M^2 / K)` bumps in every translated
{lit}`M x M` window.  The result remains purely combinatorial: it does not by
itself model spare placement, mux behavior, or successful physical repair.
-/

namespace CLRS.Research.ThreeDIC

/-- Bump named by the canonical row-major index {lit}`t` in the translated
{lit}`M x M` window at {lit}`(p, q)`. -/
def windowIndexPoint (M p q t : Nat) : Nat × Nat :=
  (p + t % M, q + t / M)

/-- Every valid canonical index names a bump inside its translated window. -/
theorem windowIndexPoint_inWindow
    {M p q t : Nat} (hM : 0 < M) (ht : t < M * M) :
    inWindow M p q (windowIndexPoint M p q t) := by
  have hmod : t % M < M := Nat.mod_lt t hM
  have hdiv : t / M < M := Nat.div_lt_of_lt_mul ht
  simp only [windowIndexPoint, inWindow]
  constructor
  · omega
  constructor
  · omega
  constructor
  · exact Nat.le_add_right q (t / M)
  · exact Nat.add_lt_add_left hdiv q

/-- Distinct valid indices name distinct bumps. -/
theorem windowIndexPoint_injective
    {M p q : Nat} :
    Set.InjOn (windowIndexPoint M p q) {t | t < M * M} := by
  intro s _hs t _ht hst
  have hrem : s % M = t % M := by
    have hfst := congrArg Prod.fst hst
    simpa [windowIndexPoint] using Nat.add_left_cancel hfst
  have hquot : s / M = t / M := by
    have hsnd := congrArg Prod.snd hst
    simpa [windowIndexPoint] using Nat.add_left_cancel hsnd
  calc
    s = s % M + M * (s / M) := (Nat.mod_add_div s M).symm
    _ = t % M + M * (t / M) := by rw [hrem, hquot]
    _ = t := Nat.mod_add_div t M

/-- Every pair of offsets in the window is named by a valid canonical index. -/
theorem exists_windowIndexPoint_eq
    {M p q di dj : Nat} (hM : 0 < M) (hdi : di < M) (hdj : dj < M) :
    ∃ t < M * M, windowIndexPoint M p q t = (p + di, q + dj) := by
  refine ⟨di + M * dj, ?_, ?_⟩
  · nlinarith
  · unfold windowIndexPoint
    apply Prod.ext <;> simp [Nat.add_mul_mod_self_left, Nat.add_mul_div_left,
      Nat.mod_eq_of_lt hdi, Nat.div_eq_of_lt hdi, hM]

/-- Number of bumps of color {lit}`c` in the translated affine window, counted
through the proved canonical enumeration. -/
def windowColorCount (M K p q c : Nat) : Nat :=
  (M * M).count (fun t =>
    affineChainColor M K (windowIndexPoint M p q t).1
      (windowIndexPoint M p q t).2 = c)

/-- The affine colors in the canonical window enumeration are consecutive
modular residues. -/
theorem affineChainColor_windowIndexPoint
    (M K p q t : Nat) :
    affineChainColor M K (windowIndexPoint M p q t).1
      (windowIndexPoint M p q t).2 =
        (p + M * q + t) % K := by
  unfold affineChainColor windowIndexPoint
  congr 1
  calc
    (p + t % M) + M * (q + t / M) =
        p + M * q + (t % M + M * (t / M)) := by ring
    _ = p + M * q + t := by rw [Nat.mod_add_div]

private lemma exists_offset_add_mod_eq
    (base c K : Nat) (hK : 0 < K) (hc : c < K) :
    ∃ d < K, (base + d) % K = c := by
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

private lemma exists_offset_progression_iff
    (base c K : Nat) (hK : 0 < K) (hc : c < K) :
    ∃ d < K, ∀ t, (base + t) % K = c ↔ t ≡ d [MOD K] := by
  obtain ⟨d, hdK, hd⟩ := exists_offset_add_mod_eq base c K hK hc
  refine ⟨d, hdK, fun t => ?_⟩
  constructor
  · intro ht
    apply Nat.ModEq.add_left_cancel' base
    change (base + t) % K = (base + d) % K
    rw [ht, hd]
  · intro ht
    have hbase : base + t ≡ base + d [MOD K] := Nat.ModEq.add_left base ht
    change (base + t) % K = (base + d) % K at hbase
    rw [hbase, hd]

private lemma div_add_one_eq_ceilDiv_of_mod_pos
    (n K : Nat) (hK : 0 < K) (hrem : 0 < n % K) :
    n / K + 1 = n ⌈/⌉ K := by
  have hdecomp : n % K + K * (n / K) = n := Nat.mod_add_div n K
  apply le_antisymm
  · by_contra hnot
    have hceil_le : n ⌈/⌉ K ≤ n / K := by omega
    have hnle : n ≤ K * (n / K) :=
      (ceilDiv_le_iff_le_mul hK).mp hceil_le
    omega
  · apply (ceilDiv_le_iff_le_mul hK).2
    rw [Nat.mul_add]
    have hmod_lt : n % K < K := Nat.mod_lt n hK
    omega

/-- **Exact balanced load in every translated affine window.**

When {lit}`0 < K <= M^2`, a fixed color occurs either
{lit}`floor(M^2 / K)` or {lit}`ceil(M^2 / K)` times in every translated
{lit}`M x M` window. -/
theorem affineChainColor_window_count_eq_floor_or_ceil
    (M K p q c : Nat) (hK : 0 < K) (_hKM : K ≤ M * M) (hc : c < K) :
    windowColorCount M K p q c = (M * M) / K ∨
      windowColorCount M K p q c = (M * M) ⌈/⌉ K := by
  unfold windowColorCount
  simp_rw [affineChainColor_windowIndexPoint]
  obtain ⟨d, hdK, hpred⟩ :=
    exists_offset_progression_iff (p + M * q) c K hK hc
  have hcount :
      (M * M).count (fun t => (p + M * q + t) % K = c) =
        (M * M).count (fun t => t ≡ d [MOD K]) := by
    simp only [Nat.count_eq_card_filter_range]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    exact fun _ => hpred t
  rw [hcount]
  by_cases hrem : d < (M * M) % K
  · right
    rw [Nat.count_modEq_card (b := M * M) hK d, Nat.mod_eq_of_lt hdK,
      if_pos hrem]
    exact div_add_one_eq_ceilDiv_of_mod_pos (M * M) K hK (by omega)
  · left
    rw [Nat.count_modEq_card (b := M * M) hK d, Nat.mod_eq_of_lt hdK,
      if_neg hrem, Nat.add_zero]

/-- A box defect contained in one translated target window charges no color
more than {lit}`ceil(M^2 / K)` times. -/
theorem affineChainColor_window_load_le_ceilDiv
    (M K p q c : Nat) (hK : 0 < K) (hKM : K ≤ M * M) (hc : c < K) :
    windowColorCount M K p q c ≤ (M * M) ⌈/⌉ K := by
  rcases affineChainColor_window_count_eq_floor_or_ceil M K p q c hK hKM hc with
    hfloor | hceil
  · rw [hfloor]
    exact (floorDiv_le_ceilDiv (a := K) (b := M * M) :
      (M * M) / K ≤ (M * M) ⌈/⌉ K)
  · exact hceil.le

end CLRS.Research.ThreeDIC
