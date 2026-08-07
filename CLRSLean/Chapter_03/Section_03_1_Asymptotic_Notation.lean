import Mathlib

open Filter
open Asymptotics

/-!
# 3.1. Asymptotic Notation

CLRS-compatible wrappers for mathlib's filter-based asymptotics on {lit}`ℕ → ℝ`.
Proves equivalence between the CLRS discrete definition and the filter
definition, plus standard algebraic properties: the `Θ` characterization with
a single shared threshold, the `o`/`ω` and `O`/`Ω` dualities, and the
little-`o` closure properties (additivity, products, composition) used in
the growth estimates of §3.2.
-/

namespace CLRS
namespace Chapter03

/-! ## Wrapper definitions -/

def isBigO (f g : ℕ → ℝ) : Prop := f =O[atTop] g

def isBigOmega (f g : ℕ → ℝ) : Prop := g =O[atTop] f

def isBigTheta (f g : ℕ → ℝ) : Prop := isBigO f g ∧ isBigOmega f g

def isLittleO (f g : ℕ → ℝ) : Prop := f =o[atTop] g

def isLittleOmega (f g : ℕ → ℝ) : Prop := g =o[atTop] f

/-! ## Equivalence with CLRS discrete definition -/

theorem isBigO_iff (f g : ℕ → ℝ) : isBigO f g ↔
    ∃ (c : ℝ), c > 0 ∧ ∃ (n₀ : ℕ), ∀ n, n ≥ n₀ → |f n| ≤ c * |g n| := by
  unfold isBigO
  rw [IsBigO_def]
  constructor
  · rintro ⟨c, hc⟩
    rcases IsBigOWith.exists_pos hc with ⟨c', hc_pos, hc'⟩
    have hevent := (isBigOWith_iff.mp hc')
    have hevent' : ∀ᶠ n in atTop, |f n| ≤ c' * |g n| := by
      simpa [Real.norm_eq_abs] using hevent
    rw [Filter.eventually_atTop] at hevent'
    rcases hevent' with ⟨n₀, hn₀⟩
    exact ⟨c', hc_pos, n₀, hn₀⟩
  · rintro ⟨c, hc_pos, n₀, hn₀⟩
    have hevent : ∀ᶠ n in atTop, |f n| ≤ c * |g n| := by
      rw [Filter.eventually_atTop]
      exact ⟨n₀, hn₀⟩
    have hevent' : ∀ᶠ n in atTop, ‖f n‖ ≤ c * ‖g n‖ := by
      simpa [Real.norm_eq_abs] using hevent
    have hOwith : IsBigOWith c atTop f g := isBigOWith_iff.mpr hevent'
    exact ⟨c, hOwith⟩

theorem isLittleO_iff (f g : ℕ → ℝ) : isLittleO f g ↔
    ∀ (c : ℝ), c > 0 → ∃ (n₀ : ℕ), ∀ n, n ≥ n₀ → |f n| ≤ c * |g n| := by
  unfold isLittleO
  rw [isLittleO_iff_forall_isBigOWith]
  constructor
  · intro h c hc_pos
    have hOwith : IsBigOWith c atTop f g := h hc_pos
    have hevent := (isBigOWith_iff.mp hOwith)
    have hevent' : ∀ᶠ n in atTop, |f n| ≤ c * |g n| := by
      simpa [Real.norm_eq_abs] using hevent
    rw [Filter.eventually_atTop] at hevent'
    rcases hevent' with ⟨n₀, hn₀⟩
    exact ⟨n₀, hn₀⟩
  · intro h c hc_pos
    rcases h c hc_pos with ⟨n₀, hn₀⟩
    have hevent : ∀ᶠ n in atTop, |f n| ≤ c * |g n| := by
      rw [Filter.eventually_atTop]
      exact ⟨n₀, hn₀⟩
    have hevent' : ∀ᶠ n in atTop, ‖f n‖ ≤ c * ‖g n‖ := by
      simpa [Real.norm_eq_abs] using hevent
    exact isBigOWith_iff.mpr hevent'

theorem isBigOmega_iff (f g : ℕ → ℝ) : isBigOmega f g ↔
    ∃ (c : ℝ), c > 0 ∧ ∃ (n₀ : ℕ), ∀ n, n ≥ n₀ → c * |g n| ≤ |f n| := by
  -- isBigOmega f g = isBigO g f, and isBigO_iff g f gives
  --   isBigO g f ↔ ∃ c>0, n₀, ∀ n≥n₀, |g n| ≤ c * |f n|
  -- We prove this RHS is equivalent to
  --   ∃ c>0, n₀, ∀ n≥n₀, c * |g n| ≤ |f n|
  -- by exchanging c ↔ c⁻¹.
  have h_base := isBigO_iff g f
  -- isBigOmega f g = isBigO g f definitionally
  -- Now the goal is: isBigO g f ↔ ∃ c>0, n₀, ∀ n≥n₀, c * |g n| ≤ |f n|
  -- But h_base says: isBigO g f ↔ ∃ c>0, n₀, ∀ n≥n₀, |g n| ≤ c * |f n|
  -- So it suffices to show the two RHSs are equivalent.
  constructor
  · -- From isBigO g f, get ∃ c>0, n₀, ∀ n≥n₀, |g n| ≤ c * |f n|
    -- Transform to ∃ c'>0, n₀, ∀ n≥n₀, c' * |g n| ≤ |f n| via c' = c⁻¹
    intro h_isO
    rcases h_base.mp h_isO with ⟨c, hc_pos, n₀, hn₀⟩
    have hc_ne_zero : c ≠ 0 := by linarith
    refine ⟨c⁻¹, inv_pos.mpr hc_pos, n₀, λ n hn => ?_⟩
    have hineq := hn₀ n hn
    calc
      c⁻¹ * |g n| ≤ c⁻¹ * (c * |f n|) := by gcongr
      _ = (c⁻¹ * c) * |f n| := by ring
      _ = 1 * |f n| := by field_simp [hc_ne_zero]
      _ = |f n| := by simp
  · intro h_omega
    rcases h_omega with ⟨c, hc_pos, n₀, hn₀⟩
    have hc_ne_zero : c ≠ 0 := by linarith
    -- Need to show isBigO g f, i.e. ∃ c'>0, n₀, ∀ n≥n₀, |g n| ≤ c' * |f n|
    -- Using c' = c⁻¹
    apply h_base.mpr
    refine ⟨c⁻¹, inv_pos.mpr hc_pos, n₀, λ n hn => ?_⟩
    have hineq := hn₀ n hn
    calc
      |g n| = (c⁻¹ * c) * |g n| := by field_simp [hc_ne_zero]
      _ = c⁻¹ * (c * |g n|) := by ring
      _ ≤ c⁻¹ * |f n| := by gcongr

theorem isLittleOmega_iff (f g : ℕ → ℝ) : isLittleOmega f g ↔
    ∀ (c : ℝ), c > 0 → ∃ (n₀ : ℕ), ∀ n, n ≥ n₀ → c * |g n| ≤ |f n| := by
  -- isLittleOmega f g = isLittleO g f
  -- isLittleO_iff g f says: isLittleO g f ↔ ∀ c>0, ∃ n₀, |g n| ≤ c * |f n|
  -- We need to show the RHS is equivalent to ∀ c>0, c * |g n| ≤ |f n|
  -- via exchanging c ↔ c⁻¹.
  have h_base := isLittleO_iff g f
  -- isLittleOmega f g = isLittleO g f definitionally
  constructor
  · intro h_o c hc
    have hc_inv_pos : c⁻¹ > 0 := inv_pos.mpr hc
    rcases (h_base.mp h_o) c⁻¹ hc_inv_pos with ⟨n₀, hn₀⟩
    have hc_ne_zero : c ≠ 0 := by linarith
    refine ⟨n₀, λ n hn => ?_⟩
    have hineq := hn₀ n hn
    calc
      c * |g n| ≤ c * (c⁻¹ * |f n|) := by gcongr
      _ = (c * c⁻¹) * |f n| := by ring
      _ = 1 * |f n| := by field_simp [hc_ne_zero]
      _ = |f n| := by simp
  · intro h_forall
    apply h_base.mpr
    intro c' hc'_pos
    have hc_inv_pos : c'⁻¹ > 0 := inv_pos.mpr hc'_pos
    rcases h_forall c'⁻¹ hc_inv_pos with ⟨n₀, hn₀⟩
    have hc_ne_zero : c' ≠ 0 := by linarith
    refine ⟨n₀, λ n hn => ?_⟩
    have hineq := hn₀ n hn
    calc
      |g n| = c' * (c'⁻¹ * |g n|) := by field_simp [hc_ne_zero]
      _ ≤ c' * |f n| := by gcongr

/-! ## Algebraic properties -/

theorem isBigO_refl (f : ℕ → ℝ) : isBigO f f := by
  unfold isBigO
  exact Asymptotics.isBigO_refl f atTop

theorem isBigOmega_refl (f : ℕ → ℝ) : isBigOmega f f :=
  isBigO_refl f

theorem isBigTheta_refl (f : ℕ → ℝ) : isBigTheta f f :=
  ⟨isBigO_refl f, isBigOmega_refl f⟩

theorem isBigO_trans {f g h : ℕ → ℝ} (hfg : isBigO f g) (hgh : isBigO g h) : isBigO f h := by
  unfold isBigO at hfg hgh ⊢
  exact IsBigO.trans hfg hgh

theorem isBigOmega_trans {f g h : ℕ → ℝ}
    (hfg : isBigOmega f g) (hgh : isBigOmega g h) : isBigOmega f h := by
  unfold isBigOmega at hfg hgh ⊢
  exact IsBigO.trans hgh hfg

theorem isBigTheta_symm {f g : ℕ → ℝ} (h : isBigTheta f g) : isBigTheta g f :=
  ⟨h.2, h.1⟩

theorem isBigTheta_trans {f g h : ℕ → ℝ}
    (hfg : isBigTheta f g) (hgh : isBigTheta g h) : isBigTheta f h :=
  ⟨isBigO_trans hfg.1 hgh.1, isBigOmega_trans hfg.2 hgh.2⟩

theorem isBigO_add {f₁ f₂ g : ℕ → ℝ} (h₁ : isBigO f₁ g) (h₂ : isBigO f₂ g) :
    isBigO (λ n => f₁ n + f₂ n) g := by
  unfold isBigO at h₁ h₂ ⊢
  exact IsBigO.add h₁ h₂

theorem isBigTheta_iff (f g : ℕ → ℝ) : isBigTheta f g ↔ isBigO f g ∧ isBigO g f := by
  simp [isBigTheta, isBigOmega, isBigO]

/-! ## Shared threshold for Θ and dualities -/

/--
**Theorem (Θ with a shared threshold).** `f = Θ(g)` iff there exist positive
constants `c₁`, `c₂` and a single threshold `n₀` such that for all `n ≥ n₀`,
`c₁ * |g n| ≤ |f n| ≤ c₂ * |g n|`.

This is the two-sided witness characterization of Θ-notation from CLRS §3.1;
the two independent witnesses are combined by taking the maximum of their
thresholds.
-/
theorem isBigTheta_iff_sharedThreshold (f g : ℕ → ℝ) : isBigTheta f g ↔
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      c₁ * |g n| ≤ |f n| ∧ |f n| ≤ c₂ * |g n| := by
  rw [isBigTheta_iff, isBigO_iff, isBigOmega_iff]
  constructor
  · rintro ⟨hO, hΩ⟩
    rcases hO with ⟨c₂, hc₂, n₀₂, h₂⟩
    rcases hΩ with ⟨c₁, hc₁, n₀₁, h₁⟩
    refine ⟨c₁, c₂, hc₁, hc₂, max n₀₁ n₀₂, ?_⟩
    intro n hn
    exact ⟨h₁ n (le_trans (le_max_left n₀₁ n₀₂) hn),
        h₂ n (le_trans (le_max_right n₀₁ n₀₂) hn)⟩
  · rintro ⟨c₁, c₂, hc₁, hc₂, n₀, h⟩
    constructor
    · refine ⟨c₂, hc₂, n₀, ?_⟩
      intro n hn
      exact (h n hn).2
    · refine ⟨c₁, hc₁, n₀, ?_⟩
      intro n hn
      exact (h n hn).1

/--
**Lemma (duality of `o` and `ω`).** `f = o(g)` iff `g = ω(f)` (CLRS §3.1,
with the convention `isLittleOmega f g := isLittleO g f`).
-/
theorem isLittleO_reciprocal (f g : ℕ → ℝ) : isLittleO f g ↔ isLittleOmega g f := by
  simp [isLittleO, isLittleOmega]

/--
**Lemma (duality of `O` and `Ω`).** `f = O(g)` iff `g = Ω(f)` (CLRS §3.1,
with the convention `isBigOmega f g := isBigO g f`).
-/
theorem isBigO_reciprocal (f g : ℕ → ℝ) : isBigO f g ↔ isBigOmega g f := by
  simp [isBigO, isBigOmega]

/-! ## Little-o and little-omega algebra -/

/--
**Lemma.** Little-`o` implies big-`O`: if `f = o(g)` then `f = O(g)`
(CLRS §3.1).
-/
theorem isLittleO_isBigO {f g : ℕ → ℝ} : isLittleO f g → isBigO f g := by
  intro h
  unfold isLittleO isBigO at h ⊢
  exact h.isBigO

/--
**Lemma (additivity of `o`).** If `f₁ = o(g)` and `f₂ = o(g)`, then
`f₁ + f₂ = o(g)` (CLRS §3.1).
-/
theorem isLittleO_add {f₁ f₂ g : ℕ → ℝ} :
    isLittleO f₁ g → isLittleO f₂ g → isLittleO (fun n => f₁ n + f₂ n) g := by
  intro h₁ h₂
  unfold isLittleO at h₁ h₂ ⊢
  exact h₁.add h₂

/--
**Lemma (product rule).** If `f₁ = o(g₁)` and `f₂ = O(g₂)`, then
`f₁ * f₂ = o(g₁ * g₂)` (CLRS §3.1).
-/
theorem isLittleO_mul {f₁ g₁ f₂ g₂ : ℕ → ℝ} :
    isLittleO f₁ g₁ → isBigO f₂ g₂ →
      isLittleO (fun n => f₁ n * f₂ n) (fun n => g₁ n * g₂ n) := by
  intro h₁ h₂
  unfold isLittleO isBigO at h₁ h₂ ⊢
  exact h₁.mul_isBigO h₂

/--
**Lemma (composition of `o`).** If `h : ℕ → ℕ` tends to infinity and
`f = o(g)`, then `f ∘ h = o(g ∘ h)`.  This is the asymptotic analogue of
substituting `h n` for `n`, as used in the growth estimates of CLRS §3.1/§3.2.
-/
theorem isLittleO_comp {f g : ℕ → ℝ} {h : ℕ → ℕ} (hh : Tendsto h atTop atTop) :
    isLittleO f g → isLittleO (fun n => f (h n)) (fun n => g (h n)) := by
  intro hfg
  unfold isLittleO at hfg ⊢
  exact hfg.comp_tendsto hh

/--
**Lemma (scaling `ω`).** If `c > 0` and `f = ω(g)`, then `c * f = ω(g)`
(CLRS §3.1: positive constant factors are irrelevant in asymptotic notation).
-/
theorem isLittleOmega_scale {f g : ℕ → ℝ} {c : ℝ} (hc : 0 < c) :
    isLittleOmega f g → isLittleOmega (fun n => c * f n) g := by
  intro h
  unfold isLittleOmega at h ⊢
  exact h.const_mul_right (ne_of_gt hc)

/--
**Lemma (`ω` survives addition of a dominated term).** If `f = ω(g)` and
`h = O(g)`, then `f + h = ω(g)` (CLRS §3.1: adding an `O(g)` term does not
change the `ω(g)` lower bound).
-/
theorem isLittleOmega_add_dominated {f g h : ℕ → ℝ} :
    isLittleOmega f g → isBigO h g → isLittleOmega (fun n => f n + h n) g := by
  intro hfg hh
  have h_ho : isLittleO h f := by
    unfold isBigO at hh
    unfold isLittleO
    exact hh.trans_isLittleO hfg
  rw [isLittleOmega_iff] at hfg
  rw [isLittleO_iff] at h_ho
  rw [isLittleOmega_iff]
  intro c hc
  rcases hfg (2 * c) (by positivity) with ⟨n₁, hn₁⟩
  rcases h_ho (1 / 2) (by norm_num) with ⟨n₂, hn₂⟩
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn
  have hn₁' : n₁ ≤ n := le_trans (le_max_left n₁ n₂) hn
  have hn₂' : n₂ ≤ n := le_trans (le_max_right n₁ n₂) hn
  have htri : |f n| - |h n| ≤ |f n + h n| := by
    have h₁ : |f n| ≤ |f n + h n| + |h n| := by
      calc
        |f n| = |(f n + h n) + (-h n)| := by congr 1; ring
        _ ≤ |f n + h n| + |(-h n)| := abs_add_le (f n + h n) (-(h n))
        _ = |f n + h n| + |h n| := by rw [abs_neg]
    linarith
  calc
    c * |g n| = (1 / 2) * (2 * c * |g n|) := by ring
    _ ≤ (1 / 2) * |f n| := by gcongr
    _ ≤ |f n| - |h n| := by linarith
    _ ≤ |f n + h n| := htri

end Chapter03
end CLRS
