import Mathlib

open Filter
open Asymptotics

/-!
# 3.1. Asymptotic Notation

CLRS-compatible wrappers for mathlib's filter-based asymptotics on `ℕ → ℝ`.
Proves equivalence between the CLRS discrete definition and the filter
definition, plus standard algebraic properties.
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

end Chapter03
end CLRS
