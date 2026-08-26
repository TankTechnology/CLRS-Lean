import CLRSLean.FourthEdition.Chapter_03.Section_03_1_Asymptotic_Notation.Core

open Filter
open Asymptotics

/-!
# CLRS-facing bridges for asymptotic notation

The core relations use norms, as Mathlib does, so that they remain meaningful
for signed functions.  CLRS prints inequalities without absolute values and
silently works with eventually nonnegative running-time functions.  The first
five theorems make that representation boundary exact.  The strict little-o
and little-omega forms additionally require the comparison side to be
eventually positive; without that assumption a strict inequality can fail at
infinitely many common zeros even though the norm-based little-o relation
holds.
-/

namespace CLRS
namespace Chapter03

/-- CLRS's nonnegative witness form of big-O. -/
theorem isBigO_iff_clrs {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    isBigO f g ↔
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        0 ≤ f n ∧ f n ≤ c * g n := by
  rw [Filter.eventually_atTop] at hf hg
  rcases hf with ⟨nf, hf⟩
  rcases hg with ⟨ng, hg⟩
  constructor
  · intro h
    rcases (isBigO_iff f g).mp h with ⟨c, hc, n₀, hn₀⟩
    refine ⟨c, hc, max n₀ (max nf ng), ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_left nf ng) (le_trans (le_max_right n₀ _) hn)
    have hng : ng ≤ n := le_trans (le_max_right nf ng) (le_trans (le_max_right n₀ _) hn)
    have hf0 := hf n hnf
    have hg0 := hg n hng
    simpa [abs_of_nonneg hf0, abs_of_nonneg hg0] using
      And.intro hf0 (hn₀ n hn₀')
  · rintro ⟨c, hc, n₀, hn₀⟩
    apply (isBigO_iff f g).mpr
    refine ⟨c, hc, max n₀ ng, ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hng : ng ≤ n := le_trans (le_max_right _ _) hn
    have hfg := hn₀ n hn₀'
    simpa [abs_of_nonneg hfg.1, abs_of_nonneg (hg n hng)] using hfg.2

/-- CLRS's nonnegative witness form of big-Omega. -/
theorem isBigOmega_iff_clrs {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    isBigOmega f g ↔
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        0 ≤ g n ∧ c * g n ≤ f n := by
  rw [Filter.eventually_atTop] at hf hg
  rcases hf with ⟨nf, hf⟩
  rcases hg with ⟨ng, hg⟩
  constructor
  · intro h
    rcases (isBigOmega_iff f g).mp h with ⟨c, hc, n₀, hn₀⟩
    refine ⟨c, hc, max n₀ (max nf ng), ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_left nf ng) (le_trans (le_max_right n₀ _) hn)
    have hng : ng ≤ n := le_trans (le_max_right nf ng) (le_trans (le_max_right n₀ _) hn)
    have hf0 := hf n hnf
    have hg0 := hg n hng
    simpa [abs_of_nonneg hf0, abs_of_nonneg hg0] using
      And.intro hg0 (hn₀ n hn₀')
  · rintro ⟨c, hc, n₀, hn₀⟩
    apply (isBigOmega_iff f g).mpr
    refine ⟨c, hc, max n₀ nf, ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_right _ _) hn
    have hfg := hn₀ n hn₀'
    simpa [abs_of_nonneg (hf n hnf), abs_of_nonneg hfg.1] using hfg.2

/-- CLRS's two-sided nonnegative definition of Theta. -/
theorem isBigTheta_iff_clrs {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    isBigTheta f g ↔
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        0 ≤ f n ∧ 0 ≤ g n ∧ c₁ * g n ≤ f n ∧ f n ≤ c₂ * g n := by
  rw [Filter.eventually_atTop] at hf hg
  rcases hf with ⟨nf, hf⟩
  rcases hg with ⟨ng, hg⟩
  constructor
  · intro h
    rcases (isBigTheta_iff_sharedThreshold f g).mp h with
      ⟨c₁, c₂, hc₁, hc₂, n₀, hn₀⟩
    refine ⟨c₁, c₂, hc₁, hc₂, max n₀ (max nf ng), ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_left nf ng) (le_trans (le_max_right n₀ _) hn)
    have hng : ng ≤ n := le_trans (le_max_right nf ng) (le_trans (le_max_right n₀ _) hn)
    have hf0 := hf n hnf
    have hg0 := hg n hng
    have hb := hn₀ n hn₀'
    simpa [abs_of_nonneg hf0, abs_of_nonneg hg0] using
      And.intro hf0 (And.intro hg0 hb)
  · rintro ⟨c₁, c₂, hc₁, hc₂, n₀, hn₀⟩
    apply (isBigTheta_iff_sharedThreshold f g).mpr
    refine ⟨c₁, c₂, hc₁, hc₂, n₀, ?_⟩
    intro n hn
    have hb := hn₀ n hn
    simpa [abs_of_nonneg hb.1, abs_of_nonneg hb.2.1] using hb.2.2

/-- CLRS's strict, eventually nonnegative definition of little-o. -/
theorem isLittleO_iff_clrs_strict {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 < g n) :
    isLittleO f g ↔
      ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        0 ≤ f n ∧ f n < c * g n := by
  rw [Filter.eventually_atTop] at hf hg
  rcases hf with ⟨nf, hf⟩
  rcases hg with ⟨ng, hg⟩
  constructor
  · intro h c hc
    rcases (isLittleO_iff f g).mp h (c / 2) (by positivity) with ⟨n₀, hn₀⟩
    refine ⟨max n₀ (max nf ng), ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_left nf ng) (le_trans (le_max_right n₀ _) hn)
    have hng : ng ≤ n := le_trans (le_max_right nf ng) (le_trans (le_max_right n₀ _) hn)
    have hf0 := hf n hnf
    have hg0 := hg n hng
    have hb := hn₀ n hn₀'
    rw [abs_of_nonneg hf0, abs_of_pos hg0] at hb
    constructor
    · exact hf0
    · nlinarith [mul_pos hc hg0]
  · intro h
    apply (isLittleO_iff f g).mpr
    intro c hc
    rcases h c hc with ⟨n₀, hn₀⟩
    refine ⟨max n₀ ng, ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hng : ng ≤ n := le_trans (le_max_right _ _) hn
    have hb := hn₀ n hn₀'
    simpa [abs_of_nonneg hb.1, abs_of_pos (hg n hng)] using hb.2.le

/-- CLRS's strict, eventually nonnegative definition of little-omega. -/
theorem isLittleOmega_iff_clrs_strict {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 < f n) (hg : ∀ᶠ n in atTop, 0 ≤ g n) :
    isLittleOmega f g ↔
      ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        0 ≤ g n ∧ c * g n < f n := by
  rw [Filter.eventually_atTop] at hf hg
  rcases hf with ⟨nf, hf⟩
  rcases hg with ⟨ng, hg⟩
  constructor
  · intro h c hc
    rcases (isLittleOmega_iff f g).mp h (2 * c) (by positivity) with ⟨n₀, hn₀⟩
    refine ⟨max n₀ (max nf ng), ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_left nf ng) (le_trans (le_max_right n₀ _) hn)
    have hng : ng ≤ n := le_trans (le_max_right nf ng) (le_trans (le_max_right n₀ _) hn)
    have hf0 := hf n hnf
    have hg0 := hg n hng
    have hb := hn₀ n hn₀'
    rw [abs_of_pos hf0, abs_of_nonneg hg0] at hb
    constructor
    · exact hg0
    · nlinarith [mul_nonneg hc.le hg0]
  · intro h
    apply (isLittleOmega_iff f g).mpr
    intro c hc
    rcases h c hc with ⟨n₀, hn₀⟩
    refine ⟨max n₀ nf, ?_⟩
    intro n hn
    have hn₀' : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have hnf : nf ≤ n := le_trans (le_max_right _ _) hn
    have hb := hn₀ n hn₀'
    simpa [abs_of_pos (hf n hnf), abs_of_nonneg hb.1] using hb.2.le

/-- Little-o is transitive. -/
theorem isLittleO_trans {f g h : ℕ → ℝ}
    (hfg : isLittleO f g) (hgh : isLittleO g h) : isLittleO f h := by
  unfold isLittleO at hfg hgh ⊢
  exact hfg.trans hgh

/-- Little-omega is transitive. -/
theorem isLittleOmega_trans {f g h : ℕ → ℝ}
    (hfg : isLittleOmega f g) (hgh : isLittleOmega g h) : isLittleOmega f h := by
  unfold isLittleOmega at hfg hgh ⊢
  exact hgh.trans hfg

/-! ## Real-domain variants

CLRS permits the independent variable to range over either naturals or reals.
The discrete wrappers remain the default elsewhere in this repository; these
definitions expose the corresponding real-at-infinity interface without
duplicating Mathlib's mature witness theory.
-/

def isBigOReal (f g : ℝ → ℝ) : Prop := f =O[atTop] g

def isBigOmegaReal (f g : ℝ → ℝ) : Prop := g =O[atTop] f

def isBigThetaReal (f g : ℝ → ℝ) : Prop := isBigOReal f g ∧ isBigOmegaReal f g

def isLittleOReal (f g : ℝ → ℝ) : Prop := f =o[atTop] g

def isLittleOmegaReal (f g : ℝ → ℝ) : Prop := g =o[atTop] f

theorem isLittleOReal_trans {f g h : ℝ → ℝ}
    (hfg : isLittleOReal f g) (hgh : isLittleOReal g h) : isLittleOReal f h := by
  unfold isLittleOReal at hfg hgh ⊢
  exact hfg.trans hgh

theorem isLittleOmegaReal_trans {f g h : ℝ → ℝ}
    (hfg : isLittleOmegaReal f g) (hgh : isLittleOmegaReal g h) :
    isLittleOmegaReal f h := by
  unfold isLittleOmegaReal at hfg hgh ⊢
  exact hgh.trans hfg

end Chapter03
end CLRS
