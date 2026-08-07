import Mathlib

/-!
# S1. Preference model

The combinatorial model of the stable-marriage problem of CLRS §25.2: a
preference profile assigns every man a strict total order over the women and
every woman a strict total order over the men, represented by distinct
numeric ranks; a pairing records who is matched to whom; and stability is the
absence of blocking pairs.

Main results:

- `PreferenceProfile`: men's and women's rank functions (with distinct ranks)
- `PreferenceProfile.mPrefers` / `PreferenceProfile.wPrefers`: strict
  preference relations derived from the ranks
- `Pairing`: a consistent pair of partner functions (CLRS §25.2)
- `Pairing.IsPerfect`: every man and every woman is matched
- `BlockingPair`: a pair that would rather be together than with its current
  partners (CLRS eq. (25.9))
- `Stable`: a pairing with no blocking pair (CLRS eq. (25.10))
-/
namespace CLRS

namespace Matchings

/--
A **preference profile** for the stable-marriage problem (CLRS §25.2): each
man `m` ranks every woman by `mRank m` and each woman `w` ranks every man by
`wRank w`, where smaller ranks mean higher preference.  The rank functions
are injective in the opposite argument, so every agent's preferences form a
strict total order.
-/
structure PreferenceProfile (M W : Type*) [Fintype M] [DecidableEq M]
    [Fintype W] [DecidableEq W] where
  /-- The rank man `m` assigns to woman `w`: smaller is better. -/
  mRank : M → W → ℕ
  /-- The rank woman `w` assigns to man `m`: smaller is better. -/
  wRank : W → M → ℕ
  /-- Every man ranks distinct women distinctly. -/
  h_mRank_injective : ∀ m : M, Function.Injective (mRank m)
  /-- Every woman ranks distinct men distinctly. -/
  h_wRank_injective : ∀ w : W, Function.Injective (wRank w)

/-- Man `m` prefers woman `w₁` to woman `w₂`. -/
def PreferenceProfile.mPrefers {M W : Type*} [Fintype M] [DecidableEq M]
    [Fintype W] [DecidableEq W] (P : PreferenceProfile M W) (m : M) (w₁ w₂ : W) : Prop :=
  P.mRank m w₁ < P.mRank m w₂

/-- Woman `w` prefers man `m₁` to man `m₂`. -/
def PreferenceProfile.wPrefers {M W : Type*} [Fintype M] [DecidableEq M]
    [Fintype W] [DecidableEq W] (P : PreferenceProfile M W) (w : W) (m₁ m₂ : M) : Prop :=
  P.wRank w m₁ < P.wRank w m₂

/--
A **pairing** of men and women (CLRS §25.2): `mPartner m` is the woman man
`m` is matched to (if any) and `wPartner w` is the man woman `w` is matched
to (if any), and the two sides agree: man `m` is matched to woman `w` if and
only if woman `w` is matched to man `m`.
-/
structure Pairing (M W : Type*) where
  /-- The woman each man is matched to, if any. -/
  mPartner : M → Option W
  /-- The man each woman is matched to, if any. -/
  wPartner : W → Option M
  /-- Mutual consistency: `m` is matched to `w` iff `w` is matched to `m`. -/
  h_consistency : ∀ m w, mPartner m = some w ↔ wPartner w = some m

namespace Pairing

/--
A pairing is **perfect** when every man and every woman is matched (CLRS
§25.2).
-/
def IsPerfect {M W : Type*} (μ : Pairing M W) : Prop :=
  (∀ m, ∃ w, μ.mPartner m = some w) ∧ (∀ w, ∃ m, μ.wPartner w = some m)

/--
`(m, w)` is a **blocking pair** for the pairing `μ` when `m` and `w` are not
matched to each other and each of them either is unmatched or strictly
prefers the other to its current partner (CLRS eq. (25.9)).
-/
def BlockingPair {M W : Type*} [Fintype M] [DecidableEq M] [Fintype W] [DecidableEq W]
    (P : PreferenceProfile M W) (μ : Pairing M W) (m : M) (w : W) : Prop :=
  (μ.wPartner w = none ∨ ∃ m', μ.wPartner w = some m' ∧ P.wPrefers w m m') ∧
    (μ.mPartner m = none ∨ ∃ w', μ.mPartner m = some w' ∧ P.mPrefers m w w')

/--
A pairing is **stable** when it has no blocking pair (CLRS eq. (25.10)).
-/
def Stable {M W : Type*} [Fintype M] [DecidableEq M] [Fintype W] [DecidableEq W]
    (P : PreferenceProfile M W) (μ : Pairing M W) : Prop :=
  ∀ m w, ¬ BlockingPair P μ m w

end Pairing

end Matchings

end CLRS
