import Mathlib

/-!
# 35.3 The Set-Covering Problem

This section formalizes the set-covering problem and the harmonic
approximation guarantee of the greedy algorithm **GREEDY-SET-COVER** from CLRS
§35.3.  Given a finite universe `X` and a family `F` of subsets of `X` whose
union is `X`, a *set cover* is a subfamily `C ⊆ F` whose union is `X`, and the
problem is to find a set cover of minimum cardinality.  Computing an optimal
cover is NP-hard, but GREEDY-SET-COVER — which repeatedly picks the set of `F`
covering the most still-uncovered elements and removes the elements it covers —
always finds a cover within a factor `H(d)` of the optimum, where `d` bounds
the sizes of the sets in `F` and `H` is the harmonic number (Theorem 35.3).

Main results:

- Definition `Covers`: a family of sets covering a universe.
- Definition `pickSet`: the greedy pick — a set of `F` covering at least as
  many uncovered elements as any other.
- Definition `greedySetCover`: the family of sets returned by GREEDY-SET-COVER.
- Definition `greedyCost`: the number of sets GREEDY-SET-COVER picks.
- Theorem `greedySetCover_covers` (Theorem 35.3, correctness): the returned
  family covers its universe.
- Theorem `greedySetCover_subset`: the returned family is drawn from `F`.
- Theorem `greedySetCover_approx` (Theorem 35.3): for every cover `C` of `X`,
  `greedyCost ≤ H(d) · |C|` — in particular, `C` may be an optimal cover.
- Theorem `greedySetCover_ln_approx` (Theorem 35.4): for every cover `C` of
  `X`, `greedyCost ≤ |C| · (⌈ln |X|⌉ + 1)` — GREEDY-SET-COVER is an
  `O(lg |X|)`-approximation algorithm.

The approximation proof is the CLRS charging argument.  Each greedy step charges
`1 / |new|` to every element covered at that step, where `new` is the set of
elements the greedy pick covers (`chargeSum`).  The total charge is exactly the
cost, and — because the greedy pick covers at least as many uncovered elements
as any set of `F` — the charge accrued by the elements of any fixed set `S` is
at most `H(|S|)` (Lemma `chargeSum_le_harmonic`).  Summing these bounds over a
cover `C` and using `|S| ≤ d` gives the `H(d)`-approximation (Theorem 35.3).

Theorem 35.4's logarithmic bound uses a different argument: a size-`k` cover of
the current uncovered set `U` forces the greedy pick to cover at least `|U| / k`
elements, so the uncovered set shrinks by the factor `(1 - 1/k)` each step
(`pickSet_sdiff_shrink`).  Iterating, after `k · ⌈ln |X|⌉` steps the uncovered
set has size below `1` (`greedyCost_le_fuel` with `1 - 1/k ≤ e^{-1/k}`), giving
`greedyCost ≤ |C| · (⌈ln |X|⌉ + 1)`.

Notation conventions used in this section:

- `X` : the universe
- `F` : the family of subsets available to the greedy algorithm
- `U` : the current set of still-uncovered elements
- `A` : a set of elements whose charge is accumulated
- `C` : a candidate set cover (a subfamily of `F`)
- `d` : a bound on the sizes of the sets in `F`
- `H(n)` : the `n`-th harmonic number `harmonic n`
-/

noncomputable section

open Finset
open scoped BigOperators

namespace CLRS

namespace SetCover

variable {α : Type} [DecidableEq α]

/-- A family `C` of sets **covers** `X` when every element of `X` lies in some
set of `C`.  This is the set-cover feasibility condition of CLRS §35.3. -/
def Covers (X : Finset α) (C : Finset (Finset α)) : Prop :=
  ∀ x ∈ X, ∃ S ∈ C, x ∈ S

/-- Some set of `F` maximizes the number of uncovered elements it covers. -/
lemma exists_max_coverage (F : Finset (Finset α)) (U : Finset α) (hF : F.Nonempty) :
    ∃ S ∈ F, ∀ T ∈ F, (T ∩ U).card ≤ (S ∩ U).card := by
  classical
  obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image F (fun S : Finset α => (S ∩ U).card) hF
  exact ⟨S, hS, by intro T hT; exact hmax T hT⟩

/--
The **greedy pick**: a set of `F` covering as many uncovered elements as any
other set of `F` (CLRS §35.3, GREEDY-SET-COVER).
-/
noncomputable def pickSet (F : Finset (Finset α)) (U : Finset α) (hF : F.Nonempty) : Finset α :=
  Classical.choose (exists_max_coverage F U hF)

/-- The greedy pick is a member of the family `F`. -/
lemma pickSet_mem (F : Finset (Finset α)) (U : Finset α) (hF : F.Nonempty) :
    pickSet F U hF ∈ F :=
  (Classical.choose_spec (exists_max_coverage F U hF)).1

/-- The greedy pick covers at least as many uncovered elements as any set of
`F`. -/
lemma pickSet_coverage_le (F : Finset (Finset α)) (U : Finset α) (hF : F.Nonempty) {T : Finset α}
    (hT : T ∈ F) :
    (T ∩ U).card ≤ (pickSet F U hF ∩ U).card :=
  (Classical.choose_spec (exists_max_coverage F U hF)).2 T hT

/-- A covering family of a nonempty universe is itself nonempty. -/
lemma cover_nonempty (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) (hU : U.Nonempty) :
    F.Nonempty := by
  rcases hU with ⟨x, hx⟩
  rcases hcov x hx with ⟨S, hS, _⟩
  exact ⟨S, hS⟩

/-- The covering property is inherited by subsets of the universe. -/
lemma cover_sub (F : Finset (Finset α)) {U U' : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) (hU' : U' ⊆ U) :
    ∀ x ∈ U', ∃ S ∈ F, x ∈ S := by
  intro x hx
  exact hcov x (hU' hx)

/-- The greedy pick of a covered nonempty universe covers at least one uncovered
element, so the uncovered set strictly shrinks. -/
lemma pickSet_sdiff_card_lt (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) (hU : U.Nonempty) :
    (U \ pickSet F U (cover_nonempty F hcov hU)).card < U.card := by
  classical
  let x := hU.choose
  have hxU : x ∈ U := hU.choose_spec
  rcases hcov x hxU with ⟨S, hS, hxS⟩
  have hmem : x ∈ S ∩ U := Finset.mem_inter.mpr ⟨hxS, hxU⟩
  have hScover : 1 ≤ (S ∩ U).card := by
    have hpos : 0 < (S ∩ U).card := Finset.card_pos.mpr ⟨x, hmem⟩
    omega
  have hpick : 1 ≤ (pickSet F U (cover_nonempty F hcov hU) ∩ U).card :=
    le_trans hScover (pickSet_coverage_le F U (cover_nonempty F hcov hU) hS)
  have hUcard : 1 ≤ U.card := by
    have hpos : 0 < U.card := Finset.card_pos.mpr ⟨x, hxU⟩
    omega
  rw [Finset.card_sdiff]
  omega

/-- The harmonic number `harmonic` is monotone in its argument. -/
lemma harmonic_mono {a b : ℕ} (h : a ≤ b) : harmonic a ≤ harmonic b := by
  induction' h with b hb ih
  · rfl
  · calc
      harmonic a ≤ harmonic b := ih
      _ ≤ harmonic (b + 1) := by
        rw [harmonic_succ]
        exact le_add_of_nonneg_right (by positivity)

/-- The harmonic number `harmonic` is nonnegative. -/
lemma harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [harmonic_succ]
      exact add_nonneg ih (by positivity)

/-- The difference of harmonic numbers is the sum of reciprocals over the
half-open interval `[a, b)`. -/
lemma harmonic_sub {a b : ℕ} (h : a ≤ b) :
    harmonic b - harmonic a = ∑ i ∈ Finset.Ico a b, (↑(i + 1 : ℕ) : ℚ)⁻¹ := by
  rw [harmonic, harmonic]
  exact (Finset.sum_Ico_eq_sub (fun i : ℕ => (↑(i + 1 : ℕ) : ℚ)⁻¹) h).symm

/-- The core harmonic charge bound: if `a ≤ n ≤ m` with `n > 0`, then the number
`(n - a)` of interval points contributes at most `H(n) - H(a)`. -/
lemma harm_bound (a n m : ℕ) (ha : a ≤ n) (hn : 0 < n) (hnm : n ≤ m) :
    (((n - a : ℕ) : ℚ) / (m : ℚ)) ≤ harmonic n - harmonic a := by
  have hIco : harmonic n - harmonic a = ∑ i ∈ Finset.Ico a n, (↑(i + 1 : ℕ) : ℚ)⁻¹ :=
    harmonic_sub ha
  have hterm : (∑ i ∈ Finset.Ico a n, (↑(n : ℚ))⁻¹) ≤ ∑ i ∈ Finset.Ico a n, (↑(i + 1 : ℕ) : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    rcases Finset.mem_Ico.mp hi with ⟨hai, hin⟩
    have hle : (i + 1 : ℕ) ≤ n := by omega
    have hip : (0 : ℚ) < ((i + 1 : ℕ) : ℚ) := by positivity
    simpa using one_div_le_one_div_of_le (b := (n : ℚ)) hip (by exact_mod_cast hle)
  have hconst : (∑ i ∈ Finset.Ico a n, (↑(n : ℚ))⁻¹) = ((n - a : ℕ) : ℚ) * (↑(n : ℚ))⁻¹ := by
    rw [Finset.sum_const, Nat.card_Ico a n]
    norm_num
  have hnm' : ((n - a : ℕ) : ℚ) * (↑(m : ℚ))⁻¹ ≤ ((n - a : ℕ) : ℚ) * (↑(n : ℚ))⁻¹ := by
    have hmn : (0 : ℚ) < (m : ℚ) := by exact_mod_cast (lt_of_lt_of_le hn hnm)
    have hnp : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
    have hle : (↑(m : ℚ))⁻¹ ≤ (↑(n : ℚ))⁻¹ := (inv_le_inv₀ hmn hnp).mpr (by exact_mod_cast hnm)
    exact mul_le_mul_of_nonneg_left hle (by positivity)
  calc
    ((n - a : ℕ) : ℚ) / (m : ℚ) = ((n - a : ℕ) : ℚ) * (↑(m : ℚ))⁻¹ := by ring
    _ ≤ ((n - a : ℕ) : ℚ) * (↑(n : ℚ))⁻¹ := hnm'
    _ = ∑ i ∈ Finset.Ico a n, (↑(n : ℚ))⁻¹ := hconst.symm
    _ ≤ ∑ i ∈ Finset.Ico a n, (↑(i + 1 : ℕ) : ℚ)⁻¹ := hterm
    _ = harmonic n - harmonic a := hIco.symm

/--
The **cost** of GREEDY-SET-COVER on the uncovered set `U`: the number of sets
the greedy algorithm picks until `U` is exhausted.  Each step picks a set of
`F` covering as many uncovered elements as any other (`pickSet`) and removes
the elements it covers.  The covering hypothesis `hcov` guarantees the uncovered
set strictly shrinks, so the loop terminates (CLRS §35.3, GREEDY-SET-COVER).
-/
noncomputable def greedyCost (F : Finset (Finset α)) : (U : Finset α) → (∀ x ∈ U, ∃ S ∈ F, x ∈ S) → ℚ
  | U, hcov =>
      if hU : U = ∅ then 0
      else
        let hF : F.Nonempty := cover_nonempty F hcov (Finset.nonempty_iff_ne_empty.mpr hU)
        let S := pickSet F U hF
        (1 : ℚ) + greedyCost F (U \ S) (cover_sub F hcov (Finset.sdiff_subset (s := U) (t := S)))
termination_by U => U.card
decreasing_by
  classical
  exact pickSet_sdiff_card_lt F hcov (Finset.nonempty_iff_ne_empty.mpr hU)

/--
The **charge** accrued by the elements of `A` while the greedy algorithm runs
on the uncovered set `U`: each step of coverage charges `1 / |new|` to every
element of `A` covered at that step, where `new` is the set of newly covered
elements.  This is the internal quantity behind Theorem 35.3's charging
argument: `greedyCost F U hcov` equals `chargeSum F U hcov U`.
-/
noncomputable def chargeSum (F : Finset (Finset α)) :
    (U : Finset α) → (∀ x ∈ U, ∃ S ∈ F, x ∈ S) → (A : Finset α) → ℚ
  | U, hcov, A =>
      if hU : U = ∅ then 0
      else
        let hF : F.Nonempty := cover_nonempty F hcov (Finset.nonempty_iff_ne_empty.mpr hU)
        let S := pickSet F U hF
        ((A ∩ S).card : ℚ) * ((S ∩ U).card : ℚ)⁻¹
          + chargeSum F (U \ S) (cover_sub F hcov (Finset.sdiff_subset (s := U) (t := S))) (A \ S)
termination_by U => U.card
decreasing_by
  classical
  exact pickSet_sdiff_card_lt F hcov (Finset.nonempty_iff_ne_empty.mpr hU)

/-- The greedy pick of a covered nonempty universe covers at least one uncovered
element. -/
lemma pickSet_covers_nonempty (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) (hU : U.Nonempty) :
    (pickSet F U (cover_nonempty F hcov hU) ∩ U).Nonempty := by
  classical
  let x := hU.choose
  have hxU : x ∈ U := hU.choose_spec
  rcases hcov x hxU with ⟨S, hS, hxS⟩
  have hScover : 1 ≤ (S ∩ U).card := by
    have hpos : 0 < (S ∩ U).card := Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxS, hxU⟩⟩
    omega
  exact Finset.card_pos.mp (le_trans hScover (pickSet_coverage_le F U (cover_nonempty F hcov hU) hS))

/--
The family of sets **returned by GREEDY-SET-COVER** on the uncovered set `U`:
the greedy picks accumulated until `U` is exhausted.
-/
noncomputable def greedySetCover (F : Finset (Finset α)) : (U : Finset α) → (∀ x ∈ U, ∃ S ∈ F, x ∈ S) → Finset (Finset α)
  | U, hcov =>
      if hU : U = ∅ then ∅
      else
        let hF : F.Nonempty := cover_nonempty F hcov (Finset.nonempty_iff_ne_empty.mpr hU)
        let S := pickSet F U hF
        insert S (greedySetCover F (U \ S) (cover_sub F hcov (Finset.sdiff_subset (s := U) (t := S))))
termination_by U => U.card
decreasing_by
  classical
  exact pickSet_sdiff_card_lt F hcov (Finset.nonempty_iff_ne_empty.mpr hU)

/-- The family returned by GREEDY-SET-COVER is drawn from the input family `F`. -/
lemma greedySetCover_subset (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) :
    greedySetCover F U hcov ⊆ F := by
  classical
  let R : Finset α → Finset α → Prop := fun a b => a.card < b.card
  have hwf : WellFounded R := (measure (fun s : Finset α => s.card)).wf
  let P : Finset α → Prop := fun U' =>
    ∀ hcov' : ∀ x ∈ U', ∃ S ∈ F, x ∈ S, greedySetCover F U' hcov' ⊆ F
  have hmain : ∀ U' : Finset α, P U' := by
    refine hwf.fix (C := P) ?_
    intro U' ih hcov'
    by_cases hU : U' = ∅
    · subst U'
      rw [greedySetCover.eq_1]
      simp
    · let hF : F.Nonempty := cover_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      let S := pickSet F U' hF
      have hlt : (U' \ S).card < U'.card :=
        pickSet_sdiff_card_lt F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      have ih' : greedySetCover F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) ⊆ F :=
        ih (U' \ S) hlt (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S)))
      rw [greedySetCover.eq_1, dif_neg hU]
      intro T hT
      rw [Finset.mem_insert] at hT
      rcases hT with hT_eq | hT_mem
      · subst T
        exact pickSet_mem F U' hF
      · exact ih' hT_mem
  exact hmain U hcov

/--
**Theorem 35.3 (correctness).**  The family returned by GREEDY-SET-COVER covers
its universe: every element of `U` lies in some chosen set.
-/
lemma greedySetCover_covers (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) :
    Covers U (greedySetCover F U hcov) := by
  classical
  let R : Finset α → Finset α → Prop := fun a b => a.card < b.card
  have hwf : WellFounded R := (measure (fun s : Finset α => s.card)).wf
  let P : Finset α → Prop := fun U' =>
    ∀ hcov' : ∀ x ∈ U', ∃ S ∈ F, x ∈ S, Covers U' (greedySetCover F U' hcov')
  have hmain : ∀ U' : Finset α, P U' := by
    refine hwf.fix (C := P) ?_
    intro U' ih hcov'
    by_cases hU : U' = ∅
    · subst U'
      intro x hx
      simp at hx
    · let hF : F.Nonempty := cover_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      let S := pickSet F U' hF
      have hlt : (U' \ S).card < U'.card :=
        pickSet_sdiff_card_lt F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      have hcov'' : ∀ x ∈ U' \ S, ∃ T ∈ F, x ∈ T :=
        cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))
      have ih' : Covers (U' \ S) (greedySetCover F (U' \ S) hcov'') :=
        ih (U' \ S) hlt hcov''
      rw [greedySetCover.eq_1, dif_neg hU]
      intro x hx
      by_cases hxS : x ∈ S
      · exact ⟨S, Finset.mem_insert.mpr (Or.inl rfl), hxS⟩
      · rcases ih' x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩) with ⟨T, hT, hxT⟩
        exact ⟨T, Finset.mem_insert.mpr (Or.inr hT), hxT⟩
  exact hmain U hcov

/-- The greedy cost is exactly the charge accrued by the elements of the whole
universe. -/
lemma greedyCost_eq_chargeSum (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) :
    greedyCost F U hcov = chargeSum F U hcov U := by
  classical
  let R : Finset α → Finset α → Prop := fun a b => a.card < b.card
  have hwf : WellFounded R := (measure (fun s : Finset α => s.card)).wf
  let P : Finset α → Prop := fun U' =>
    ∀ hcov' : ∀ x ∈ U', ∃ S ∈ F, x ∈ S, greedyCost F U' hcov' = chargeSum F U' hcov' U'
  have hmain : ∀ U' : Finset α, P U' := by
    refine hwf.fix (C := P) ?_
    intro U' ih hcov'
    by_cases hU : U' = ∅
    · subst U'
      rw [greedyCost.eq_1, chargeSum.eq_1]
      simp
    · let hF : F.Nonempty := cover_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      let S := pickSet F U' hF
      have hlt : (U' \ S).card < U'.card :=
        pickSet_sdiff_card_lt F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      have hih : greedyCost F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S)))
          = chargeSum F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) (U' \ S) :=
        ih (U' \ S) hlt (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S)))
      have hone : ((U' ∩ S).card : ℚ) * ((S ∩ U').card : ℚ)⁻¹ = 1 := by
        have hne0 : (S ∩ U').card ≠ 0 := by
          have hpos : 1 ≤ (S ∩ U').card :=
            Finset.card_pos.mpr (pickSet_covers_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU))
          omega
        have hc : (U' ∩ S).card = (S ∩ U').card := by rw [Finset.inter_comm]
        rw [hc]
        exact mul_inv_cancel₀ (by exact_mod_cast hne0)
      calc
        greedyCost F U' hcov' = 1 + greedyCost F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) := by
          rw [greedyCost.eq_1, dif_neg hU]
        _ = ((U' ∩ S).card : ℚ) * ((S ∩ U').card : ℚ)⁻¹
            + chargeSum F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) (U' \ S) := by
          rw [hone, hih]
        _ = chargeSum F U' hcov' U' := by
          conv_rhs => rw [chargeSum.eq_1]
          rw [dif_neg hU]
  exact hmain U hcov

/--
**Lemma (charge bound).**  A set `A` of elements still uncovered — necessarily a
subset of some set of `F` — is charged at most `H(|A|)` over the whole greedy
run.  This is the charging step of Theorem 35.3: when the greedy pick first
covers an element of `A`, it covers at least `|A|` uncovered elements, so the
price per element is at most the corresponding harmonic term.
-/
lemma chargeSum_le_harmonic (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) {A : Finset α}
    (hA : A ⊆ U) (hAS : ∃ S ∈ F, A ⊆ S) :
    chargeSum F U hcov A ≤ harmonic A.card := by
  classical
  let R : Finset α → Finset α → Prop := fun a b => a.card < b.card
  have hwf : WellFounded R := (measure (fun s : Finset α => s.card)).wf
  let P : Finset α → Prop := fun U' =>
    ∀ hcov' : ∀ x ∈ U', ∃ S ∈ F, x ∈ S, ∀ A' : Finset α,
      A' ⊆ U' → (∃ S ∈ F, A' ⊆ S) → chargeSum F U' hcov' A' ≤ harmonic A'.card
  have hmain : ∀ U' : Finset α, P U' := by
    refine hwf.fix (C := P) ?_
    intro U' ih hcov' A' hA' hAS'
    by_cases hU : U' = ∅
    · subst U'
      rw [chargeSum.eq_1]
      simp
      exact harmonic_nonneg A'.card
    · let hF : F.Nonempty := cover_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      let S := pickSet F U' hF
      have hlt : (U' \ S).card < U'.card :=
        pickSet_sdiff_card_lt F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      have hA'2 : A' \ S ⊆ U' \ S := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hA' (Finset.mem_sdiff.mp hx).1, (Finset.mem_sdiff.mp hx).2⟩
      rcases hAS' with ⟨S0, hS0F, hA'S0⟩
      have hAS'2 : ∃ S1 ∈ F, A' \ S ⊆ S1 := ⟨S0, hS0F, by
        intro x hx
        exact hA'S0 (Finset.mem_sdiff.mp hx).1⟩
      have hterm2 : chargeSum F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) (A' \ S)
          ≤ harmonic (A' \ S).card :=
        ih (U' \ S) hlt (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) (A' \ S) hA'2 hAS'2
      have hcard : (A' ∩ S).card = A'.card - (A' \ S).card := by
        have hsum : (A' ∩ S).card + (A' \ S).card = A'.card := Finset.card_inter_add_card_sdiff A' S
        omega
      have hterm1 : ((A' ∩ S).card : ℚ) * ((S ∩ U').card : ℚ)⁻¹
          ≤ harmonic A'.card - harmonic (A' \ S).card := by
        by_cases hAe : A' = ∅
        · subst A'
          simp
        · have hn : 0 < A'.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAe)
          have hAS0 : A'.card ≤ (S0 ∩ U').card := by
            apply Finset.card_le_card
            intro x hx
            exact Finset.mem_inter.mpr ⟨hA'S0 hx, hA' hx⟩
          have hnm : A'.card ≤ (S ∩ U').card :=
            le_trans hAS0 (pickSet_coverage_le F U' hF hS0F)
          have hb := harm_bound (A' \ S).card A'.card (S ∩ U').card
            (Finset.card_le_card (Finset.sdiff_subset (s := A') (t := S))) hn hnm
          rw [hcard]
          exact hb
      calc
        chargeSum F U' hcov' A' = ((A' ∩ S).card : ℚ) * ((S ∩ U').card : ℚ)⁻¹
            + chargeSum F (U' \ S) (cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))) (A' \ S) := by
          rw [chargeSum.eq_1, dif_neg hU]
        _ ≤ (harmonic A'.card - harmonic (A' \ S).card) + harmonic (A' \ S).card := by
          nlinarith [hterm1, hterm2]
        _ = harmonic A'.card := by ring
  exact hmain U hcov A hA hAS

/-- If every element of `T` lies in some member of the family `ℱ`, then `T` is
no larger than the sum of the sizes of the members' intersections with `T`. -/
lemma card_le_sum_card_of_cover {T : Finset α} {ℱ : Finset (Finset α)}
    (h : ∀ x ∈ T, ∃ S ∈ ℱ, x ∈ S) :
    T.card ≤ ∑ S ∈ ℱ, (S ∩ T).card := by
  classical
  have hsub : T ⊆ Finset.biUnion ℱ (fun S : Finset α => S ∩ T) := by
    intro x hx
    rcases h x hx with ⟨S, hS, hxS⟩
    exact Finset.mem_biUnion.mpr ⟨S, hS, Finset.mem_inter.mpr ⟨hxS, hx⟩⟩
  have hcard : T.card ≤ (Finset.biUnion ℱ (fun S : Finset α => S ∩ T)).card :=
    Finset.card_le_card hsub
  have hcard2 : (Finset.biUnion ℱ (fun S : Finset α => S ∩ T)).card ≤ ∑ S ∈ ℱ, (S ∩ T).card := by
    exact Finset.card_biUnion_le (s := ℱ) (t := fun S : Finset α => S ∩ T)
  exact le_trans hcard hcard2

/-- The total charge of the whole uncovered set is no more than the sum, over a
cover `C` of the universe, of the charges of the cover sets' portions of the
uncovered set. -/
lemma chargeSum_U_le_sum_cover (F : Finset (Finset α)) (X U : Finset α) (C : Finset (Finset α))
    (hU : U ⊆ X) (hC : Covers X C) (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) :
    chargeSum F U hcov U ≤ ∑ S ∈ C, chargeSum F U hcov (S ∩ U) := by
  classical
  let R : Finset α → Finset α → Prop := fun a b => a.card < b.card
  have hwf : WellFounded R := (measure (fun s : Finset α => s.card)).wf
  let P : Finset α → Prop := fun U' =>
    ∀ hcov' : ∀ x ∈ U', ∃ S ∈ F, x ∈ S, U' ⊆ X →
      chargeSum F U' hcov' U' ≤ ∑ S ∈ C, chargeSum F U' hcov' (S ∩ U')
  have hmain : ∀ U' : Finset α, P U' := by
    refine hwf.fix (C := P) ?_
    intro U' ih hcov' hU'X
    by_cases hU : U' = ∅
    · subst U'
      simp [chargeSum.eq_1]
    · let hF : F.Nonempty := cover_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      let Sp := pickSet F U' hF
      let U'' := U' \ Sp
      let T := U' ∩ Sp
      have hcov'' : ∀ x ∈ U'', ∃ S ∈ F, x ∈ S :=
        cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := Sp))
      have hlt : U''.card < U'.card := by
        simpa [U''] using pickSet_sdiff_card_lt F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      have hstep : chargeSum F U' hcov' U' = (T.card : ℚ) * ((Sp ∩ U').card : ℚ)⁻¹
          + chargeSum F U'' hcov'' U'' := by
        rw [chargeSum.eq_1, dif_neg hU]
      have h1 : (T.card : ℚ) * ((Sp ∩ U').card : ℚ)⁻¹
          ≤ ∑ S ∈ C, ((S ∩ T).card : ℚ) * ((Sp ∩ U').card : ℚ)⁻¹ := by
        have hcoverT : ∀ x ∈ T, ∃ S ∈ C, x ∈ S := by
          intro x hx
          rcases hC x (hU'X (Finset.mem_inter.mp hx).1) with ⟨S, hS, hxS⟩
          exact ⟨S, hS, hxS⟩
        have hcardT : T.card ≤ ∑ S ∈ C, (S ∩ T).card := card_le_sum_card_of_cover hcoverT
        have hcardQ : (T.card : ℚ) ≤ ∑ S ∈ C, ((S ∩ T).card : ℚ) := by
          exact_mod_cast hcardT
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right hcardQ (by positivity)
      have h2 : chargeSum F U'' hcov'' U'' ≤ ∑ S ∈ C, chargeSum F U'' hcov'' (S ∩ U'') := by
        exact ih U'' hlt hcov'' (by
          intro x hx
          exact hU'X (Finset.mem_sdiff.mp hx).1)
      have hrhs : ∑ S ∈ C, chargeSum F U' hcov' (S ∩ U')
          = ∑ S ∈ C, (((S ∩ T).card : ℚ) * ((Sp ∩ U').card : ℚ)⁻¹
              + chargeSum F U'' hcov'' (S ∩ U'')) := by
        apply Finset.sum_congr rfl
        intro S hS
        have hSinter : (S ∩ U') ∩ Sp = S ∩ T := by
          simp [T, Finset.inter_assoc]
        have hSdiff : (S ∩ U') \ Sp = S ∩ U'' := by
          dsimp [U'']
          ext x; simp [Finset.mem_sdiff, Finset.mem_inter]; tauto
        rw [chargeSum.eq_1, dif_neg hU]
        simp [Sp, U'', hSinter, hSdiff]
      calc
        chargeSum F U' hcov' U' = (T.card : ℚ) * ((Sp ∩ U').card : ℚ)⁻¹ + chargeSum F U'' hcov'' U'' := hstep
        _ ≤ ∑ S ∈ C, (((S ∩ T).card : ℚ) * ((Sp ∩ U').card : ℚ)⁻¹
              + chargeSum F U'' hcov'' (S ∩ U'')) := by
          rw [Finset.sum_add_distrib]
          exact add_le_add h1 h2
        _ = ∑ S ∈ C, chargeSum F U' hcov' (S ∩ U') := hrhs.symm
  exact hmain U hcov hU

/--
**Theorem 35.3.**  GREEDY-SET-COVER returns a set cover whose cost is at most
`H(d) · |C|` for every cover `C` of `X` — in particular, for an optimal one —
where `d` bounds the sizes of the sets in `F` and `H` is the harmonic number.
Thus GREEDY-SET-COVER is an `H(d)`-approximation algorithm (CLRS §35.3).

Indeed, the cost is the total charge (`greedyCost_eq_chargeSum`), the total
charge is no more than the sum over a cover of its per-set charges
(`chargeSum_U_le_sum_cover`), each per-set charge is at most `H(|S|)`
(`chargeSum_le_harmonic`), and `H(|S|) ≤ H(d)` by monotonicity.
-/
theorem greedySetCover_approx (X : Finset α) (F : Finset (Finset α))
    (hcov : ∀ x ∈ X, ∃ S ∈ F, x ∈ S)
    (d : ℕ) (hd : ∀ S ∈ F, S.card ≤ d)
    (C : Finset (Finset α)) (hCsub : C ⊆ F) (hCcov : Covers X C) :
    greedyCost F X hcov ≤ harmonic d * (C.card : ℚ) := by
  classical
  have h1 := greedyCost_eq_chargeSum F hcov
  have h2 := chargeSum_U_le_sum_cover F X X C (le_refl X) hCcov hcov
  have h3 : ∀ S ∈ C, chargeSum F X hcov (S ∩ X) ≤ harmonic d := by
    intro S hS
    have hSsubF : S ∈ F := hCsub hS
    have hleS : chargeSum F X hcov (S ∩ X) ≤ harmonic (S ∩ X).card :=
      chargeSum_le_harmonic F hcov
        (by intro x hx; exact (Finset.mem_inter.mp hx).2)
        ⟨S, hSsubF, by intro x hx; exact (Finset.mem_inter.mp hx).1⟩
    have hcard : (S ∩ X).card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
    have hcard' : (S ∩ X).card ≤ d := le_trans hcard (hd S hSsubF)
    exact le_trans hleS (harmonic_mono hcard')
  have h4 : (∑ S ∈ C, chargeSum F X hcov (S ∩ X)) ≤ ∑ S ∈ C, harmonic d := by
    exact Finset.sum_le_sum h3
  have h5 : (∑ S ∈ C, harmonic d) = (C.card : ℚ) * harmonic d := by
    rw [Finset.sum_const]
    norm_num
  calc
    greedyCost F X hcov = chargeSum F X hcov X := h1
    _ ≤ ∑ S ∈ C, chargeSum F X hcov (S ∩ X) := h2
    _ ≤ ∑ S ∈ C, harmonic d := h4
    _ = harmonic d * (C.card : ℚ) := by
      rw [h5]
      ring

/-- If the family `C` covers the nonempty set `U`, then some set of `C` covers
at least `|U| / |C|` elements of `U`.  This is the averaging step of Theorem
35.4: a size-`k` cover distributes `|U|` elements among its `k` sets. -/
lemma exists_cover_set_ge_fraction {U : Finset α} {C : Finset (Finset α)}
    (hC : Covers U C) (hU : U.Nonempty) :
    ∃ S ∈ C, (U.card : ℚ) / (C.card : ℚ) ≤ ((S ∩ U).card : ℚ) := by
  classical
  have hCne : C.Nonempty := cover_nonempty C hC hU
  have hsum : (U.card : ℚ) ≤ ∑ S ∈ C, ((S ∩ U).card : ℚ) := by
    exact_mod_cast card_le_sum_card_of_cover hC
  by_contra hnone
  have hall : ∀ S ∈ C, ((S ∩ U).card : ℚ) < (U.card : ℚ) / (C.card : ℚ) := by
    intro S hS
    exact lt_of_not_ge (fun hge => hnone ⟨S, hS, hge⟩)
  have hle : ∀ S ∈ C, ((S ∩ U).card : ℚ) ≤ (U.card : ℚ) / (C.card : ℚ) := by
    intro S hS
    exact le_of_lt (hall S hS)
  have hstrict : (∑ S ∈ C, ((S ∩ U).card : ℚ)) < ∑ S ∈ C, ((U.card : ℚ) / (C.card : ℚ)) := by
    refine Finset.sum_lt_sum hle ?_
    rcases hCne with ⟨S0, hS0⟩
    exact ⟨S0, hS0, hall S0 hS0⟩
  have hsumlt : (∑ S ∈ C, ((S ∩ U).card : ℚ)) < (C.card : ℚ) * ((U.card : ℚ) / (C.card : ℚ)) := by
    rwa [Finset.sum_const, nsmul_eq_mul] at hstrict
  have hcancel : (C.card : ℚ) * ((U.card : ℚ) / (C.card : ℚ)) = (U.card : ℚ) := by
    have hc : (C.card : ℚ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr hCne)
    field_simp [hc]
  linarith

/-- The greedy pick covers at least `|U| / |C|` elements of the uncovered set
`U`, because some set of the cover `C` — which is a subfamily of `F` — covers
that many, and the greedy pick covers at least as many as any set of `F`. -/
lemma pickSet_cover_fraction (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) {C : Finset (Finset α)}
    (hCsub : C ⊆ F) (hCcov : Covers U C) (hU : U.Nonempty) :
    (U.card : ℚ) / (C.card : ℚ) ≤ ((pickSet F U (cover_nonempty F hcov hU) ∩ U).card : ℚ) := by
  classical
  rcases exists_cover_set_ge_fraction hCcov hU with ⟨S, hS, hSfrac⟩
  have hle : (S ∩ U).card ≤ (pickSet F U (cover_nonempty F hcov hU) ∩ U).card :=
    pickSet_coverage_le F U (cover_nonempty F hcov hU) (hCsub hS)
  exact le_trans hSfrac (by exact_mod_cast hle)

/-- One greedy step shrinks the uncovered set by the factor `(1 - 1/|C|)`: since
the greedy pick covers at least `|U| / |C|` elements, the remainder `U \ S` has
at most `|U| · (1 - 1/|C|)` elements.  This is the multiplicative decrease of
Theorem 35.4's proof. -/
lemma pickSet_sdiff_shrink (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) {C : Finset (Finset α)}
    (hCsub : C ⊆ F) (hCcov : Covers U C) (hU : U.Nonempty) :
    ((U \ pickSet F U (cover_nonempty F hcov hU)).card : ℚ) ≤
      (U.card : ℚ) * (1 - (C.card : ℚ)⁻¹) := by
  classical
  let S := pickSet F U (cover_nonempty F hcov hU)
  have hf := pickSet_cover_fraction F hcov hCsub hCcov hU
  have hsplit : ((U \ S).card : ℚ) = (U.card : ℚ) - ((U ∩ S).card : ℚ) := by
    have hc : (U ∩ S).card + (U \ S).card = U.card := Finset.card_inter_add_card_sdiff U S
    linarith [show ((U ∩ S).card : ℚ) + ((U \ S).card : ℚ) = (U.card : ℚ) from by exact_mod_cast hc]
  calc
    ((U \ S).card : ℚ) = (U.card : ℚ) - ((U ∩ S).card : ℚ) := hsplit
    _ ≤ (U.card : ℚ) - (U.card : ℚ) / (C.card : ℚ) := by
      have hle : (U.card : ℚ) / (C.card : ℚ) ≤ ((U ∩ S).card : ℚ) := by
        simpa [S, Finset.inter_comm] using hf
      linarith
    _ = (U.card : ℚ) * (1 - (C.card : ℚ)⁻¹) := by ring

/--
**Fuel bound.**  If after `N` greedy steps the uncovered size is bounded by the
`N`-th power of the shrink factor `(1 - 1/|C|)`, then the greedy loop has
terminated: `greedyCost ≤ N`.  More precisely, if `|U| · (1 - 1/|C|)^N < 1`
then the cost is at most `N`.  This is the iteration step of Theorem 35.4.
-/
lemma greedyCost_le_fuel (F : Finset (Finset α)) {U : Finset α}
    (hcov : ∀ x ∈ U, ∃ S ∈ F, x ∈ S) {C : Finset (Finset α)}
    (hCsub : C ⊆ F) (hCcov : Covers U C) (N : ℕ)
    (hN : (U.card : ℚ) * ((1 - (C.card : ℚ)⁻¹) ^ N) < 1) :
    greedyCost F U hcov ≤ N := by
  classical
  let R : Finset α → Finset α → Prop := fun a b => a.card < b.card
  have hwf : WellFounded R := (measure (fun s : Finset α => s.card)).wf
  let P : Finset α → Prop := fun U' =>
    ∀ hcov' : ∀ x ∈ U', ∃ S ∈ F, x ∈ S, ∀ hCsub' : C ⊆ F,
      ∀ hCcov' : Covers U' C, ∀ N' : ℕ,
        (U'.card : ℚ) * ((1 - (C.card : ℚ)⁻¹) ^ N') < 1 → greedyCost F U' hcov' ≤ N'
  have hmain : ∀ U' : Finset α, P U' := by
    refine hwf.fix (C := P) ?_
    intro U' ih hcov' hCsub' hCcov' N' hN'
    by_cases hU : U' = ∅
    · subst U'
      rw [greedyCost.eq_1]
      simp
    · let hF : F.Nonempty := cover_nonempty F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      let S := pickSet F U' hF
      have hlt : (U' \ S).card < U'.card :=
        pickSet_sdiff_card_lt F hcov' (Finset.nonempty_iff_ne_empty.mpr hU)
      have hcov'' : ∀ x ∈ U' \ S, ∃ T ∈ F, x ∈ T :=
        cover_sub F hcov' (Finset.sdiff_subset (s := U') (t := S))
      have hCcov'' : Covers (U' \ S) C := by
        intro x hx
        exact hCcov' x (Finset.mem_sdiff.mp hx).1
      by_cases hN0 : N' = 0
      · subst N'
        have hcard1 : (1 : ℕ) ≤ U'.card := by
          have hpos : 0 < U'.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hU)
          omega
        have hone : (1 : ℚ) ≤ (U'.card : ℚ) := by exact_mod_cast hcard1
        have hlt1 : (U'.card : ℚ) < 1 := by simpa using hN'
        linarith
      · obtain ⟨N'', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
        let c : ℚ := 1 - (C.card : ℚ)⁻¹
        have hinv_le : (C.card : ℚ)⁻¹ ≤ 1 := by
          by_cases hk0 : C.card = 0
          · simp [hk0]
          · have hk1 : 1 ≤ C.card := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
            have hkq : (1 : ℚ) ≤ (C.card : ℚ) := by exact_mod_cast hk1
            exact inv_le_one_of_one_le₀ hkq
        have hcnonneg : 0 ≤ c := by
          dsimp [c]
          linarith
        have hshrink := pickSet_sdiff_shrink F hcov' hCsub' hCcov' (Finset.nonempty_iff_ne_empty.mpr hU)
        have hfuel' : ((U' \ S).card : ℚ) * (c ^ N'') < 1 := by
          have hcpow : 0 ≤ c ^ N'' := pow_nonneg hcnonneg N''
          have hmul : ((U' \ S).card : ℚ) * (c ^ N'') ≤ (U'.card : ℚ) * (c ^ (N'' + 1)) := by
            calc
              ((U' \ S).card : ℚ) * (c ^ N'') ≤ (U'.card : ℚ) * c * (c ^ N'') := by
                exact mul_le_mul_of_nonneg_right hshrink hcpow
              _ = (U'.card : ℚ) * (c * (c ^ N'')) := by ring
              _ = (U'.card : ℚ) * (c ^ (N'' + 1)) := by rw [pow_succ]; ring
          exact lt_of_le_of_lt hmul (by simpa [c] using hN')
        have hfuel'' : ((U' \ S).card : ℚ) * ((1 - (C.card : ℚ)⁻¹) ^ N'') < 1 := by
          simpa [c] using hfuel'
        have ih' : greedyCost F (U' \ S) hcov'' ≤ N'' :=
          ih (U' \ S) hlt hcov'' hCsub' hCcov'' N'' hfuel''
        rw [greedyCost.eq_1, dif_neg hU]
        have hsum : (1 : ℚ) + greedyCost F (U' \ S) hcov'' ≤ (1 : ℚ) + (N'' : ℚ) := by
          nlinarith [ih']
        have hcast : ((N'' + 1 : ℕ) : ℚ) = (1 : ℚ) + (N'' : ℚ) := by
          norm_num [Nat.cast_add, add_comm]
        nlinarith
  exact hmain U hcov hCsub hCcov N hN

/--
**Theorem 35.4.**  GREEDY-SET-COVER is an `O(lg |X|)`-approximation algorithm:
for every cover `C` of `X`, the greedy cost is at most `|C| · (⌈ln |X|⌉ + 1)`
(CLRS §35.3, Theorem 35.4).

The proof iterates the multiplicative shrink `|U_{i+1}| ≤ |U_i| · (1 - 1/|C|)`:
after `|C| · ⌈ln |X|⌉` steps the uncovered set has size below `1`, so the loop
has terminated.  The comparison `1 - 1/k ≤ e^{-1/k}` turns the iterated shrink
into the exponential bound `|X| · (1 - 1/k)^{k·L} ≤ |X| · e^{-L} < 1`, where
`L = ⌈ln |X|⌉ + 1`.
-/
theorem greedySetCover_ln_approx (X : Finset α) (F : Finset (Finset α))
    (hcov : ∀ x ∈ X, ∃ S ∈ F, x ∈ S)
    (C : Finset (Finset α)) (hCsub : C ⊆ F) (hCcov : Covers X C) :
    greedyCost F X hcov ≤ (C.card : ℚ) * (((⌈Real.log (X.card : ℝ)⌉ : ℤ).toNat + 1 : ℕ) : ℚ) := by
  classical
  let L : ℕ := (⌈Real.log (X.card : ℝ)⌉ : ℤ).toNat + 1
  let k : ℕ := C.card
  let cQ : ℚ := 1 - (k : ℚ)⁻¹
  let cR : ℝ := 1 - (k : ℝ)⁻¹
  have hfuel : (X.card : ℚ) * (cQ ^ (k * L)) < 1 := by
    by_cases hX0 : X = ∅
    · subst X
      simp [cQ]
    · by_cases hk0 : k = 0
      · have hCempty : C = ∅ := Finset.card_eq_zero.mp (by simpa [k] using hk0)
        have hXempty : X = ∅ := by
          by_contra hne
          rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨x, hx⟩
          rcases hCcov x hx with ⟨S, hS, _⟩
          simpa [hCempty] using hS
        contradiction
      · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
        have hXposn : 0 < X.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hX0)
        have hX1n : 1 ≤ X.card := Nat.succ_le_of_lt hXposn
        have hkℝ : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
        have hcRnonneg : 0 ≤ cR := by
          dsimp [cR]
          have hinv : (k : ℝ)⁻¹ ≤ 1 := by
            have hkq : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
            exact inv_le_one_of_one_le₀ hkq
          linarith
        have hpow1 : cR ^ k ≤ Real.exp (-1) := by
          have hbase : cR ≤ Real.exp (-(k : ℝ)⁻¹) := by
            dsimp [cR]
            have h := Real.add_one_le_exp (-(k : ℝ)⁻¹)
            linarith
          calc
            cR ^ k ≤ (Real.exp (-(k : ℝ)⁻¹)) ^ k := pow_le_pow_left₀ hcRnonneg hbase k
            _ = Real.exp (k * (-(k : ℝ)⁻¹)) := by rw [Real.exp_nat_mul]
            _ = Real.exp (-1) := by
              have hmul : k * (-(k : ℝ)⁻¹) = -1 := by
                rw [mul_neg, mul_inv_cancel₀ hkℝ]
              rw [hmul]
        have hpow2 : (cR ^ k) ^ L ≤ Real.exp (-(L : ℝ)) := by
          have hb : 0 ≤ cR ^ k := pow_nonneg hcRnonneg k
          calc
            (cR ^ k) ^ L ≤ (Real.exp (-1)) ^ L := pow_le_pow_left₀ hb hpow1 L
            _ = Real.exp (L * (-1)) := by rw [Real.exp_nat_mul]
            _ = Real.exp (-(L : ℝ)) := by ring_nf
        have hleR : (X.card : ℝ) * (cR ^ (k * L)) ≤ (X.card : ℝ) * Real.exp (-(L : ℝ)) := by
          have h1 : cR ^ (k * L) ≤ Real.exp (-(L : ℝ)) := by
            rw [pow_mul]
            exact hpow2
          exact mul_le_mul_of_nonneg_left h1 (by exact_mod_cast (Nat.zero_le X.card))
        have hltR : (X.card : ℝ) * Real.exp (-(L : ℝ)) < 1 := by
          have hXpos : 0 < (X.card : ℝ) := by exact_mod_cast hXposn
          have hlog : Real.exp (Real.log (X.card : ℝ)) = (X.card : ℝ) := Real.exp_log hXpos
          have hlogn : 0 ≤ Real.log (X.card : ℝ) := Real.log_nonneg (by exact_mod_cast hX1n)
          have hceil0 : 0 ≤ (⌈Real.log (X.card : ℝ)⌉ : ℤ) := Int.ceil_nonneg hlogn
          have hL : (L : ℝ) = ((⌈Real.log (X.card : ℝ)⌉ : ℤ) : ℝ) + 1 := by
            dsimp [L]
            have htoNat : ((⌈Real.log (X.card : ℝ)⌉ : ℤ).toNat : ℤ) = ⌈Real.log (X.card : ℝ)⌉ :=
              Int.toNat_of_nonneg hceil0
            have htoNatℝ : ((⌈Real.log (X.card : ℝ)⌉ : ℤ).toNat : ℝ) = ((⌈Real.log (X.card : ℝ)⌉ : ℤ) : ℝ) := by
              exact_mod_cast htoNat
            norm_num
            rw [htoNatℝ]
          have hltln : Real.log (X.card : ℝ) < (L : ℝ) := by
            have h1 : Real.log (X.card : ℝ) < ((⌈Real.log (X.card : ℝ)⌉ : ℤ) : ℝ) + 1 := by
              have hle : Real.log (X.card : ℝ) ≤ ((⌈Real.log (X.card : ℝ)⌉ : ℤ) : ℝ) := Int.le_ceil _
              have hlt : ((⌈Real.log (X.card : ℝ)⌉ : ℤ) : ℝ) < Real.log (X.card : ℝ) + 1 := Int.ceil_lt_add_one _
              nlinarith
            rwa [hL]
          have hsub : Real.log (X.card : ℝ) - (L : ℝ) < 0 := by linarith
          calc
            (X.card : ℝ) * Real.exp (-(L : ℝ)) = Real.exp (Real.log (X.card : ℝ)) * Real.exp (-(L : ℝ)) := by rw [hlog]
            _ = Real.exp (Real.log (X.card : ℝ) + (-(L : ℝ))) := by rw [← Real.exp_add]
            _ = Real.exp (Real.log (X.card : ℝ) - (L : ℝ)) := rfl
            _ < Real.exp 0 := Real.exp_lt_exp.mpr hsub
            _ = 1 := by norm_num
        have hltQ : (X.card : ℚ) * (cQ ^ (k * L)) < 1 := by
          have hltR' : (X.card : ℝ) * (cR ^ (k * L)) < 1 := lt_of_le_of_lt hleR hltR
          have hcast : (cQ : ℝ) = cR := by
            dsimp [cQ, cR]
            norm_num
          have hltR'' : (X.card : ℝ) * ((cQ : ℝ) ^ (k * L)) < 1 := by
            simpa [hcast] using hltR'
          exact_mod_cast hltR''
        simpa [cQ, k] using hltQ
  have hcost := greedyCost_le_fuel F hcov hCsub hCcov (k * L) (by simpa [cQ, k] using hfuel)
  have hN : ((k * L : ℕ) : ℚ) = (k : ℚ) * (L : ℚ) := by norm_num [Nat.cast_mul]
  simpa [hN, k, L] using hcost

end SetCover

end CLRS
