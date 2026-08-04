import CLRSLean.Extensions.TreapRandom

open CLRS.Probability
open scoped BigOperators

namespace CLRS.Extensions

namespace Treap

/-!
# Randomized treap: expected height

This module develops the next proof layer toward bounding the expected
**height** (the maximum depth over all keys) by {lit}`O(log n)`.

The depth of a single key was bounded in {lit}`TreapRandom` via its harmonic
ancestor sum.  The height needs more: a bound on the *maximum* depth, which is
obtained by an exponential tail on the depth of a single key.

**Record structure.**  Walking left from key {lit}`b`, its left-ancestors are
exactly the left-to-right record maxima of the priority sequence
{lit}`(σ b, σ (b-1), …, σ 0)`.  In a random permutation the number of records
has an exponential tail, so the depth does too, and a union bound over the keys
turns it into an {lit}`O(log n)` expected-height bound.

Main results:

- Theorem {lit}`expectedTreapHeight_le`: {lit}`E[height] ≤ 30 · H_n`, an
  explicit expected-height bound.  The proof combines an exponential tail on
  the single-key depth (via the left/right-ancestor record-maxima structure)
  with a union bound over the keys and a tail sum split at
  {lit}`k ≈ 12 · ⌈H_n⌉`.

Status: prototype, not registered in {lit}`literate.toml`.  The depth
decomposition, the left-ancestor product formula, the exponential tails on the
left- and right-ancestor counts, the single-key depth tail, and the final
expected-height bound are all kernel-checked
({lit}`[propext, Classical.choice, Quot.sound]`).
-/

/-- The left-ancestors of key {lit}`b`: keys strictly below {lit}`b` that are
ancestors of {lit}`b`. -/
noncomputable def leftAncestors {n : ℕ} (σ : PrioPerm n) (b : Fin n) : ℕ :=
  (Finset.univ.filter (fun a : Fin n => a < b ∧ Ancestor σ a b)).card

/-- The right-ancestors of key {lit}`b`: keys strictly above {lit}`b` that are
ancestors of {lit}`b`. -/
noncomputable def rightAncestors {n : ℕ} (σ : PrioPerm n) (b : Fin n) : ℕ :=
  (Finset.univ.filter (fun a : Fin n => b < a ∧ Ancestor σ a b)).card

/-- The depth of {lit}`b` counts its left-ancestors, itself, and its
right-ancestors. -/
lemma depth_eq_left_add_right {n : ℕ} (σ : PrioPerm n) (b : Fin n) :
    depth σ b = leftAncestors σ b + rightAncestors σ b + 1 := by
  classical
  have hpt : ∀ a : Fin n, (if Ancestor σ a b then 1 else 0) =
      (if a < b ∧ Ancestor σ a b then 1 else 0) + (if a = b then 1 else 0) +
        (if b < a ∧ Ancestor σ a b then 1 else 0) := by
    intro a
    by_cases hne : a = b
    · subst a; simp [Ancestor]
    · have hltgt : a < b ∨ b < a := lt_or_gt_of_ne hne
      rcases hltgt with hlt | hgt
      · have hb_lt : ¬ b < a := not_lt.mpr (le_of_lt hlt)
        have ha_ne : ¬ a = b := ne_of_lt hlt
        simp [hlt, hb_lt, ha_ne]
      · have ha_lt : ¬ a < b := not_lt.mpr (le_of_lt hgt)
        have ha_ne : ¬ a = b := ne_of_gt hgt
        simp [hgt, ha_lt, ha_ne]
  calc
    depth σ b = (∑ a : Fin n, if Ancestor σ a b then 1 else 0) := by
      unfold depth
      rw [Finset.card_filter]
    _ = (∑ a : Fin n, ((if a < b ∧ Ancestor σ a b then 1 else 0) + (if a = b then 1 else 0) +
          (if b < a ∧ Ancestor σ a b then 1 else 0))) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hpt a
    _ = (∑ a : Fin n, if a < b ∧ Ancestor σ a b then 1 else 0) + 1 +
        (∑ a : Fin n, if b < a ∧ Ancestor σ a b then 1 else 0) := by
          simp [Finset.sum_add_distrib, Finset.sum_ite_eq']
    _ = leftAncestors σ b + rightAncestors σ b + 1 := by
          unfold leftAncestors rightAncestors
          rw [Finset.card_filter, Finset.card_filter]
          ring

/-- The height of the treap under {lit}`σ`: the maximum depth over all keys. -/
noncomputable def treapHeight {n : ℕ} (σ : PrioPerm n) : ℕ :=
  (Finset.univ.sup (fun b : Fin n => depth σ b))

/-- The expected height under a uniform random priority permutation. -/
noncomputable def expectedTreapHeight {n : ℕ} : ℝ :=
  fintypeExpect (fun σ : PrioPerm n => (treapHeight σ : ℝ))

/-! ## Exponential tail on the depth -/

/-- Right-multiplication by a transposition is a bijection on `PrioPerm n`; it
swaps the priorities carried by the keys `c` and `t`. -/
lemma swapComp'_bijective {c t : Fin n} :
    Function.Bijective (fun (σ : PrioPerm n) => σ * (Equiv.swap c t)) := by
  constructor
  · intro σ₁ σ₂ h
    apply_fun (fun φ : PrioPerm n => φ * (Equiv.swap c t)) at h
    simpa [mul_assoc] using h
  · intro σ
    refine ⟨σ * (Equiv.swap c t), ?_⟩
    simp [mul_assoc]

/-- Swapping the priorities carried by the keys `c` and `t` (neither of which is
the leader `a`) preserves `a` carrying the maximum priority of `I`. -/
lemma maxOver_swap_key {n : ℕ} {I : Finset (Fin n)} {a c t : Fin n} (σ : PrioPerm n)
    (hca : c ≠ a) (hta : t ≠ a) (hcI : c ∈ I) (htI : t ∈ I)
    (hmax : MaxOver σ I a) :
    MaxOver (σ * (Equiv.swap c t)) I a := by
  rcases hmax with ⟨haI, hle⟩
  refine ⟨haI, ?_⟩
  intro k hkI
  have hswapa : Equiv.swap c t a = a := Equiv.swap_apply_of_ne_of_ne (Ne.symm hca) (Ne.symm hta)
  have ha' : prioOfPerm (σ * (Equiv.swap c t)) a = prioOfPerm σ a := by
    unfold prioOfPerm
    rw [Equiv.Perm.mul_apply, hswapa]
  rw [ha']
  have hk' : prioOfPerm (σ * (Equiv.swap c t)) k = prioOfPerm σ (Equiv.swap c t k) := by
    unfold prioOfPerm
    rw [Equiv.Perm.mul_apply]
  rw [hk']
  by_cases hkc : k = c
  · subst k
    rw [Equiv.swap_apply_left]
    exact hle t htI
  · by_cases hkt : k = t
    · subst k
      rw [Equiv.swap_apply_right]
      exact hle c hcI
    · have hk'' : Equiv.swap c t k = k := Equiv.swap_apply_of_ne_of_ne hkc hkt
      rw [hk'']
      exact hle k hkI

/-- Swapping the priorities carried by `c` and `t` moves the maximum priority of
`U` from `c` to `t` (both in `U`). -/
lemma maxOver_swap_max {n : ℕ} {U : Finset (Fin n)} {c t : Fin n} (σ : PrioPerm n)
    (hcU : c ∈ U) (htU : t ∈ U) (hmax : MaxOver σ U c) :
    MaxOver (σ * (Equiv.swap c t)) U t := by
  rcases hmax with ⟨hcU', hle⟩
  refine ⟨htU, ?_⟩
  intro k hkU
  have ht' : prioOfPerm (σ * (Equiv.swap c t)) t = prioOfPerm σ c := by
    unfold prioOfPerm
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  rw [ht']
  have hk' : prioOfPerm (σ * (Equiv.swap c t)) k = prioOfPerm σ (Equiv.swap c t k) := by
    unfold prioOfPerm
    rw [Equiv.Perm.mul_apply]
  rw [hk']
  by_cases hkc : k = c
  · subst k
    rw [Equiv.swap_apply_left]
    exact hle t htU
  · by_cases hkt : k = t
    · subst k
      rw [Equiv.swap_apply_right]
    · have hk'' : Equiv.swap c t k = k := Equiv.swap_apply_of_ne_of_ne hkc hkt
      rw [hk'']
      exact hle k hkU

/-- Given that all keys of `T` are left-ancestors of `b` (with every `a ∈ T`
strictly below `c`), the maximum priority of `Icc c b` is equally likely to sit
at any of its keys.  Counted: the `c`-max events have one `|Icc c b|`-th of the
mass of the `T`-max events. -/
lemma maxExtend_uniform {n : ℕ} {b : Fin n} (T : Finset (Fin n)) {c : Fin n}
    (hT : ∀ a ∈ T, a < c) (hc : c < b) :
    ((Finset.univ.filter (fun σ : PrioPerm n =>
        (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ (Finset.Icc c b) c)).card) *
      (Finset.Icc c b).card =
    (Finset.univ.filter (fun σ : PrioPerm n =>
        ∀ a ∈ T, MaxOver σ (Finset.Icc a b) a)).card := by
  classical
  let U : Finset (Fin n) := Finset.Icc c b
  have hcU : c ∈ U := by dsimp [U]; exact Finset.mem_Icc.mpr ⟨le_rfl, le_of_lt hc⟩
  -- For each a ∈ T, the swap of {a}∪{c,t}... build the "all T maxima preserved" helper.
  have hTswap : ∀ (a : Fin n), a ∈ T → ∀ (t : Fin n), t ∈ U →
      ∀ (σ : PrioPerm n), MaxOver σ (Finset.Icc a b) a →
        MaxOver (σ * (Equiv.swap c t)) (Finset.Icc a b) a := by
    intro a haT t htU σ hmax
    have hac : a < c := hT a haT
    have hca' : c ≠ a := ne_of_gt hac
    have hta' : t ≠ a := ne_of_gt (lt_of_lt_of_le hac (Finset.mem_Icc.mp htU).1)
    have haI : a ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨le_rfl, le_of_lt (lt_trans hac hc)⟩
    have hcI : c ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨le_of_lt hac, le_of_lt hc⟩
    have htI : t ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc] at htU
      exact Finset.mem_Icc.mpr ⟨le_trans (le_of_lt hac) htU.1, htU.2⟩
    exact maxOver_swap_key σ hca' hta' hcI htI hmax
  -- Step 1: for each t ∈ U, the events {t = max of U} within {all T maxima} are equiprobable
  -- via the swap c t bijection.
  have hEq : ∀ t ∈ U, (Finset.univ.filter (fun σ : PrioPerm n =>
        (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U t)).card =
      (Finset.univ.filter (fun σ : PrioPerm n =>
        (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U c)).card := by
    intro t htU
    apply Finset.card_bij (fun σ _ => σ * (Equiv.swap c t))
    · -- maps the t-set into the c-set
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      rcases hσ with ⟨hσu, ⟨hTσ, htmax⟩⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      constructor
      · intro a haT
        exact hTswap a haT t htU σ (hTσ a haT)
      · -- c is the max of U under σ * swap ct
        have hc' : MaxOver (σ * (Equiv.swap c t)) U c := by
          simpa [Equiv.swap_comm] using maxOver_swap_max (c := t) (t := c) σ htU hcU htmax
        exact hc'
    · -- injectivity
      intro σ₁ hσ₁ σ₂ hσ₂ h
      exact (swapComp'_bijective (c := c) (t := t)).1 h
    · -- surjectivity onto the c-set
      intro σ hσ
      rw [Finset.mem_filter] at hσ
      rcases hσ with ⟨hσu, ⟨hTσ, hcmax⟩⟩
      refine ⟨σ * (Equiv.swap c t), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        constructor
        · intro a haT
          exact hTswap a haT t htU σ (hTσ a haT)
        · -- t is the max of U under σ * swap ct
          exact maxOver_swap_max σ hcU htU hcmax
      · -- σ * swap * swap = σ
        simpa [mul_assoc]
  -- Step 2: the {t = max of U} events partition {all T maxima}.
  have hcover : (Finset.univ.filter (fun σ : PrioPerm n =>
        ∀ a ∈ T, MaxOver σ (Finset.Icc a b) a)) =
      Finset.biUnion U (fun t => Finset.univ.filter (fun σ : PrioPerm n =>
        (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U t)) := by
    apply Finset.Subset.antisymm
    · intro σ hσ
      rw [Finset.mem_filter] at hσ
      rcases hσ with ⟨hσu, hTσ⟩
      -- the max of U under σ is at some t ∈ U
      have hmaxU : ∃ t ∈ U, MaxOver σ U t := by
        have hUne : U.Nonempty := ⟨c, hcU⟩
        rcases Finset.exists_max_image U (prioOfPerm σ) hUne with ⟨m, hmU, hmax⟩
        refine ⟨m, hmU, ?_⟩
        exact ⟨hmU, hmax⟩
      rcases hmaxU with ⟨t, htU, htmax⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨t, htU, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hTσ, htmax⟩⟩⟩
    · intro σ hσ
      rw [Finset.mem_biUnion] at hσ
      rcases hσ with ⟨t, htU, hσt⟩
      rw [Finset.mem_filter] at hσt
      exact Finset.mem_filter.mpr ⟨hσt.1, hσt.2.1⟩
  -- Step 3: the {t = max of U} sets are pairwise disjoint
  have hdisj : ∀ t₁ ∈ U, ∀ t₂ ∈ U, t₁ ≠ t₂ →
      Disjoint (Finset.univ.filter (fun σ : PrioPerm n =>
          (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U t₁))
               (Finset.univ.filter (fun σ : PrioPerm n =>
          (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U t₂)) := by
    intro t₁ ht₁ t₂ ht₂ hne
    apply Finset.disjoint_filter.2
    intro σ _ h₁ h₂
    -- MaxOver σ U t₁ and MaxOver σ U t₂ imply t₁ = t₂ (unique max)
    have hu1 : MaxOver σ U t₁ := h₁.2
    have hu2 : MaxOver σ U t₂ := h₂.2
    -- uniqueness: MaxOver U t₁ ∧ MaxOver U t₂ → t₁ = t₂
    have ht1t2 : t₁ = t₂ := by
      have h12 : (σ t₂).1 ≤ (σ t₁).1 := hu1.2 t₂ ht₂
      have h21 : (σ t₁).1 ≤ (σ t₂).1 := hu2.2 t₁ ht₁
      have heq : (σ t₁).1 = (σ t₂).1 := le_antisymm h21 h12
      exact σ.injective (Fin.ext heq)
    exact hne ht1t2
  calc
    ((Finset.univ.filter (fun σ : PrioPerm n =>
        (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U c)).card) * U.card
        = (∑ t ∈ U, (Finset.univ.filter (fun σ : PrioPerm n =>
            (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U t)).card) := by
          rw [Finset.sum_congr rfl (fun t ht => hEq t ht)]
          rw [Finset.sum_const]
          simp [nsmul_eq_mul, mul_comm]
    _ = (Finset.biUnion U (fun t => Finset.univ.filter (fun σ : PrioPerm n =>
          (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) ∧ MaxOver σ U t))).card := by
          rw [← Finset.card_biUnion]
          · exact hdisj
    _ = (Finset.univ.filter (fun σ : PrioPerm n =>
          ∀ a ∈ T, MaxOver σ (Finset.Icc a b) a)).card := by rw [hcover]

lemma leftAncestors_product {n : ℕ} {b : Fin n} (S : Finset (Fin n))
    (hS : ∀ a ∈ S, a < b) :
    ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card : ℝ) =
      (Fintype.card (PrioPerm n) : ℝ) * ∏ a ∈ S, (1 / ((Finset.Icc a b).card : ℝ)) := by
  classical
  have hIH : ∀ m : ℕ, ∀ S : Finset (Fin n), S.card = m → (∀ a ∈ S, a < b) →
      ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card : ℝ) =
        (Fintype.card (PrioPerm n) : ℝ) * ∏ a ∈ S, (1 / ((Finset.Icc a b).card : ℝ)) := by
    intro m
    induction m with
    | zero =>
        intro S hcard hS
        have hSempty : S = ∅ := (Finset.card_eq_zero.mp hcard)
        subst S
        simp
    | succ m ih =>
        intro S hcard hS
        by_cases hempty : S = ∅
        · subst S
          simp
        · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
          let c : Fin n := S.max' hSne
          have hcS : c ∈ S := Finset.max'_mem S hSne
          have hcb : c < b := hS c hcS
          have hothers : ∀ a ∈ S.erase c, a < c := by
            intro a ha
            rw [Finset.mem_erase] at ha
            have hle : a ≤ c := Finset.le_max' S a ha.2
            exact lt_of_le_of_ne hle ha.1
          have hSsplit : Insert.insert c (S.erase c) = S := Finset.insert_erase hcS
          have hcard2 : (S.erase c).card = m := by
            have : (S.erase c).card = S.card - 1 := Finset.card_erase_of_mem hcS
            omega
          have hS2 : ∀ a ∈ S.erase c, a < b := by
            intro a ha
            rw [Finset.mem_erase] at ha
            exact hS a ha.2
          have hme := maxExtend_uniform (S.erase c) hothers hcb
          have hSsplit' : S = Insert.insert c (S.erase c) := hSsplit.symm
          have hcardId : (Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card *
              (Finset.Icc c b).card =
            (Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S.erase c, MaxOver σ (Finset.Icc a b) a)).card := by
            have hSetEq : (Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)) =
                (Finset.univ.filter (fun σ : PrioPerm n => (∀ a ∈ S.erase c, MaxOver σ (Finset.Icc a b) a) ∧
                  MaxOver σ (Finset.Icc c b) c)) := by
              ext σ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h
                constructor
                · intro a ha
                  rw [Finset.mem_erase] at ha
                  exact h a ha.2
                · exact h c hcS
              · intro h
                intro a ha
                by_cases hac : a = c
                · subst a
                  exact h.2
                · exact h.1 a (Finset.mem_erase.mpr ⟨hac, ha⟩)
            rw [hSetEq]
            simpa using hme
          have hcn0 : ((Finset.Icc c b).card : ℝ) ≠ 0 := by
            have hpos : 0 < (Finset.Icc c b).card := by
              have : c ∈ Finset.Icc c b := Finset.mem_Icc.mpr ⟨le_rfl, le_of_lt hcb⟩
              exact Finset.card_pos.mpr ⟨c, this⟩
            exact_mod_cast (ne_of_gt hpos)
          -- hcardId: |{all S}|·|[c,b]| = |{all S.erase c}|
          -- so |{all S}| = |{all S.erase c}|/|[c,b]|
          have hdiv : ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card : ℝ) =
              ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S.erase c, MaxOver σ (Finset.Icc a b) a)).card : ℝ) /
                ((Finset.Icc c b).card : ℝ) := by
            have hcardId' : ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card : ℝ) *
                ((Finset.Icc c b).card : ℝ) =
              ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S.erase c, MaxOver σ (Finset.Icc a b) a)).card : ℝ) := by
              exact_mod_cast hcardId
            exact (eq_div_iff hcn0).mpr hcardId'
          calc
            ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card : ℝ)
                = ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S.erase c, MaxOver σ (Finset.Icc a b) a)).card : ℝ) *
                    (1 / ((Finset.Icc c b).card : ℝ)) := by
                  rw [hdiv]
                  ring
            _ = (Fintype.card (PrioPerm n) : ℝ) * (∏ a ∈ S.erase c, (1 / ((Finset.Icc a b).card : ℝ))) *
                  (1 / ((Finset.Icc c b).card : ℝ)) := by
                  rw [ih (S.erase c) hcard2 hS2]
            _ = (Fintype.card (PrioPerm n) : ℝ) * (∏ a ∈ S, (1 / ((Finset.Icc a b).card : ℝ))) := by
                  rw [← hSsplit]
                  rw [Finset.prod_insert]
                  · rw [Finset.erase_insert (by simp)]
                    ring
                  · simp
  exact hIH S.card S rfl hS

/- `(n+1).choose n = n+1`. -/
private lemma choose_succ (n : ℕ) : Nat.choose (n + 1) n = n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      rw [ih, Nat.choose_self]

lemma eSymm_le {α : Type} [DecidableEq α] (C : Finset α) (x : α → ℝ)
    (hx : ∀ a, 0 ≤ x a) (k : ℕ) :
    (∑ s ∈ Finset.powersetCard k C, ∏ a ∈ s, x a) ≤
      (∑ a ∈ C, x a)^k / (Nat.factorial k : ℝ) := by
  classical
  let S : Finset α → ℝ := fun D => ∑ a ∈ D, x a
  let e : Finset α → ℕ → ℝ := fun D k => ∑ s ∈ Finset.powersetCard k D, ∏ a ∈ s, x a
  have hmain : ∀ D : Finset α, ∀ k : ℕ, e D k ≤ (S D)^k / (Nat.factorial k : ℝ) := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
        intro k
        by_cases hk : k = 0
        · subst k; simp [e, S]
        · have hpc : Finset.powersetCard k (∅ : Finset α) = ∅ := by
            ext s
            rw [Finset.mem_powersetCard]
            constructor
            · intro h
              have hs_empty : s = ∅ := Finset.subset_empty.mp h.1
              have hcard0 : s.card = 0 := by rw [hs_empty]; simp
              omega
            · intro h; simp at h
          have hS : S ∅ = 0 := by simp [S]
          have he : e ∅ k = 0 := by
            unfold e
            rw [hpc]
            simp
          rw [he, hS]
          have hz : (0 : ℝ)^k = 0 := zero_pow hk
          simp [hz]
    | @insert a D' haD ih =>
        intro k
        by_cases hk : k = 0
        · subst k
          simp [e, S]
        · -- k ≥ 1, write k = n+1
          have hkn : k = (k - 1) + 1 := by omega
          -- powersetCard (n+1) (insert a D') splits
          have hsplit : Finset.powersetCard k (Insert.insert a D') =
              Finset.powersetCard k D' ∪ Finset.image (Insert.insert a) (Finset.powersetCard (k - 1) D') := by
            rw [hkn]
            exact Finset.powersetCard_succ_insert haD (k - 1)
          have hdisj : Disjoint (Finset.powersetCard k D')
              (Finset.image (Insert.insert a) (Finset.powersetCard (k - 1) D')) := by
            -- one side has a, the other doesn't
            rw [Finset.disjoint_left]
            intro s hs hs2
            rw [Finset.mem_image] at hs2
            rcases hs2 with ⟨t, ht, hst⟩
            -- s ∈ powersetCard k D' (so a ∉ s since a ∉ D'), but s = insert a t ∋ a. Contradiction.
            have hsD : s ⊆ D' := (Finset.mem_powersetCard.mp hs).1
            have has : a ∈ s := by rw [← hst]; exact Finset.mem_insert_self a t
            have has' : a ∉ s := fun h => haD (hsD h)
            exact has' has
          -- e k (insert a D') = e k D' + x a * e (k-1) D'
          have he : e (Insert.insert a D') k = e D' k + x a * e D' (k - 1) := by
            unfold e
            rw [hsplit, Finset.sum_union hdisj]
            congr 1
            -- the image part
            rw [Finset.sum_image]
            · -- ∑_{t ∈ powersetCard (k-1) D'} ∏_{a' ∈ insert a t} x a' = x a · e D' (k-1)
              rw [show (∑ t ∈ Finset.powersetCard (k - 1) D', ∏ a' ∈ Insert.insert a t, x a') =
                  x a * (∑ t ∈ Finset.powersetCard (k - 1) D', ∏ a' ∈ t, x a') by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro t ht
                have hat : a ∉ t := fun h => haD ((Finset.mem_powersetCard.mp ht).1 h)
                rw [Finset.prod_insert hat]]
            · intro t₁ ht₁ t₂ ht₂ h
              -- insert a t₁ = insert a t₂ → t₁ = t₂ (since a ∉ t₁, t₂)
              have hat₁ : a ∉ t₁ := fun h' => haD ((Finset.mem_powersetCard.mp ht₁).1 h')
              have hat₂ : a ∉ t₂ := fun h' => haD ((Finset.mem_powersetCard.mp ht₂).1 h')
              have her : (Insert.insert a t₁).erase a = (Insert.insert a t₂).erase a := by
                rw [h]
              rw [Finset.erase_insert hat₁, Finset.erase_insert hat₂] at her
              exact her
          -- bound e D' k and e D' (k-1) by IH
          have ihk : e D' k ≤ (S D')^k / (Nat.factorial k : ℝ) := ih k
          have ihk1 : e D' (k - 1) ≤ (S D')^(k - 1) / (Nat.factorial (k - 1) : ℝ) := ih (k - 1)
          -- binomial inequality: (S D' + x a)^k ≥ (S D')^k + k·x a·(S D')^(k-1)
          have hbin : (S D')^k + (k : ℝ) * x a * (S D')^(k - 1) ≤ (S D' + x a)^k := by
            let t : ℕ → ℝ := fun m => (Nat.choose k m : ℝ) * (S D')^m * (x a)^(k - m)
            have htk : t k = (S D')^k := by
              unfold t
              rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self]
              ring
            have htk1 : t (k - 1) = (k : ℝ) * (S D')^(k - 1) * x a := by
              unfold t
              have hsub : k - (k - 1) = 1 := by omega
              rw [hsub, pow_one]
              have hc : (Nat.choose k (k - 1) : ℝ) = (k : ℝ) := by
                have : Nat.choose k (k - 1) = k := by
                  rcases k with _ | k'
                  · exfalso; exact hk rfl
                  · have : Nat.choose (k' + 1) (k' + 1 - 1) = k' + 1 := by
                      rw [show k' + 1 - 1 = k' by omega]
                      exact choose_succ k'
                    simpa using this
                exact_mod_cast this
              rw [hc]
            have hS_nonneg : 0 ≤ S D' := Finset.sum_nonneg (fun a ha => hx a)
            have hnonneg : ∀ m, 0 ≤ t m := by
              intro m
              unfold t
              exact mul_nonneg (mul_nonneg (by exact_mod_cast (Nat.zero_le (Nat.choose k m))) (pow_nonneg hS_nonneg m)) (pow_nonneg (hx a) (k - m))
            have hle : t k + t (k - 1) ≤ ∑ m ∈ Finset.range (k + 1), t m := by
              have hind : (∑ m ∈ Finset.range (k + 1), if m = k ∨ m = k - 1 then t m else 0) ≤
                  ∑ m ∈ Finset.range (k + 1), t m := by
                exact Finset.sum_le_sum (fun m hm => by
                  by_cases h : m = k ∨ m = k - 1
                  · simp [h]
                  · simp [h, hnonneg m])
              have hind' : (∑ m ∈ Finset.range (k + 1), if m = k ∨ m = k - 1 then t m else 0) = t k + t (k - 1) := by
                rw [show (∑ m ∈ Finset.range (k + 1), if m = k ∨ m = k - 1 then t m else 0) =
                    (∑ m ∈ Finset.range (k + 1), ((if m = k then t m else 0) + (if m = k - 1 then t m else 0))) by
                  apply Finset.sum_congr rfl
                  intro m hm
                  have hne : k ≠ k - 1 := by omega
                  by_cases h1 : m = k
                  · subst m; simp [hne]
                  · by_cases h2 : m = k - 1
                    · subst m
                      have hne' : k - 1 ≠ k := by omega
                      simp [hne']
                    · simp [h1, h2]]
                rw [Finset.sum_add_distrib]
                rw [Finset.sum_ite_eq']
                rw [Finset.sum_ite_eq']
                have hk1mem : k - 1 ∈ Finset.range (k + 1) := by
                  rw [Finset.mem_range]; omega
                have hkmem : k ∈ Finset.range (k + 1) := by simp
                simp [hk1mem, hkmem]
              rw [← hind']
              exact hind
            have hsum : (S D' + x a)^k = ∑ m ∈ Finset.range (k + 1), t m := by
              rw [add_pow]
              congr 1
              funext m
              simp [t]
              ring
            calc
              (S D')^k + (k : ℝ) * x a * (S D')^(k - 1) = t k + t (k - 1) := by
                rw [htk, htk1]; ring
              _ ≤ ∑ m ∈ Finset.range (k + 1), t m := hle
              _ = (S D' + x a)^k := hsum.symm
          -- assemble
          have hS' : S (Insert.insert a D') = S D' + x a := by
            unfold S
            rw [Finset.sum_insert haD]
            ring
          -- final
          calc
            e (Insert.insert a D') k = e D' k + x a * e D' (k - 1) := he
            _ ≤ (S D')^k / (Nat.factorial k : ℝ) + x a * ((S D')^(k - 1) / (Nat.factorial (k - 1) : ℝ)) := by
                  have hxa : 0 ≤ x a := hx a
                  nlinarith [ihk, ihk1, hxa]
            _ ≤ (S (Insert.insert a D'))^k / (Nat.factorial k : ℝ) := by
                  rw [hS']
                  -- need: S^k/k! + a·S^(k-1)/(k-1)! ≤ (S+a)^k/k!
                  -- ⟺ S^k + k·a·S^(k-1) ≤ (S+a)^k  (multiply by k!, using k! = k·(k-1)!)
                  have hfac : (Nat.factorial k : ℝ) = (k : ℝ) * (Nat.factorial (k - 1) : ℝ) := by
                    have hnfac : Nat.factorial k = k * Nat.factorial (k - 1) := by
                      rw [hkn]
                      rw [Nat.factorial_succ]
                      congr 1
                    exact_mod_cast hnfac
                  rw [hfac]
                  field_simp
                  nlinarith [hbin]
  exact hmain C k

lemma fintypeExpect_le {Ω : Type} [Fintype Ω] [DecidableEq Ω] (X Y : Ω → ℝ)
    (h : ∀ ω, X ω ≤ Y ω) : fintypeExpect X ≤ fintypeExpect Y := by
  unfold fintypeExpect
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => h ω)) (by positivity)

lemma leftAncestors_tail {n : ℕ} {b : Fin n} (k : ℕ) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ leftAncestors σ b)) ≤
      (∑ a : Fin n, if a < b then (1 / ((Finset.Icc a b).card : ℝ)) else 0)^k /
        (Nat.factorial k : ℝ) := by
  classical
  let C : Finset (Fin n) := Finset.univ.filter (fun a : Fin n => a < b)
  have hcov : ∀ σ, indicator (k ≤ leftAncestors σ b) ≤
      ∑ S ∈ Finset.powersetCard k C, indicator (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a) := by
    intro σ
    by_cases hk : k ≤ leftAncestors σ b
    · have hA : ∃ S ∈ Finset.powersetCard k C, ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a := by
        let A : Finset (Fin n) := C.filter (fun a => MaxOver σ (Finset.Icc a b) a)
        have hAcard : k ≤ A.card := by
          have hAeq : A.card = leftAncestors σ b := by
            unfold A leftAncestors C
            congr 1
            ext a
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · intro h
              rcases h with ⟨h1, h2⟩
              have hmm : Finset.Icc (min a b) (max a b) = Finset.Icc a b := by
                rw [min_eq_left (le_of_lt h1), max_eq_right (le_of_lt h1)]
              exact ⟨h1, (by
                unfold Ancestor
                right
                rw [hmm]
                exact h2.2)⟩
            · intro h
              rcases h with ⟨h1, h2⟩
              have hmm : Finset.Icc (min a b) (max a b) = Finset.Icc a b := by
                rw [min_eq_left (le_of_lt h1), max_eq_right (le_of_lt h1)]
              exact ⟨h1, (by
                unfold MaxOver
                unfold Ancestor at h2
                rcases h2 with h | hle
                · exfalso; exact (ne_of_lt h1) h
                · exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, le_of_lt h1⟩, (by rwa [hmm] at hle)⟩)⟩
          omega
        rcases Finset.exists_subset_card_eq hAcard with ⟨S, hSA, hScard⟩
        refine ⟨S, ?_, ?_⟩
        · exact Finset.mem_powersetCard.mpr ⟨(fun a ha => (Finset.mem_filter.mp (hSA ha)).1), hScard⟩
        · intro a ha
          exact (Finset.mem_filter.mp (hSA ha)).2
      have hrhs : 1 ≤ ∑ S ∈ Finset.powersetCard k C, indicator (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a) := by
        rcases hA with ⟨S, hS, hSanc⟩
        have hS1 : indicator (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a) = 1 := by
          simp [indicator]
          exact hSanc
        have hle1 : indicator (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a) ≤
            ∑ T ∈ Finset.powersetCard k C, indicator (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) := by
          have hnonneg : ∀ T ∈ Finset.powersetCard k C, 0 ≤ indicator (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) := by
            intro T hT
            by_cases hc : (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a)
            · have h1 : indicator (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) = 1 := by
                rw [indicator, if_pos hc]
              rw [h1]; norm_num
            · have h0 : indicator (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a) = 0 := by
                rw [indicator, if_neg hc]
              rw [h0]
          exact Finset.single_le_sum (s := Finset.powersetCard k C)
            (f := fun T => indicator (∀ a ∈ T, MaxOver σ (Finset.Icc a b) a))
            hnonneg (by exact hS)
        rw [hS1] at hle1
        exact hle1
      simpa [hk, hrhs]
    · have hzero : indicator (k ≤ leftAncestors σ b) = 0 := by
        rw [indicator, if_neg hk]
      rw [hzero]
      exact Finset.sum_nonneg (fun S hS => by
        by_cases hc : (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)
        · rw [indicator, if_pos hc]; norm_num
        · rw [indicator, if_neg hc])
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ leftAncestors σ b))
        ≤ fintypeExpect (fun σ : PrioPerm n => ∑ S ∈ Finset.powersetCard k C, indicator (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)) := by
          exact fintypeExpect_le _ _ hcov
    _ = ∑ S ∈ Finset.powersetCard k C, fintypeExpect (fun σ : PrioPerm n => indicator (∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)) := by
          rw [fintypeExpect_sum]
    _ = ∑ S ∈ Finset.powersetCard k C, ∏ a ∈ S, (1 / ((Finset.Icc a b).card : ℝ)) := by
          apply Finset.sum_congr rfl
          intro S hS
          have hS' : ∀ a ∈ S, a < b := by
            intro a ha
            have hSC : S ⊆ C := (Finset.mem_powersetCard.mp hS).1
            exact (Finset.mem_filter.mp (hSC ha)).2
          have hprod := leftAncestors_product S hS'
          unfold fintypeExpect indicator
          rw [Finset.sum_boole]
          rw [show (Fintype.card (PrioPerm n) : ℝ) = (Nat.factorial n : ℝ) by simp [PrioPerm, Fintype.card_perm]]
          have hnfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
          have hprod' : ((Finset.univ.filter (fun σ : PrioPerm n => ∀ a ∈ S, MaxOver σ (Finset.Icc a b) a)).card : ℝ) =
              (Nat.factorial n : ℝ) * ∏ a ∈ S, (1 / ((Finset.Icc a b).card : ℝ)) := by
            rw [show (Fintype.card (PrioPerm n) : ℝ) = (Nat.factorial n : ℝ) by simp [PrioPerm, Fintype.card_perm]] at hprod
            exact hprod
          field_simp [hnfac]
          exact hprod'
    _ ≤ (∑ a ∈ C, (1 / ((Finset.Icc a b).card : ℝ)))^k / (Nat.factorial k : ℝ) := by
          exact eSymm_le C (fun a => 1 / ((Finset.Icc a b).card : ℝ)) (by intro a; positivity) k
    _ = (∑ a : Fin n, if a < b then (1 / ((Finset.Icc a b).card : ℝ)) else 0)^k / (Nat.factorial k : ℝ) := by
          congr 1
          unfold C
          rw [Finset.sum_filter]

-- The left-ancestor sum over the interval reciprocals is at most H_n.
lemma left_sum_le_harmonicReal {n : ℕ} {b : Fin n} :
    (∑ a : Fin n, if a < b then (1 / ((Finset.Icc a b).card : ℝ)) else 0) ≤ harmonicReal n := by
  classical
  have hconv : (∑ a : Fin n, if a < b then (1 / ((Finset.Icc a b).card : ℝ)) else 0) =
      (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else 0) := by
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hab : a < b
    · have hcard : (Finset.Icc a b).card = b.val - a.val + 1 := by
        have hab' : a.val < b.val := hab
        rw [Fin.card_Icc]
        omega
      simp [hab, hcard, one_div]
    · simp [hab]
  rw [hconv]
  calc
    (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else 0)
        = (∑ i ∈ Finset.range n, if i < b.val then (((b.val - i + 1 : ℕ) : ℝ)⁻¹) else 0) := by
          rw [sum_fin_eq_range b]
    _ ≤ harmonicReal n - 1 := by
          have hn1 : 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le b.val) b.isLt)
          exact below_sum_le_harmonic_val (n := n) (b := b.val) hn1 b.isLt
    _ ≤ harmonicReal n := by linarith

/-! ## Right-ancestor tail via reflection -/

/-- Right-composition with the order-reversing involution {lit}`Fin.revPerm` is
an involution (hence a bijection) on {lit}`PrioPerm n`. -/
noncomputable def revCompEquiv {n : ℕ} : PrioPerm n ≃ PrioPerm n where
  toFun σ := σ * Fin.revPerm
  invFun σ := σ * Fin.revPerm
  left_inv := by
    intro σ
    ext x
    simp [Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev]
  right_inv := by
    intro σ
    ext x
    simp [Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev]

/-- The ancestor relation commutes with order reversal: for {lit}`b < a`, the
key {lit}`a` is an ancestor of {lit}`b` under {lit}`σ` iff the reversed key is
an ancestor of the reversed key under {lit}`σ * Fin.revPerm`. -/
lemma ancestor_rev_perm {n : ℕ} {σ : PrioPerm n} {a b : Fin n} (hab : b < a) :
    Ancestor (σ * Fin.revPerm) (Fin.revPerm a) (Fin.revPerm b) ↔ Ancestor σ a b := by
  classical
  have hane : a ≠ b := ne_of_gt hab
  have hne' : Fin.revPerm a ≠ Fin.revPerm b := by
    intro h
    exact hane (Fin.revPerm.injective h)
  have hra : Fin.revPerm a < Fin.revPerm b := by
    simpa [Fin.revPerm_apply] using (Fin.rev_lt_rev (i := a) (j := b)).2 hab
  have hmin1 : min (Fin.revPerm a) (Fin.revPerm b) = Fin.revPerm a := min_eq_left (le_of_lt hra)
  have hmax1 : max (Fin.revPerm a) (Fin.revPerm b) = Fin.revPerm b := max_eq_right (le_of_lt hra)
  have hmin2 : min a b = b := min_eq_right (le_of_lt hab)
  have hmax2 : max a b = a := max_eq_left (le_of_lt hab)
  unfold Ancestor
  rw [hmin1, hmax1, hmin2, hmax2]
  simp only [hne', hane, or_false, false_or]
  constructor
  · intro h k hk
    have hk' : Fin.revPerm k ∈ Finset.Icc (Fin.revPerm a) (Fin.revPerm b) := by
      rw [Finset.mem_Icc] at hk ⊢
      rcases hk with ⟨hbk, hka⟩
      constructor
      · exact (Fin.rev_le_rev (i := a) (j := k)).2 hka
      · exact (Fin.rev_le_rev (i := k) (j := b)).2 hbk
    have hp := h (Fin.revPerm k) hk'
    simpa [prioOfPerm, Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev] using hp
  · intro h k hk
    have hk' : Fin.revPerm k ∈ Finset.Icc b a := by
      rw [Finset.mem_Icc] at hk ⊢
      rcases hk with ⟨hrak, hkrb⟩
      constructor
      · simpa [Fin.revPerm_apply] using (Fin.le_rev_iff (i := k) (j := b)).1 hkrb
      · simpa [Fin.revPerm_apply] using (Fin.rev_le_iff (i := a) (j := k)).1 hrak
    have hp := h (Fin.revPerm k) hk'
    simpa [prioOfPerm, Equiv.Perm.mul_apply, Fin.revPerm_apply, Fin.rev_rev] using hp

/-- The right-ancestors of {lit}`b` are exactly the left-ancestors of the
reversed key under the reflected permutation. -/
lemma rightAncestors_eq_left_rev {n : ℕ} (σ : PrioPerm n) (b : Fin n) :
    rightAncestors σ b = leftAncestors (σ * Fin.revPerm) (Fin.revPerm b) := by
  classical
  unfold rightAncestors leftAncestors
  apply Finset.card_nbij (fun a => Fin.revPerm a)
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rcases ha with ⟨hba, hanc⟩
    constructor
    · simpa [Fin.revPerm_apply] using (Fin.rev_lt_rev (i := a) (j := b)).2 hba
    · exact (ancestor_rev_perm hba).2 hanc
  · intro a₁ ha₁ a₂ ha₂ h
    exact Fin.revPerm.injective h
  · intro b' hb'
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hb'
    rcases hb' with ⟨hb'l, hanc'⟩
    refine ⟨Fin.revPerm b', ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · simpa [Fin.revPerm_apply] using (Fin.lt_rev_iff (i := b) (j := b')).2 hb'l
      · refine (ancestor_rev_perm (a := Fin.revPerm b') (b := b) ?_).1 ?_
        · simpa [Fin.revPerm_apply] using (Fin.lt_rev_iff (i := b) (j := b')).2 hb'l
        · simpa [Fin.revPerm_apply, Fin.rev_rev] using hanc'
    · simp [Fin.revPerm_apply, Fin.rev_rev]

/-- If {lit}`S ≤ H_n` and {lit}`S ≥ 0`, then {lit}`S^k/k! ≤ H_n^k/k!`. -/
private lemma harmonic_pow_div_le {n : ℕ} (k : ℕ) (S : ℝ)
    (hS : S ≤ harmonicReal n) (hS0 : 0 ≤ S) :
    S^k / (Nat.factorial k : ℝ) ≤ (harmonicReal n)^k / (Nat.factorial k : ℝ) := by
  have hH0 : 0 ≤ harmonicReal n := by
    unfold harmonicReal
    exact Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (by positivity))
  have hpow : S^k ≤ (harmonicReal n)^k := pow_le_pow_left₀ hS0 hS k
  exact div_le_div_of_nonneg_right hpow (by positivity)

/-- The probability that key {lit}`b` has at least {lit}`k` left-ancestors is
at most {lit}`H_n^k / k!`. -/
lemma leftAncestors_tail_le_harmonic {n : ℕ} {b : Fin n} (k : ℕ) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ leftAncestors σ b)) ≤
      (harmonicReal n)^k / (Nat.factorial k : ℝ) := by
  classical
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ leftAncestors σ b)) ≤
      (∑ a : Fin n, if a < b then (1 / ((Finset.Icc a b).card : ℝ)) else 0)^k /
        (Nat.factorial k : ℝ) := by
          exact leftAncestors_tail (b := b) k
    _ ≤ (harmonicReal n)^k / (Nat.factorial k : ℝ) := by
          exact harmonic_pow_div_le k _ (left_sum_le_harmonicReal (n := n) (b := b)) (by
            exact Finset.sum_nonneg (fun a ha => by
              by_cases h : a < b
              · rw [if_pos h]; positivity
              · rw [if_neg h]))

/-- The probability that key {lit}`b` has at least {lit}`k` right-ancestors is
at most {lit}`H_n^k / k!`. -/
lemma rightAncestors_tail_le_harmonic {n : ℕ} {b : Fin n} (k : ℕ) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ rightAncestors σ b)) ≤
      (harmonicReal n)^k / (Nat.factorial k : ℝ) := by
  classical
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ rightAncestors σ b))
        = fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ leftAncestors (σ * Fin.revPerm) (Fin.revPerm b))) := by
          congr 1
          funext σ
          simpa [rightAncestors_eq_left_rev σ b]
    _ = fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ leftAncestors σ (Fin.revPerm b))) := by
          exact fintypeExpect_equiv (revCompEquiv)
            (fun σ : PrioPerm n => indicator (k ≤ leftAncestors σ (Fin.revPerm b)))
    _ ≤ (∑ a : Fin n, if a < Fin.revPerm b then (1 / ((Finset.Icc a (Fin.revPerm b)).card : ℝ)) else 0)^k /
          (Nat.factorial k : ℝ) := by
          exact leftAncestors_tail (b := Fin.revPerm b) k
    _ ≤ (harmonicReal n)^k / (Nat.factorial k : ℝ) := by
          exact harmonic_pow_div_le k _ (left_sum_le_harmonicReal (n := n) (b := Fin.revPerm b)) (by
            exact Finset.sum_nonneg (fun a ha => by
              by_cases h : a < Fin.revPerm b
              · rw [if_pos h]; positivity
              · rw [if_neg h]))

/-! ## Depth tail -/

/-- The probability that the depth of key {lit}`b` is at least {lit}`k` is at
most {lit}`2 · H_n^t / t!` where {lit}`t = (k - 1) / 2`.  Depth splits into
left-ancestors plus right-ancestors plus itself, so {lit}`depth ≥ k` forces at
least one side to carry at least {lit}`t` ancestors; each side has an
exponential tail. -/
lemma depth_tail {n : ℕ} (b : Fin n) (k : ℕ) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ depth σ b)) ≤
      2 * (harmonicReal n)^((k - 1) / 2) / (Nat.factorial ((k - 1) / 2) : ℝ) := by
  classical
  let t : ℕ := (k - 1) / 2
  have hcov : ∀ σ, indicator (k ≤ depth σ b) ≤
      indicator (t ≤ leftAncestors σ b) + indicator (t ≤ rightAncestors σ b) := by
    intro σ
    by_cases hk : k ≤ depth σ b
    · have hsome : t ≤ leftAncestors σ b ∨ t ≤ rightAncestors σ b := by
        by_contra hnone
        have hLt : leftAncestors σ b < t := Nat.lt_of_not_ge (fun h => hnone (Or.inl h))
        have hRt : rightAncestors σ b < t := Nat.lt_of_not_ge (fun h => hnone (Or.inr h))
        have h2t : 2 * t ≤ k := by dsimp [t]; omega
        have hbad : depth σ b < k := by
          rw [depth_eq_left_add_right σ b]
          omega
        exact (not_le_of_gt hbad) hk
      rw [indicator, if_pos hk]
      rcases hsome with hL | hR
      · have h1 : indicator (t ≤ leftAncestors σ b) = 1 := by rw [indicator, if_pos hL]
        rw [h1]
        have hR0 : 0 ≤ indicator (t ≤ rightAncestors σ b) := by
          unfold indicator
          by_cases h : t ≤ rightAncestors σ b <;> simp [h]
        linarith
      · have h1 : indicator (t ≤ rightAncestors σ b) = 1 := by rw [indicator, if_pos hR]
        rw [h1]
        have hL0 : 0 ≤ indicator (t ≤ leftAncestors σ b) := by
          unfold indicator
          by_cases h : t ≤ leftAncestors σ b <;> simp [h]
        linarith
    · rw [indicator, if_neg hk]
      have hR0 : 0 ≤ indicator (t ≤ rightAncestors σ b) := by
        unfold indicator
        by_cases h : t ≤ rightAncestors σ b <;> simp [h]
      have hL0 : 0 ≤ indicator (t ≤ leftAncestors σ b) := by
        unfold indicator
        by_cases h : t ≤ leftAncestors σ b <;> simp [h]
      linarith
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ depth σ b))
        ≤ fintypeExpect (fun σ : PrioPerm n => indicator (t ≤ leftAncestors σ b) + indicator (t ≤ rightAncestors σ b)) := by
          exact fintypeExpect_le _ _ hcov
    _ = fintypeExpect (fun σ : PrioPerm n => indicator (t ≤ leftAncestors σ b)) +
        fintypeExpect (fun σ : PrioPerm n => indicator (t ≤ rightAncestors σ b)) := by
          rw [fintypeExpect_add]
    _ ≤ (harmonicReal n)^t / (Nat.factorial t : ℝ) + (harmonicReal n)^t / (Nat.factorial t : ℝ) := by
          have hL := leftAncestors_tail_le_harmonic (b := b) t
          have hR := rightAncestors_tail_le_harmonic (b := b) t
          nlinarith
    _ = 2 * (harmonicReal n)^t / (Nat.factorial t : ℝ) := by ring


/-- `k! ≥ 2^(k-1)` for `k ≥ 1`, as reals. -/
private lemma factorial_ge_two_pow (k : ℕ) (hk : 1 ≤ k) :
    (2 : ℝ)^(k - 1) ≤ (k.factorial : ℝ) := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k; norm_num
      · have hk1 : 1 ≤ k := by omega
        have ih' : (2 : ℝ)^(k - 1) ≤ (k.factorial : ℝ) := ih hk1
        calc
          (2 : ℝ)^((k + 1) - 1) = (2 : ℝ)^k := by rw [show (k + 1) - 1 = k by omega]
          _ = (2 : ℝ) * (2 : ℝ)^(k - 1) := by
                have hpow : (2 : ℝ)^k = (2 : ℝ)^(k - 1) * 2 := by
                  rw [show k = (k - 1) + 1 by omega]
                  rw [pow_add]
                  norm_num
                rw [hpow]
                ring
          _ ≤ (k + 1 : ℝ) * (2 : ℝ)^(k - 1) := by
                have hk2 : 2 ≤ (k + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ hk1)
                exact mul_le_mul_of_nonneg_right hk2 (by positivity)
          _ ≤ (k + 1 : ℝ) * (k.factorial : ℝ) := by
                exact mul_le_mul_of_nonneg_left ih' (by positivity)
          _ = ((k + 1 : ℕ).factorial : ℝ) := by
                rw [Nat.factorial_succ]
                norm_num

/-- The tail `Σ_{i<m} (1/2)^i ≤ 2`. -/
private lemma geom_sum_inv_two_le (m : ℕ) :
    (∑ i ∈ Finset.range m, ((1 : ℝ) / 2)^i) ≤ 2 := by
  have hmul := geom_sum_mul_neg ((1 : ℝ) / 2) m
  have hsum_le : (∑ i ∈ Finset.range m, ((1 : ℝ) / 2)^i) * (1 - (1 : ℝ) / 2) ≤ 1 := by
    rw [hmul]
    have hpow0 : 0 ≤ ((1 : ℝ) / 2)^m := by positivity
    linarith
  have hstep : (∑ i ∈ Finset.range m, ((1 : ℝ) / 2)^i) * (1 - (1 : ℝ) / 2) ≤ 2 * (1 - (1 : ℝ) / 2) := by
    have h2 : 2 * (1 - (1 : ℝ) / 2) = 1 := by norm_num
    rw [h2]
    exact hsum_le
  have hhalf : (0 : ℝ) < 1 - (1 : ℝ) / 2 := by norm_num
  exact le_of_mul_le_mul_right hstep hhalf

/-- `Σ_{k=0}^{n} 1/k! ≤ 3`. -/
private lemma sum_inv_factorial_le_three (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ)) ≤ 3 := by
  have hsplit : (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ)) =
      (1 : ℝ) + ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1).factorial : ℝ) := by
    rw [Finset.sum_range_succ']
    rw [add_comm]
    norm_num
  rw [hsplit]
  have hb : (∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1).factorial : ℝ)) ≤
      (∑ k ∈ Finset.range n, ((1 : ℝ) / 2)^k) := by
    apply Finset.sum_le_sum
    intro k hk
    have hf := factorial_ge_two_pow (k + 1) (by omega)
    have hf2 : (2 : ℝ)^k ≤ ((k + 1).factorial : ℝ) := by simpa [Nat.succ_eq_add_one] using hf
    have hf' : (1 : ℝ) / ((k + 1).factorial : ℝ) ≤ ((1 : ℝ) / 2)^k := by
      have hfac0 : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
      have h2pos : (0 : ℝ) < (2 : ℝ)^k := by positivity
      have hle := (inv_le_inv₀ hfac0 h2pos).mpr hf2
      rw [one_div, one_div]
      simpa [inv_pow] using hle
    exact hf'
  calc
    (1 : ℝ) + ∑ k ∈ Finset.range n, (1 : ℝ) / ((k + 1).factorial : ℝ)
        ≤ (1 : ℝ) + ∑ k ∈ Finset.range n, ((1 : ℝ) / 2)^k := by
          nlinarith [hb]
    _ ≤ 3 := by
          have hgeom : (∑ k ∈ Finset.range n, ((1 : ℝ) / 2)^k) ≤ 2 := geom_sum_inv_two_le n
          nlinarith

/-- `(1 + 1/n)^n ≤ 3` for `n ≥ 1`. -/
private lemma one_add_one_div_pow_le_three (n : ℕ) (hn : 1 ≤ n) :
    ((1 : ℝ) + (1 : ℝ) / n)^n ≤ 3 := by
  have hnz : (n : ℝ) ≠ 0 := by positivity
  calc
    ((1 : ℝ) + (1 : ℝ) / n)^n
        = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((1 : ℝ) / n)^k) := by
          rw [add_comm (1 : ℝ)]
          rw [add_pow]
          simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ (∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (k.factorial : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          have hck : (n.choose k : ℝ) * (k.factorial : ℝ) ≤ (n : ℝ)^k := by
            have hc := Nat.choose_le_pow_div (α := ℝ) k n
            have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
            rwa [le_div_iff₀ hf] at hc
          have hnpos : (0 : ℝ) < (n : ℝ)^k := pow_pos (by positivity) k
          have hf : (0 : ℝ) < (k.factorial : ℝ) := by positivity
          have hck' : (n.choose k : ℝ) / (n : ℝ)^k ≤ (1 : ℝ) / (k.factorial : ℝ) := by
            exact (div_le_div_iff₀ hnpos hf).2 (by simpa using hck)
          have hcv : (n.choose k : ℝ) * ((1 : ℝ) / n)^k = (n.choose k : ℝ) / (n : ℝ)^k := by
            have hpow : ((1 : ℝ) / n)^k = (1 : ℝ) / (n : ℝ)^k := by
              rw [one_div, inv_pow, one_div]
            rw [hpow]
            field_simp [hnz]
          rw [hcv]
          exact hck'
    _ ≤ 3 := sum_inv_factorial_le_three n

/-- `t^t / t! ≤ 3^t` for `t ≥ 1`. -/
private lemma pow_div_factorial_le_three (t : ℕ) (ht : 1 ≤ t) :
    (t : ℝ)^t / (t.factorial : ℝ) ≤ (3 : ℝ)^t := by
  have hle : (t : ℝ)^t ≤ (t.factorial : ℝ) * (3 : ℝ)^t := by
    induction t with
    | zero => omega
    | succ t ih =>
        by_cases ht0 : t = 0
        · subst t; norm_num
        · have ht1 : 1 ≤ t := by omega
          have ht0' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) ht1)
          have ih' : (t : ℝ)^t ≤ (t.factorial : ℝ) * (3 : ℝ)^t := ih ht1
          have hone : ((1 : ℝ) + (1 : ℝ) / t)^t ≤ 3 := one_add_one_div_pow_le_three t ht1
          have hone_nonneg : 0 ≤ ((1 : ℝ) + (1 : ℝ) / t)^t := by
            have h1t : 0 ≤ (1 : ℝ) / t := div_nonneg (by norm_num) (le_of_lt ht0')
            exact pow_nonneg (by linarith) t
          have htz : (t : ℝ) ≠ 0 := by positivity
          calc
            ((t + 1 : ℕ) : ℝ)^(t + 1) = ((t : ℝ) + 1)^(t + 1) := by norm_num
            _ = ((t : ℝ) + 1) * ((t : ℝ) + 1)^t := by rw [pow_succ]; ring
            _ = ((t : ℝ) + 1) * ((t : ℝ)^t * ((1 : ℝ) + (1 : ℝ) / t)^t) := by
                  congr 1
                  rw [← mul_pow]
                  congr 1
                  field_simp [htz]
            _ ≤ ((t : ℝ) + 1) * ((t.factorial : ℝ) * (3 : ℝ)^t * 3) := by
                  have hprod : (t : ℝ)^t * ((1 : ℝ) + (1 : ℝ) / t)^t ≤
                      (t.factorial : ℝ) * (3 : ℝ)^t * 3 := by
                    have h1 : (t : ℝ)^t * ((1 : ℝ) + (1 : ℝ) / t)^t ≤
                        (t.factorial : ℝ) * (3 : ℝ)^t * ((1 : ℝ) + (1 : ℝ) / t)^t := by
                      exact mul_le_mul_of_nonneg_right ih' hone_nonneg
                    have h2 : (t.factorial : ℝ) * (3 : ℝ)^t * ((1 : ℝ) + (1 : ℝ) / t)^t ≤
                        (t.factorial : ℝ) * (3 : ℝ)^t * 3 := by
                      have hf3 : 0 ≤ (t.factorial : ℝ) * (3 : ℝ)^t := by positivity
                      exact mul_le_mul_of_nonneg_left hone hf3
                    exact le_trans h1 h2
                  have hpos : 0 ≤ (t : ℝ) + 1 := by positivity
                  exact mul_le_mul_of_nonneg_left hprod hpos
            _ = ((t + 1 : ℕ).factorial : ℝ) * (3 : ℝ)^(t + 1) := by
                  rw [Nat.factorial_succ]
                  norm_num
                  ring
  have hfac0 : (0 : ℝ) < (t.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hfac0]
  calc
    (t : ℝ)^t ≤ (t.factorial : ℝ) * (3 : ℝ)^t := hle
    _ = (3 : ℝ)^t * (t.factorial : ℝ) := by ring



/-- `n ≤ exp(H_n)`, from `log(n+1) ≤ H_n`. -/
private lemma nat_le_exp_harmonicReal {n : ℕ} : (n : ℝ) ≤ Real.exp (harmonicReal n) := by
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤ harmonicReal n := by
    have h := log_add_one_le_harmonic n
    rw [← harmonicReal_eq_harmonic] at h
    exact h
  have hpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  calc
    (n : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.le_succ n)
    _ = Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) := by rw [Real.exp_log hpos]
    _ ≤ Real.exp (harmonicReal n) := by exact Real.exp_le_exp.mpr hlog

/-- `(n²)·(1/2)^(6·Kh) ≤ 1` when `H_n ≤ Kh`. -/
private lemma n_sq_mul_inv_pow_le_one {n : ℕ} (Kh : ℕ) (hH : harmonicReal n ≤ (Kh : ℝ)) :
    (n : ℝ)^2 * ((1 : ℝ) / 2)^(6 * Kh) ≤ 1 := by
  have hn : (n : ℝ) ≤ Real.exp (harmonicReal n) := nat_le_exp_harmonicReal
  have hpos : (0 : ℝ) ≤ Real.exp (harmonicReal n) := (Real.exp_pos (harmonicReal n)).le
  have hsq : (n : ℝ)^2 ≤ (Real.exp (harmonicReal n))^2 := by nlinarith
  have hsq' : (n : ℝ)^2 ≤ Real.exp (2 * harmonicReal n) := by
    have h : (Real.exp (harmonicReal n))^2 = Real.exp (2 * harmonicReal n) := by
      rw [pow_two]
      rw [← Real.exp_add]
      ring_nf
    rw [h] at hsq
    exact hsq
  have hExp2 : Real.exp (2 * harmonicReal n) ≤ Real.exp (2 * (Kh : ℝ)) := by
    exact Real.exp_le_exp.mpr (by nlinarith [hH])
  have hExpKh : Real.exp (2 * (Kh : ℝ)) = (Real.exp 2)^Kh := by
    rw [show (2 : ℝ) * (Kh : ℝ) = (Kh : ℝ) * 2 by ring]
    rw [Real.exp_nat_mul]
  have hbase : Real.exp 2 * ((1 : ℝ) / 2)^6 ≤ 1 := by
    have h2 : Real.exp 2 < 64 := by
      have h1 : Real.exp 1 < 3 := by exact lt_trans Real.exp_one_lt_d9 (by norm_num)
      calc
        Real.exp 2 = Real.exp (1 + 1) := by norm_num
        _ = Real.exp 1 * Real.exp 1 := by rw [Real.exp_add]
        _ < 9 := by nlinarith [h1, (Real.exp_pos 1)]
        _ < 64 := by norm_num
    have h6 : ((1 : ℝ) / 2)^6 = (1 : ℝ) / 64 := by norm_num
    rw [h6]
    have hd : Real.exp 2 * (1 / 64) = Real.exp 2 / 64 := by ring
    rw [hd]
    have hle : Real.exp 2 ≤ 64 := le_of_lt h2
    have h64 : (0 : ℝ) < 64 := by norm_num
    rw [div_le_one₀ h64]
    exact hle
  calc
    (n : ℝ)^2 * ((1 : ℝ) / 2)^(6 * Kh) ≤ Real.exp (2 * harmonicReal n) * ((1 : ℝ) / 2)^(6 * Kh) := by
      exact mul_le_mul_of_nonneg_right hsq' (by positivity)
    _ ≤ Real.exp (2 * (Kh : ℝ)) * ((1 : ℝ) / 2)^(6 * Kh) := by
      exact mul_le_mul_of_nonneg_right hExp2 (by positivity)
    _ = (Real.exp 2)^Kh * ((1 : ℝ) / 2)^(6 * Kh) := by rw [hExpKh]
    _ = (Real.exp 2 * ((1 : ℝ) / 2)^6)^Kh := by
      rw [pow_mul]
      rw [← mul_pow]
    _ ≤ 1 := by
      have hb0 : 0 ≤ Real.exp 2 * ((1 : ℝ) / 2)^6 := by positivity
      exact pow_le_one₀ hb0 hbase

/-- The depth of a key is at most `n`. -/
lemma depth_le_n {n : ℕ} (σ : PrioPerm n) (b : Fin n) : depth σ b ≤ n := by
  classical
  unfold depth
  simpa using Finset.card_le_univ (s := Finset.univ.filter (fun a : Fin n => Ancestor σ a b))

/-- The height of a treap is at most `n`. -/
lemma treapHeight_le_n {n : ℕ} (σ : PrioPerm n) : treapHeight σ ≤ n := by
  unfold treapHeight
  exact Finset.sup_le (fun b hb => depth_le_n σ b)

/-- A natural `h ≤ n` is the number of `k ∈ [1, n]` with `k ≤ h`. -/
private lemma nat_eq_sum_indicator {h n : ℕ} (hh : h ≤ n) :
    (h : ℝ) = ∑ k ∈ Finset.Icc 1 n, indicator (k ≤ h) := by
  classical
  have hboole : (∑ k ∈ Finset.Icc 1 n, indicator (k ≤ h)) = ((Finset.Icc 1 n).filter (fun k => k ≤ h)).card := by
    simp [indicator]
  have hset : (Finset.Icc 1 n).filter (fun k => k ≤ h) = Finset.Icc 1 h := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hk
      rcases hk with ⟨hk1, hk2⟩
      rcases hk1 with ⟨hk1a, hk1b⟩
      exact ⟨hk1a, hk2⟩
    · intro hk
      rcases hk with ⟨hk1, hk2⟩
      constructor
      · constructor <;> omega
      · exact hk2
  rw [hboole, hset, Nat.card_Icc]
  congr 1

/-- `E[height]` equals the tail-sum `Σ_{k=1}^{n} P[height ≥ k]`. -/
lemma expectedTreapHeight_eq_sum {n : ℕ} :
    expectedTreapHeight (n := n) =
      ∑ k ∈ Finset.Icc 1 n, fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ treapHeight σ)) := by
  classical
  unfold expectedTreapHeight
  have hred : (fun σ : PrioPerm n => (treapHeight σ : ℝ)) =
      fun σ : PrioPerm n => ∑ k ∈ Finset.Icc 1 n, indicator (k ≤ treapHeight σ) := by
    funext σ
    exact nat_eq_sum_indicator (treapHeight_le_n σ)
  rw [hred]
  rw [fintypeExpect_sum]

/-- Union bound: `P[height ≥ k] ≤ Σ_b P[depth(b) ≥ k]`. -/
lemma height_tail {n : ℕ} (k : ℕ) (hk1 : 1 ≤ k) :
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ treapHeight σ)) ≤
      (n : ℝ) * (2 * (harmonicReal n)^((k - 1) / 2) / (Nat.factorial ((k - 1) / 2) : ℝ)) := by
  classical
  have hcov : ∀ σ, indicator (k ≤ treapHeight σ) ≤
      ∑ b : Fin n, indicator (k ≤ depth σ b) := by
    intro σ
    by_cases hk : k ≤ treapHeight σ
    · rw [indicator, if_pos hk]
      have hex : ∃ b : Fin n, k ≤ depth σ b := by
        by_contra hnone
        have hall : ∀ b : Fin n, depth σ b < k := by
          intro b
          exact Nat.lt_of_not_ge (fun h => hnone ⟨b, h⟩)
        have hle : treapHeight σ ≤ k - 1 := by
          unfold treapHeight
          exact Finset.sup_le (fun b hb => Nat.le_sub_one_of_lt (hall b))
        omega
      rcases hex with ⟨b, hb⟩
      have h1 : indicator (k ≤ depth σ b) = 1 := by rw [indicator, if_pos hb]
      have hnonneg : ∀ b' ∈ (Finset.univ : Finset (Fin n)), 0 ≤ indicator (k ≤ depth σ b') := by
        intro b' hb'
        by_cases h : k ≤ depth σ b' <;> simp [indicator, h]
      have hle1 : (1 : ℝ) ≤ ∑ b' : Fin n, indicator (k ≤ depth σ b') := by
        have hle := Finset.single_le_sum hnonneg (Finset.mem_univ b)
        rwa [h1] at hle
      exact hle1
    · rw [indicator, if_neg hk]
      exact Finset.sum_nonneg (fun b hb => by by_cases h : k ≤ depth σ b <;> simp [indicator, h])
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ treapHeight σ))
        ≤ fintypeExpect (fun σ : PrioPerm n => ∑ b : Fin n, indicator (k ≤ depth σ b)) := by
          exact fintypeExpect_le _ _ hcov
    _ = ∑ b : Fin n, fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ depth σ b)) := by
          rw [fintypeExpect_sum]
    _ ≤ ∑ b : Fin n, (2 * (harmonicReal n)^((k - 1) / 2) / (Nat.factorial ((k - 1) / 2) : ℝ)) := by
          apply Finset.sum_le_sum
          intro b hb
          exact depth_tail b k
    _ = (n : ℝ) * (2 * (harmonicReal n)^((k - 1) / 2) / (Nat.factorial ((k - 1) / 2) : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          simp [nsmul_eq_mul]



/-- `H^t / t! ≤ (1/2)^t` when `t ≥ 6H` and `H ≥ 0`. -/
private lemma pow_div_factorial_le_inv_two {H : ℝ} (t : ℕ) (ht1 : 1 ≤ t) (hH0 : 0 ≤ H)
    (ht6 : (t : ℝ) ≥ 6 * H) : H^t / (t.factorial : ℝ) ≤ ((1 : ℝ) / 2)^t := by
  have hf := pow_div_factorial_le_three t ht1
  have htz : (t : ℝ) ≠ 0 := by positivity
  have htpos : (0 : ℝ) < (t : ℝ) := by positivity
  have hHt0 : 0 ≤ H / t := div_nonneg hH0 (le_of_lt htpos)
  have hpow0 : 0 ≤ (H / t)^t := pow_nonneg hHt0 t
  have h1 : H^t / (t.factorial : ℝ) ≤ (3 * H / t)^t := by
    calc
      H^t / (t.factorial : ℝ) = (H / t)^t * (t : ℝ)^t / (t.factorial : ℝ) := by
        have h : (H / t)^t * (t : ℝ)^t = H^t := by
          rw [← mul_pow]
          congr 1
          field_simp [htz]
        rw [h]
      _ = (H / t)^t * ((t : ℝ)^t / (t.factorial : ℝ)) := by ring
      _ ≤ (H / t)^t * (3 : ℝ)^t := by
        exact mul_le_mul_of_nonneg_left hf hpow0
      _ = (3 * H / t)^t := by
        rw [← mul_pow]
        congr 1
        field_simp [htz]
  have hdiv : 3 * H / t ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ htpos]
    have h2 : (1 : ℝ) / 2 * (t : ℝ) = (t : ℝ) / 2 := by ring
    rw [h2]
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith [ht6])
  have hdiv0 : 0 ≤ 3 * H / t := div_nonneg (mul_nonneg (by norm_num) hH0) (le_of_lt htpos)
  have hpow : (3 * H / t)^t ≤ ((1 : ℝ) / 2)^t := pow_le_pow_left₀ hdiv0 hdiv t
  exact le_trans h1 hpow

theorem expectedTreapHeight_le {n : ℕ} :
    expectedTreapHeight (n := n) ≤ 30 * (harmonic n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [expectedTreapHeight, treapHeight, depth, PrioPerm, fintypeExpect]
  · have hn1 : 1 ≤ n := by omega
    let H : ℝ := harmonicReal n
    have hH0 : 0 ≤ H := by
      unfold H harmonicReal
      exact Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (by positivity))
    have hH1 : 1 ≤ H := by
      unfold H harmonicReal
      have hmem : 0 ∈ Finset.range n := by rw [Finset.mem_range]; omega
      have hnonneg : ∀ i ∈ Finset.range n, 0 ≤ ((i + 1 : ℕ) : ℝ)⁻¹ := by
        intro i hi
        exact inv_nonneg.mpr (by positivity)
      have hterm : ((0 + 1 : ℕ) : ℝ)⁻¹ = 1 := by norm_num
      have hle := Finset.single_le_sum hnonneg hmem
      rwa [hterm] at hle
    let Kh : ℕ := Nat.ceil H
    have hKh : H ≤ (Kh : ℝ) := by
      dsimp [Kh]
      exact (Nat.ceil_le (n := Nat.ceil H)).mp le_rfl
    have hKh1 : 1 ≤ Kh := by exact_mod_cast (le_trans hH1 hKh)
    have hKh_le : (Kh : ℝ) ≤ H + 1 := by
      have hc : Nat.ceil H ≤ Nat.floor H + 1 := by
        rw [Nat.ceil_le]
        rw [Nat.cast_add]
        norm_num
        exact le_of_lt (Nat.lt_floor_add_one H)
      have hfl : (Nat.floor H : ℝ) ≤ H := Nat.floor_le hH0
      dsimp [Kh]
      have hc' : (Nat.ceil H : ℝ) ≤ ((Nat.floor H : ℕ) + 1 : ℝ) := by exact_mod_cast hc
      have hcast : ((Nat.floor H : ℕ) + 1 : ℝ) = (Nat.floor H : ℝ) + 1 := by norm_num
      nlinarith [hc', hfl, hcast]
    let K : ℕ := 12 * Kh
    let T : ℕ := 6 * Kh
    have hT : (T : ℝ) ≥ 6 * H := by
      dsimp [T]
      norm_num
      nlinarith [hKh]
    have hT1 : 1 ≤ T := by dsimp [T]; omega
    have hdecay : (n : ℝ)^2 * ((1 : ℝ) / 2)^T ≤ 1 := by
      have hd := n_sq_mul_inv_pow_le_one Kh hKh
      simpa [T] using hd
    let P : ℕ → ℝ := fun k => fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ treapHeight σ))
    have hhead : (∑ k ∈ Finset.Icc 1 n, if k ≤ K then P k else 0) ≤ (K : ℝ) := by
      have hP1 : ∀ k, P k ≤ 1 := by
        intro k
        unfold P
        have hpt : ∀ σ : PrioPerm n, indicator (k ≤ treapHeight σ) ≤ (1 : ℝ) := by
          intro σ
          by_cases h : k ≤ treapHeight σ <;> simp [indicator, h]
        calc
          fintypeExpect (fun σ : PrioPerm n => indicator (k ≤ treapHeight σ)) ≤ fintypeExpect (fun σ : PrioPerm n => (1 : ℝ)) := by
            exact fintypeExpect_le _ _ hpt
          _ = 1 := by
            have hcard : Fintype.card (PrioPerm n) ≠ 0 := by simp [PrioPerm]
            exact fintypeExpect_const hcard (1 : ℝ)
      calc
        (∑ k ∈ Finset.Icc 1 n, if k ≤ K then P k else 0)
            ≤ (∑ k ∈ Finset.Icc 1 n, if k ≤ K then (1 : ℝ) else 0) := by
              apply Finset.sum_le_sum
              intro k hk
              by_cases h : k ≤ K
              · simp [h, hP1 k]
              · simp [h]
        _ = ((Finset.Icc 1 n).filter (fun k => k ≤ K)).card := by
              simp [Finset.sum_boole]
        _ ≤ (K : ℝ) := by
              have hsub : (Finset.Icc 1 n).filter (fun k => k ≤ K) ⊆ Finset.Icc 1 K := by
                intro k hk
                rw [Finset.mem_filter] at hk
                rw [Finset.mem_Icc] at hk ⊢
                exact ⟨hk.1.1, hk.2⟩
              have hcard : ((Finset.Icc 1 n).filter (fun k => k ≤ K)).card ≤ (Finset.Icc 1 K).card := Finset.card_le_card hsub
              have hcardK : (Finset.Icc 1 K).card = K := by
                rw [Nat.card_Icc]
                omega
              rw [hcardK] at hcard
              exact_mod_cast hcard
    have htail : (∑ k ∈ Finset.Icc 1 n, if K < k then P k else 0) ≤ (2 : ℝ) := by
      have hPk : ∀ k, K < k → P k ≤ (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) := by
        intro k hkK
        have hk1 : 1 ≤ k := by omega
        have ht := height_tail (n := n) k hk1
        let t : ℕ := (k - 1) / 2
        have htT : T ≤ t := by
          have hK2 : K / 2 ≤ (k - 1) / 2 := by
            exact Nat.div_le_div_right (by omega : K ≤ k - 1)
          have hKd : K / 2 = T := by
            dsimp [K, T]
            omega
          rw [← hKd]
          exact hK2
        have hterm : H^t / (t.factorial : ℝ) ≤ ((1 : ℝ) / 2)^T := by
          have h1t : 1 ≤ t := by omega
          have hlt := pow_div_factorial_le_inv_two t h1t hH0 ?_
          · have hle1 : H^t / (t.factorial : ℝ) ≤ ((1 : ℝ) / 2)^t := hlt
            have hpow : ((1 : ℝ) / 2)^t ≤ ((1 : ℝ) / 2)^T := by
              exact pow_le_pow_of_le_one (by norm_num) (by norm_num) htT
            exact le_trans hle1 hpow
          · have ht6 : (6 : ℝ) * H ≤ (t : ℝ) := by
              have h1 : (T : ℝ) ≤ (t : ℝ) := by exact_mod_cast htT
              nlinarith [hT, h1]
            exact ht6
        unfold P
        have hfac : (2 * H^t / (t.factorial : ℝ)) ≤ 2 * ((1 : ℝ) / 2)^T := by
          calc
            (2 * H^t / (t.factorial : ℝ)) = 2 * (H^t / (t.factorial : ℝ)) := by
              rw [mul_div_assoc]
            _ ≤ 2 * ((1 : ℝ) / 2)^T := by
              exact mul_le_mul_of_nonneg_left hterm (by norm_num)
        calc
          fintypeExpect (fun σ => indicator (k ≤ treapHeight σ)) ≤ (n : ℝ) * (2 * H^t / (t.factorial : ℝ)) := by
            simpa [t] using ht
          _ ≤ (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) := by
            exact mul_le_mul_of_nonneg_left hfac (by positivity)
      calc
        (∑ k ∈ Finset.Icc 1 n, if K < k then P k else 0)
            ≤ (∑ k ∈ Finset.Icc 1 n, if K < k then (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) else 0) := by
              apply Finset.sum_le_sum
              intro k hk
              by_cases h : K < k
              · simpa [h] using hPk k h
              · simp [h]
        _ ≤ (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) * n := by
              have hf : (Finset.Icc 1 n).filter (fun k => K < k) = Finset.Icc (K + 1) n := by
                ext k
                simp only [Finset.mem_filter, Finset.mem_Icc]
                constructor
                · intro hk
                  rcases hk with ⟨hk1, hk2⟩
                  rcases hk1 with ⟨hk1a, hk1b⟩
                  exact ⟨by omega, hk1b⟩
                · intro hk
                  rcases hk with ⟨hk1, hk2⟩
                  constructor
                  · constructor <;> omega
                  · omega
              have hsub2 : Finset.Icc (K + 1) n ⊆ Finset.Icc 1 n := by
                intro k hk
                rw [Finset.mem_Icc] at hk ⊢
                exact ⟨by omega, hk.2⟩
              calc
                (∑ k ∈ Finset.Icc 1 n, if K < k then (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) else 0)
                    = (∑ k ∈ (Finset.Icc 1 n).filter (fun k => K < k), (n : ℝ) * (2 * ((1 : ℝ) / 2)^T)) := by
                      rw [Finset.sum_filter]
                _ = ∑ k ∈ Finset.Icc (K + 1) n, (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) := by
                      rw [hf]
                _ ≤ ∑ k ∈ Finset.Icc 1 n, (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) := by
                      exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun k hk hk' => by positivity)
                _ = (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) * n := by
                      rw [Finset.sum_const]
                      rw [Nat.card_Icc]
                      have hcard : n + 1 - 1 = n := by omega
                      rw [hcard]
                      simp [nsmul_eq_mul]
                      ring
        _ ≤ (2 : ℝ) := by
              have hc : (n : ℝ) * (2 * ((1 : ℝ) / 2)^T) * n ≤ 2 := by
                nlinarith [hdecay]
              exact hc
    calc
      expectedTreapHeight (n := n) = ∑ k ∈ Finset.Icc 1 n, P k := by
        unfold P
        exact expectedTreapHeight_eq_sum
      _ = (∑ k ∈ Finset.Icc 1 n, if k ≤ K then P k else 0) +
          (∑ k ∈ Finset.Icc 1 n, if K < k then P k else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            by_cases h : k ≤ K
            · have hK : ¬ K < k := by omega
              simp [h, hK]
            · have hK : K < k := by omega
              simp [h, hK]
      _ ≤ (K : ℝ) + 2 := by nlinarith [hhead, htail]
      _ = 12 * (Kh : ℝ) + 2 := by
            dsimp [K]
            norm_num
      _ ≤ 30 * (harmonic n : ℝ) := by
            have hHreal : H = (harmonic n : ℝ) := by
              unfold H
              exact harmonicReal_eq_harmonic n
            have hK1 : 12 * (Kh : ℝ) + 2 ≤ 12 * H + 14 := by nlinarith [hKh_le]
            have hK2 : 12 * H + 14 ≤ 30 * H := by nlinarith [hH1]
            nlinarith [hK1, hK2, hHreal]

set_option linter.unusedTactic false

end Treap

end CLRS.Extensions
