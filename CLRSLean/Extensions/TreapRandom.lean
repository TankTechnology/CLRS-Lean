import CLRSLean.Chapter_07.Section_07_3_Randomized_Quicksort.Comparison_Probability
import CLRSLean.Extensions.RandomizedTreap
import CLRSLean.Probability.FiniteExpectation
import Mathlib.Tactic

open CLRS.Probability
open CLRS.Chapter07

/-!
# Randomized treap: expected depth (prototype)

This module analyzes the *probabilistic* side of the treap.  With
{lit}`n` keys and uniformly random distinct priorities, the canonical treap
(root = maximum priority, recurse on the two halves) has expected height
{lit}`O(log n)`.  The first milestone proved here is the expected **depth** of
a single key, which is the probabilistic core.

**Model.**  Keys are {lit}`Fin n`.  A random priority assignment is a uniform
random permutation {lit}`σ : Fin n ≃ Fin n` (the sample space is
{lit}`Equiv.Perm (Fin n)`), and the priority of key {lit}`i` is {lit}`σ i`.
The combinatorial characterization that ties the analysis to the treap shape
is: for {lit}`a ≠ b`, key {lit}`a` is an **ancestor** of key {lit}`b` in the
canonical treap iff {lit}`a` has the maximum priority among the keys in the
closed interval {lit}`[min a b, max a b]` — the maximum-priority key in an
interval is exactly the key that sits on the path from the root to {lit}`b`.

Consequently {lit}`depth b` is the number of ancestors of {lit}`b`, and by
linearity of expectation the expected depth is

> {lit}`E[depth b] = 1 + Σ_{a ≠ b} 1 / (|a - b| + 1)`

because among the {lit}`k = |a - b| + 1` keys of the interval, each is equally
likely to carry the maximum priority.  The right-hand side is a pair of
harmonic sums, so {lit}`E[depth b] ≤ 2 · H_n = O(log n)`.

Main results:

- Theorem {lit}`ancestor_prob`: for {lit}`a ≠ b`, {lit}`P[a ancestor of b] =
  1 / (|a - b| + 1)`.  The proof reuses Chapter 7's minimum-position symmetry
  lemma {lit}`isFirst_prob`, reducing the maximum-priority event to it via the
  order-reversing involution {lit}`Fin.revPerm`.
- Theorem {lit}`expectedDepth_le_harmonic`: {lit}`E[depth b] ≤ 2 · H_n`, so a
  random treap has logarithmic expected depth.

Status: prototype.  The probabilistic core — the ancestor-probability counting
and the harmonic bound — is complete.  The next module, {lit}`TreapHeight`,
uses exponential depth tails and a union bound to prove the expected
**height** result {lit}`E[height] ≤ 30 · H_n`.  Both remain extension work
outside the textbook coverage ledger.
-/

namespace CLRS.Extensions

namespace Treap

open scoped BigOperators

/-- Keys are {lit}`Fin n`; {lit}`n` is the number of keys. -/
abbrev Key (n : ℕ) := Fin n

/-- A random priority assignment: a permutation of the keys' priorities.
Key {lit}`i` gets priority {lit}`σ i`. -/
abbrev PrioPerm (n : ℕ) := Equiv.Perm (Fin n)

/-- The priority of key {lit}`i` under the permutation {lit}`σ`, as a natural. -/
def prioOfPerm {n : ℕ} (σ : PrioPerm n) (i : Fin n) : ℕ := (σ i).1

/-- Key {lit}`a` is an *ancestor* of key {lit}`b` in the canonical treap under
priority order {lit}`σ`: every key, and for {lit}`a ≠ b`, {lit}`a` carries the
maximum priority among the keys in the closed interval between {lit}`a` and
{lit}`b`. -/
def Ancestor {n : ℕ} (σ : PrioPerm n) (a b : Fin n) : Prop :=
  a = b ∨ ∀ k ∈ Finset.Icc (min a b) (max a b), prioOfPerm σ k ≤ prioOfPerm σ a

instance instDecidableAncestor {n : ℕ} (σ : PrioPerm n) (a b : Fin n) :
    Decidable (Ancestor σ a b) := by
  unfold Ancestor
  infer_instance

/-- The depth of key {lit}`b` in the canonical treap under {lit}`σ`: the number
of keys that are ancestors of {lit}`b`. -/
noncomputable def depth {n : ℕ} (σ : PrioPerm n) (b : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : Fin n => Ancestor σ a b)).card

/-- The expected depth of key {lit}`b` under a uniform random priority
permutation. -/
noncomputable def expectedDepth {n : ℕ} (b : Fin n) : ℝ :=
  fintypeExpect (fun σ : PrioPerm n => (depth σ b : ℝ))

/-- Depth counts ancestors, so by linearity of expectation the expected depth
is the sum over keys of the probability that the key is an ancestor of
{lit}`b`. -/
theorem expectedDepth_eq_sum {n : ℕ} (b : Fin n) :
    expectedDepth b =
      ∑ a : Fin n, fintypeExpect (fun σ : PrioPerm n => indicator (Ancestor σ a b)) := by
  unfold expectedDepth
  have hred : (fun σ : PrioPerm n => (depth σ b : ℝ)) =
      fun σ : PrioPerm n => ∑ a : Fin n, indicator (Ancestor σ a b) := by
    funext σ
    simp [depth, indicator]
  rw [hred]
  rw [fintypeExpect_sum]

/-! ## Ancestor probability

For {lit}`a ≠ b`, key {lit}`a` is an ancestor of {lit}`b` exactly when it
carries the maximum priority among the keys of the closed interval
{lit}`[min a b, max a b]`.  Under the uniform random permutation each key of an
interval {lit}`S` is equally likely to carry the maximum, so
{lit}`P[a ancestor b] = 1 / (|a - b| + 1)`.

The proof reuses Chapter 7's minimum-position symmetry lemma
{lit}`isFirst_prob` instead of re-proving it for maxima: composing the random
permutation with the order-reversing involution {lit}`Fin.revPerm` (after
inversion) is a bijection on the sample space that turns the maximum-priority
event into the minimum-position event. -/

/-- Key {lit}`a` carries the maximum priority among the keys of the set
{lit}`S`. -/
def MaxOver {n : ℕ} (σ : PrioPerm n) (S : Finset (Fin n)) (a : Fin n) : Prop :=
  a ∈ S ∧ ∀ k ∈ S, prioOfPerm σ k ≤ prioOfPerm σ a

instance instDecidableMaxOver {n : ℕ} (σ : PrioPerm n) (S : Finset (Fin n)) (a : Fin n) :
    Decidable (MaxOver σ S a) := by
  unfold MaxOver
  infer_instance

/-- {name}`Fin.revPerm` is an involution: applying it twice is the identity. -/
lemma revPerm_trans_revPerm {n : ℕ} :
    (Fin.revPerm.trans Fin.revPerm : Fin n ≃ Fin n) = Equiv.refl (α := Fin n) := by
  apply Equiv.ext
  intro i
  simp [Fin.revPerm_apply, Fin.rev_rev]

/-- Composing the inverse of a random permutation with the order-reversing
involution {lit}`Fin.revPerm` is a bijection on {lit}`PrioPerm n`.  Under this
bijection the maximum-priority event becomes Chapter 7's minimum-position
event, so the uniform distribution makes them equiprobable. -/
def revBijection {n : ℕ} : PrioPerm n ≃ PrioPerm n where
  toFun σ := Fin.revPerm.trans σ.symm
  invFun π := π.symm.trans Fin.revPerm
  left_inv := by
    intro σ
    change (Fin.revPerm.trans σ.symm).symm.trans Fin.revPerm = σ
    calc
      (Fin.revPerm.trans σ.symm).symm.trans Fin.revPerm
          = (σ.symm.symm.trans Fin.revPerm.symm).trans Fin.revPerm := by rw [Equiv.symm_trans]
      _ = (σ.trans Fin.revPerm).trans Fin.revPerm := by simp
      _ = σ.trans (Fin.revPerm.trans Fin.revPerm) := by rw [Equiv.trans_assoc]
      _ = σ := by
        rw [revPerm_trans_revPerm]
        rw [Equiv.trans_refl]
  right_inv := by
    intro π
    change Fin.revPerm.trans (π.symm.trans Fin.revPerm).symm = π
    calc
      Fin.revPerm.trans (π.symm.trans Fin.revPerm).symm
          = Fin.revPerm.trans (Fin.revPerm.symm.trans π.symm.symm) := by rw [Equiv.symm_trans]
      _ = Fin.revPerm.trans (Fin.revPerm.trans π) := by simp
      _ = (Fin.revPerm.trans Fin.revPerm).trans π := by rw [Equiv.trans_assoc]
      _ = π := by
        rw [revPerm_trans_revPerm]
        rw [Equiv.refl_trans]

/-- Under {name}`revBijection`, the position of key {lit}`x` is the reversed
priority of {lit}`x`. -/
lemma revBijection_symm_apply {n : ℕ} (σ : PrioPerm n) (x : Fin n) :
    (revBijection σ).symm x = Fin.revPerm (σ x) := by
  simp [revBijection]

/-- The maximum-priority event over {lit}`S` is Chapter 7's minimum-position
event under {name}`revBijection`. -/
lemma maxOver_iff_firstIn {n : ℕ} (S : Finset (Fin n)) (a : Fin n) (σ : PrioPerm n) :
    MaxOver σ S a ↔ IsFirstIn S a (revBijection σ) := by
  unfold MaxOver IsFirstIn
  simp only [pos, revBijection_symm_apply]
  constructor
  · rintro ⟨haS, hmax⟩
    refine ⟨haS, ?_⟩
    intro y hyS
    rw [Fin.revPerm_apply, Fin.revPerm_apply]
    rw [Fin.rev_le_rev (i := σ a) (j := σ y)]
    simpa [prioOfPerm] using hmax y hyS
  · rintro ⟨haS, hfirst⟩
    refine ⟨haS, ?_⟩
    intro k hkS
    have hle : Fin.revPerm (σ a) ≤ Fin.revPerm (σ k) := by
      simpa [pos, revBijection_symm_apply] using hfirst k hkS
    rw [Fin.revPerm_apply, Fin.revPerm_apply] at hle
    have hk : σ k ≤ σ a := (Fin.rev_le_rev (i := σ a) (j := σ k)).mp hle
    simpa [prioOfPerm] using hk

/-- Each key of a nonempty set {lit}`S` carries the maximum priority among
{lit}`S` with probability {lit}`1 / |S|`, by symmetry under the uniform random
permutation (via the Chapter 7 minimum-position lemma). -/
theorem maxOver_prob {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (a : Fin n)
    (ha : a ∈ S) :
    fintypeExpect (fun σ : PrioPerm n => indicator (MaxOver σ S a)) = 1 / (S.card : ℝ) := by
  classical
  have hFirst : fintypeExpect (fun σ : PrioPerm n => indicator (IsFirstIn S a σ)) =
      1 / (S.card : ℝ) := by
    unfold fintypeExpect indicator
    rw [Finset.sum_boole]
    rw [show (Fintype.card (PrioPerm n) : ℝ) = (Nat.factorial n : ℝ)
      by simp [PrioPerm, Fintype.card_perm]]
    exact isFirst_prob S hS a ha
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (MaxOver σ S a))
        = fintypeExpect (fun σ : PrioPerm n => indicator (IsFirstIn S a (revBijection σ))) := by
          apply congrArg fintypeExpect
          funext σ
          unfold indicator
          simp [maxOver_iff_firstIn]
    _ = fintypeExpect (fun σ : PrioPerm n => indicator (IsFirstIn S a σ)) := by
          exact fintypeExpect_equiv (revBijection)
            (fun σ : PrioPerm n => indicator (IsFirstIn S a σ))
    _ = 1 / (S.card : ℝ) := hFirst

/-- The number of keys in the closed interval between {lit}`a` and {lit}`b` is
{lit}`|a - b| + 1`. -/
lemma interval_card {n : ℕ} (a b : Fin n) :
    (Finset.Icc (min a b) (max a b)).card = (max a b).val - (min a b).val + 1 := by
  rw [Fin.card_Icc]
  have hmm : (min a b).val ≤ (max a b).val := by
    exact_mod_cast (min_le_max (a := a) (b := b))
  omega

/-- **Ancestor probability.**  For {lit}`a ≠ b`, the probability that {lit}`a`
is an ancestor of {lit}`b` is {lit}`1 / (|a - b| + 1)`. -/
theorem ancestor_prob {n : ℕ} {a b : Fin n} (hne : a ≠ b) :
    fintypeExpect (fun σ : PrioPerm n => indicator (Ancestor σ a b)) =
      1 / (((max a b).val - (min a b).val + 1 : ℕ) : ℝ) := by
  classical
  let I : Finset (Fin n) := Finset.Icc (min a b) (max a b)
  have haI : a ∈ I := by
    dsimp [I]
    exact Finset.mem_Icc.mpr ⟨min_le_left a b, le_max_left a b⟩
  have hIne : I.Nonempty := ⟨a, haI⟩
  calc
    fintypeExpect (fun σ : PrioPerm n => indicator (Ancestor σ a b))
        = fintypeExpect (fun σ : PrioPerm n => indicator (MaxOver σ I a)) := by
          apply congrArg fintypeExpect
          funext σ
          have hiff : Ancestor σ a b ↔ MaxOver σ I a := by
            unfold Ancestor MaxOver
            constructor
            · intro h
              rcases h with h | hmax
              · exact False.elim (hne h)
              · exact ⟨haI, hmax⟩
            · intro ⟨_, hmax⟩
              exact Or.inr hmax
          unfold indicator
          simp [hiff]
    _ = 1 / (I.card : ℝ) := maxOver_prob I hIne a haI
    _ = 1 / (((max a b).val - (min a b).val + 1 : ℕ) : ℝ) := by
          congr 1
          simpa [I] using (congrArg (fun x : ℕ => (x : ℝ)) (interval_card a b))

/-! ## Expected depth bound

With {lit}`P[a ancestor b] = 1 / (|a - b| + 1)`, linearity of expectation gives

> {lit}`E[depth b] = 1 + Σ_{a ≠ b} 1 / (|a - b| + 1)`.

The keys strictly below {lit}`b` form a partial harmonic sum at most
{lit}`H_n - 1`, and the keys strictly above form another at most
{lit}`H_n - 1`, so {lit}`E[depth b] ≤ 2 · H_n = O(log n)`. -/

noncomputable def harmonicReal (m : ℕ) : ℝ := ∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)⁻¹)

lemma harmonicReal_eq_succ_shift {n : ℕ} (hn : 1 ≤ n) :
    harmonicReal n = 1 + ∑ i ∈ Finset.range (n - 1), (((i + 2 : ℕ) : ℝ)⁻¹) := by
  unfold harmonicReal
  have hn' : n = (n - 1) + 1 := by omega
  rw [hn']
  rw [Finset.sum_range_succ']
  norm_num
  ring

lemma harmonicReal_eq_harmonic (m : ℕ) : harmonicReal m = (harmonic m : ℝ) := by
  unfold harmonicReal harmonic
  simp [Rat.cast_sum, Rat.cast_inv]

lemma below_sum_eq {n b : ℕ} (hb : b < n) :
    (∑ i ∈ Finset.range n, if i < b then (((b - i + 1 : ℕ) : ℝ)⁻¹) else 0) =
      ∑ i ∈ Finset.range b, (((i + 2 : ℕ) : ℝ)⁻¹) := by
  calc
    (∑ i ∈ Finset.range n, if i < b then (((b - i + 1 : ℕ) : ℝ)⁻¹) else 0)
        = (∑ i ∈ (Finset.range n).filter (fun i => i < b), (((b - i + 1 : ℕ) : ℝ)⁻¹)) := by
          rw [Finset.sum_filter]
    _ = (∑ i ∈ Finset.range b, (((b - i + 1 : ℕ) : ℝ)⁻¹)) := by
          rw [show (Finset.range n).filter (fun i => i < b) = Finset.range b by
            ext i
            rw [Finset.mem_filter]
            simp only [Finset.mem_range]
            constructor <;> omega]
    _ = (∑ i ∈ Finset.range b, (((i + 2 : ℕ) : ℝ)⁻¹)) := by
          rw [← Finset.sum_range_reflect]
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < b := Finset.mem_range.mp hi
          have hval : b - (b - 1 - i) + 1 = i + 2 := by omega
          rw [hval]

lemma below_sum_le_harmonic_val {n b : ℕ} (hn : 1 ≤ n) (hb : b < n) :
    (∑ i ∈ Finset.range n, if i < b then (((b - i + 1 : ℕ) : ℝ)⁻¹) else 0) ≤ harmonicReal n - 1 := by
  calc
    (∑ i ∈ Finset.range n, if i < b then (((b - i + 1 : ℕ) : ℝ)⁻¹) else 0)
        = (∑ i ∈ Finset.range b, (((i + 2 : ℕ) : ℝ)⁻¹)) := below_sum_eq hb
    _ ≤ (∑ i ∈ Finset.range (n - 1), (((i + 2 : ℕ) : ℝ)⁻¹)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            have hib : i < b := Finset.mem_range.mp hi
            exact Finset.mem_range.mpr (by omega)
          · intro i hi hi_not
            exact inv_nonneg.mpr (by positivity)
    _ = harmonicReal n - 1 := by
          rw [harmonicReal_eq_succ_shift hn]
          ring

lemma above_sum_eq {n b : ℕ} (hb : b < n) :
    (∑ i ∈ Finset.range n, if b < i then (((i - b + 1 : ℕ) : ℝ)⁻¹) else 0) =
      ∑ k ∈ Finset.range (n - 1 - b), (((k + 2 : ℕ) : ℝ)⁻¹) := by
  calc
    (∑ i ∈ Finset.range n, if b < i then (((i - b + 1 : ℕ) : ℝ)⁻¹) else 0)
        = (∑ i ∈ (Finset.range n).filter (fun i => b < i), (((i - b + 1 : ℕ) : ℝ)⁻¹)) := by
          rw [Finset.sum_filter]
    _ = (∑ k ∈ Finset.range (n - 1 - b), (((k + 2 : ℕ) : ℝ)⁻¹)) := by
          refine Finset.sum_bij (fun i _ => i - b - 1) ?_ ?_ ?_ ?_
          · intro i hi
            rw [Finset.mem_filter] at hi
            rcases hi with ⟨hin, hbi⟩
            have hin' : i < n := Finset.mem_range.mp hin
            rw [Finset.mem_range]
            omega
          · intro i₁ hi₁ i₂ hi₂ h
            rw [Finset.mem_filter] at hi₁ hi₂
            rcases hi₁ with ⟨hin₁, hb₁⟩
            rcases hi₂ with ⟨hin₂, hb₂⟩
            omega
          · intro k hk
            rw [Finset.mem_range] at hk
            refine ⟨k + b + 1, ?_, ?_⟩
            · rw [Finset.mem_filter]
              constructor
              · rw [Finset.mem_range]
                omega
              · omega
            · omega
          · intro i hi
            have hbi : b < i := by
              rw [Finset.mem_filter] at hi
              exact hi.2
            have hval : i - b + 1 = i - b - 1 + 2 := by omega
            rw [hval]

lemma above_sum_le_harmonic_val {n b : ℕ} (hn : 1 ≤ n) (hb : b < n) :
    (∑ i ∈ Finset.range n, if b < i then (((i - b + 1 : ℕ) : ℝ)⁻¹) else 0) ≤ harmonicReal n - 1 := by
  calc
    (∑ i ∈ Finset.range n, if b < i then (((i - b + 1 : ℕ) : ℝ)⁻¹) else 0)
        = (∑ k ∈ Finset.range (n - 1 - b), (((k + 2 : ℕ) : ℝ)⁻¹)) := above_sum_eq hb
    _ ≤ (∑ i ∈ Finset.range (n - 1), (((i + 2 : ℕ) : ℝ)⁻¹)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro i hi
            have hib : i < n - 1 - b := Finset.mem_range.mp hi
            have hle : n - 1 - b ≤ n - 1 := Nat.sub_le (n - 1) b
            exact Finset.mem_range.mpr (by omega)
          · intro i hi hi_not
            exact inv_nonneg.mpr (by positivity)
    _ = harmonicReal n - 1 := by
          rw [harmonicReal_eq_succ_shift hn]
          ring

lemma sum_split_three {n : ℕ} (b : Fin n) (X Y : Fin n → ℝ) :
    (∑ a : Fin n, if a < b then X a else if b < a then Y a else 1) =
      1 + (∑ a : Fin n, if a < b then X a else 0) +
          (∑ a : Fin n, if b < a then Y a else 0) := by
  calc
    (∑ a : Fin n, if a < b then X a else if b < a then Y a else 1)
        = (∑ a : Fin n, ((if a = b then 1 else 0) + (if a < b then X a else 0) + (if b < a then Y a else 0))) := by
          apply Finset.sum_congr rfl
          intro a ha
          by_cases hab : a = b
          · subst a; simp
          · have hne : a ≠ b := hab
            have hltgt : a < b ∨ b < a := lt_or_gt_of_ne hne
            rcases hltgt with hlt | hgt
            · have hba : ¬ b < a := not_lt.mpr (le_of_lt hlt)
              have heq : ¬ a = b := ne_of_lt hlt
              simp [hlt, hba, heq]
            · have hnot : ¬ a < b := not_lt.mpr (le_of_lt hgt)
              have heq : ¬ a = b := ne_of_gt hgt
              simp [hgt, hnot, heq]
    _ = (∑ a : Fin n, if a = b then 1 else 0) + (∑ a : Fin n, if a < b then X a else 0) +
        (∑ a : Fin n, if b < a then Y a else 0) := by
          simp [Finset.sum_add_distrib]
    _ = 1 + (∑ a : Fin n, if a < b then X a else 0) + (∑ a : Fin n, if b < a then Y a else 0) := by
          rw [Finset.sum_ite_eq']
          simp

lemma sum_fin_eq_range {n : ℕ} (b : Fin n) :
    (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else 0) =
      (∑ i ∈ Finset.range n, if i < b.val then (((b.val - i + 1 : ℕ) : ℝ)⁻¹) else 0) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if i < b.val then (((b.val - i + 1 : ℕ) : ℝ)⁻¹) else 0)]
  congr 1

lemma sum_fin_eq_range_above {n : ℕ} (b : Fin n) :
    (∑ a : Fin n, if b < a then (((a.val - b.val + 1 : ℕ) : ℝ)⁻¹) else 0) =
      (∑ i ∈ Finset.range n, if b.val < i then (((i - b.val + 1 : ℕ) : ℝ)⁻¹) else 0) := by
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => if b.val < i then (((i - b.val + 1 : ℕ) : ℝ)⁻¹) else 0)]
  congr 1

lemma below_sum_le_harmonic {n : ℕ} (b : Fin n) :
    (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else 0) ≤ harmonicReal n - 1 := by
  by_cases hn : n = 0
  · subst n; nomatch b
  · rw [sum_fin_eq_range b]
    exact below_sum_le_harmonic_val (n := n) (b := b.val) (by omega) b.isLt

lemma above_sum_le_harmonic {n : ℕ} (b : Fin n) :
    (∑ a : Fin n, if b < a then (((a.val - b.val + 1 : ℕ) : ℝ)⁻¹) else 0) ≤ harmonicReal n - 1 := by
  by_cases hn : n = 0
  · subst n; nomatch b
  · rw [sum_fin_eq_range_above b]
    exact above_sum_le_harmonic_val (n := n) (b := b.val) (by omega) b.isLt

theorem expectedDepth_le_harmonic {n : ℕ} (b : Fin n) :
    expectedDepth b ≤ 2 * (harmonic n : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n; nomatch b
  · have hbd : expectedDepth b =
        1 + (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else 0) +
            (∑ a : Fin n, if b < a then (((a.val - b.val + 1 : ℕ) : ℝ)⁻¹) else 0) := by
      rw [expectedDepth_eq_sum]
      have hsum : (∑ a : Fin n, fintypeExpect (fun σ : PrioPerm n => indicator (Ancestor σ a b))) =
          (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else
                          if b < a then (((a.val - b.val + 1 : ℕ) : ℝ)⁻¹) else 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hab : a = b
        · subst a
          have hcard : Fintype.card (PrioPerm n) ≠ 0 := by simp [PrioPerm]
          simp [Ancestor, indicator, fintypeExpect_const hcard]
        · have hne : a ≠ b := hab
          rw [ancestor_prob hne]
          have hltgt : a < b ∨ b < a := lt_or_gt_of_ne hne
          rcases hltgt with hlt | hgt
          · have hmax : max a b = b := max_eq_right (le_of_lt hlt)
            have hmin : min a b = a := min_eq_left (le_of_lt hlt)
            have hsize : (max a b).val - (min a b).val + 1 = b.val - a.val + 1 := by
              rw [hmax, hmin]
            rw [hsize]
            simp [hlt]
          · have hmax : max a b = a := max_eq_left (le_of_lt hgt)
            have hmin : min a b = b := min_eq_right (le_of_lt hgt)
            have hsize : (max a b).val - (min a b).val + 1 = a.val - b.val + 1 := by
              rw [hmax, hmin]
            have hnot : ¬ a < b := not_lt.mpr (le_of_lt hgt)
            rw [hsize]
            simp [hgt, hnot]
      rw [hsum]
      exact sum_split_three b (fun a => (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹))
        (fun a => (((a.val - b.val + 1 : ℕ) : ℝ)⁻¹))
    have hL : (∑ a : Fin n, if a < b then (((b.val - a.val + 1 : ℕ) : ℝ)⁻¹) else 0) ≤
        harmonicReal n - 1 := below_sum_le_harmonic b
    have hR : (∑ a : Fin n, if b < a then (((a.val - b.val + 1 : ℕ) : ℝ)⁻¹) else 0) ≤
        harmonicReal n - 1 := above_sum_le_harmonic b
    calc
      expectedDepth b ≤ 1 + (harmonicReal n - 1) + (harmonicReal n - 1) := by
        rw [hbd]
        nlinarith [hL, hR]
      _ = 2 * harmonicReal n - 1 := by ring
      _ ≤ 2 * harmonicReal n := by linarith
      _ = 2 * (harmonic n : ℝ) := by rw [harmonicReal_eq_harmonic]

end Treap

end CLRS.Extensions
