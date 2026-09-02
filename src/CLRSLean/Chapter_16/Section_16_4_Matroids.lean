import Mathlib.Tactic
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Rank.Finite
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Loop
import Mathlib.Data.List.Sort

/-!
# Matroids and greedy methods

This section formalizes CLRS §16.4: the theory of *matroids* and the general
`GREEDY` algorithm, culminating in the theorem that on a weighted matroid the
greedy algorithm returns a maximum-weight independent set.  Where CLRS §16.2
states the greedy-choice property and optimal substructure informally, matroid
theory makes them precise, so this page is the reusable home for the greedy
meta-theorem.

We **build on Mathlib's matroid library** rather than redefining matroid theory.
The ground `Matroid α`, its `Matroid.Indep`, `Matroid.IsBasis`, `Matroid.eRk`,
the finite augmentation lemma `Matroid.Indep.augment_finset`, and the
contraction `M ／ {x}` are all imported from
`Mathlib.Combinatorics.Matroid`.

Main results:

- `CLRS.Matroid16.WeightedMatroid`: a `Matroid` bundled with a nonnegative
  weight `w : α → ℕ` (CLRS "weighted matroid").
- `CLRS.Matroid16.greedy`: the executable `GREEDY` procedure that scans elements
  in a given (nonincreasing-weight) order and keeps each element that preserves
  independence.
- `CLRS.Matroid16.greedy_isBasis`: the greedy output is a *basis* (maximal
  independent set) of the elements it scanned.
- `CLRS.Matroid16.greedy_optimal` (**CLRS Theorem 16.10 / Corollary 16.11**):
  when scanning in nonincreasing weight order over the whole ground set, `greedy`
  returns a maximum-weight independent set.
- `CLRS.Matroid16.greedy_choice` (**CLRS Theorem 16.6**, greedy-choice
  property): a maximum-weight singleton-independent element lies in some
  maximum-weight independent set.
- `CLRS.Matroid16.optimal_substructure` (**CLRS Lemma 16.7**): optimal
  substructure through the matroid contraction `M ／ {x}`.
- `CLRS.Matroid16.greedyRun_optimal`: the fully self-contained version over a
  `Fintype`, sorting the ground set internally.

Notation and model conventions used in this section:

- `M` : a `Matroid α` (Mathlib's ground-set-as-`Set` matroid).
- `w` : `α → ℕ`, a nonnegative weight (`ℕ` makes nonnegativity automatic).
- `order` : a `List α` scanned by `greedy`, assumed sorted in nonincreasing
  weight (`List.Pairwise (fun a b => w b ≤ w a) order`) and to cover the ground set.
- Independent competitors are taken as `Finset α` with `M.Indep ↑B`; over a
  finite ground set every independent set is such a coerced `Finset`.
- `gweight w s = ∑ e ∈ s, w e` is the total weight of a `Finset`.

Proof theme.  The key structural fact is that `greedy` restricted to the
high-weight prefix `{e | t < w e}` is *itself* a greedy run, hence a basis of
that threshold set; therefore for every threshold `t` it selects at least as
many high-weight elements as any independent set does.  A layer-cake identity
`∑ e ∈ s, w e = ∑ t, |{e ∈ s | t < w e}|` then upgrades the per-threshold
cardinality domination to weight domination.  This mirrors the CLRS exchange
argument while offloading the exchange itself to Mathlib's `augment_finset`.
-/

namespace CLRS.Matroid16

open scoped Matroid

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (M : Matroid α) (w : α → ℕ) [DecidablePred M.Indep]

/-- A **weighted matroid** (CLRS §16.4): a `Matroid` together with a nonnegative
weight function `w : α → ℕ`.  Using `ℕ` for weights makes the nonnegativity
requirement of CLRS automatic. -/
structure WeightedMatroid (α : Type*) where
  /-- The underlying matroid. -/
  toMatroid : Matroid α
  /-- The nonnegative weight of each element. -/
  weight : α → ℕ

/-- Total weight of a finite set of elements, `∑ e ∈ s, w e`. -/
def gweight (w : α → ℕ) (s : Finset α) : ℕ := ∑ e ∈ s, w e

/-- One step of `GREEDY`: add `e` to the accumulated set `acc` when doing so
keeps the set independent, otherwise discard `e` (CLRS `GREEDY` lines 4-6). -/
def gstep (acc : Finset α) (e : α) : Finset α :=
  if M.Indep (↑(insert e acc) : Set α) then insert e acc else acc

/-- The **`GREEDY` procedure** (CLRS §16.4).  Scanning `order` (assumed sorted in
nonincreasing weight), it folds `gstep`, keeping each element that preserves
independence.  The result is an independent set; when `order` covers the ground
set it is a maximum-weight independent set (see `greedy_optimal`). -/
def greedy (order : List α) : Finset α := order.foldl (gstep M) ∅

/-- `GREEDY` applied through a `WeightedMatroid` bundle. -/
def WeightedMatroid.greedy (WM : WeightedMatroid α) [DecidablePred WM.toMatroid.Indep]
    (order : List α) : Finset α :=
  CLRS.Matroid16.greedy WM.toMatroid order

/-! ## Structural lemmas about the greedy fold -/

/-- The accumulator only grows as `gstep` is folded. -/
lemma foldl_gstep_monotone (order : List α) (acc : Finset α) :
    acc ⊆ order.foldl (gstep M) acc := by
  induction order generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    have h1 : acc ⊆ gstep M acc x := by
      unfold gstep; split
      · exact Finset.subset_insert x acc
      · exact subset_rfl
    exact h1.trans (ih (gstep M acc x))

/-- Everything the greedy fold produces comes from the accumulator or the list. -/
lemma foldl_gstep_subset (order : List α) (acc : Finset α) :
    order.foldl (gstep M) acc ⊆ acc ∪ order.toFinset := by
  induction order generalizing acc with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, List.toFinset_cons]
    refine (ih (gstep M acc x)).trans ?_
    have hgs : gstep M acc x ⊆ insert x acc := by
      unfold gstep; split
      · exact subset_rfl
      · exact Finset.subset_insert x acc
    calc gstep M acc x ∪ xs.toFinset
        ⊆ insert x acc ∪ xs.toFinset := Finset.union_subset_union hgs subset_rfl
      _ = acc ∪ insert x xs.toFinset := by rw [Finset.insert_union, Finset.union_insert]

/-- The greedy fold preserves independence. -/
lemma foldl_gstep_indep (order : List α) (acc : Finset α) (hacc : M.Indep (↑acc : Set α)) :
    M.Indep (↑(order.foldl (gstep M) acc) : Set α) := by
  induction order generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
    rw [List.foldl_cons]
    apply ih
    unfold gstep
    split
    · rename_i h; exact h
    · exact hacc

/-- If `e` was scanned but not kept, then adding it to the final greedy set is
dependent: `gstep` skipped `e` precisely because it created a dependency, and
the accumulator only grew afterwards. -/
lemma foldl_gstep_skip (order : List α) :
    ∀ (acc : Finset α) (e : α), e ∈ order → e ∉ order.foldl (gstep M) acc →
      ¬ M.Indep (insert e (↑(order.foldl (gstep M) acc)) : Set α) := by
  induction order with
  | nil => intro acc e he _; simp at he
  | cons x xs ih =>
    intro acc e he hnotin
    rw [List.foldl_cons] at hnotin ⊢
    rcases List.mem_cons.1 he with rfl | hmem
    · by_cases hind : M.Indep (↑(insert e acc) : Set α)
      · exfalso
        have hxg : e ∈ gstep M acc e := by
          unfold gstep; rw [if_pos hind]; exact Finset.mem_insert_self e acc
        exact hnotin ((foldl_gstep_monotone M xs (gstep M acc e)) hxg)
      · have hgs : gstep M acc e = acc := by unfold gstep; rw [if_neg hind]
        rw [hgs] at hnotin ⊢
        intro hcontra
        apply hind
        rw [Finset.coe_insert]
        refine hcontra.subset ?_
        apply Set.insert_subset_insert
        exact_mod_cast foldl_gstep_monotone M xs acc
    · exact ih (gstep M acc x) e hmem hnotin

/-- The greedy output is independent (CLRS: `GREEDY` maintains an independent
set as its loop invariant). -/
lemma greedy_indep (order : List α) : M.Indep (↑(greedy M order) : Set α) := by
  unfold greedy
  exact foldl_gstep_indep M order ∅ (by simpa using M.empty_indep)

/-- The greedy output is drawn from the scanned list. -/
lemma greedy_subset (order : List α) : greedy M order ⊆ order.toFinset := by
  unfold greedy
  have h := foldl_gstep_subset M order ∅
  simpa using h

/-- **The greedy output is a basis** (maximal independent set) of the elements it
scanned: it is independent, contained in the scanned ground elements, and cannot
be extended by any scanned ground element.  This is the structural heart of the
greedy optimality proof. -/
lemma greedy_isBasis (order : List α) :
    M.IsBasis (↑(greedy M order) : Set α) (↑order.toFinset ∩ M.E) := by
  have hI : M.Indep (↑(greedy M order) : Set α) := greedy_indep M order
  have hsub : (↑(greedy M order) : Set α) ⊆ ↑order.toFinset ∩ M.E := by
    apply Set.subset_inter
    · exact_mod_cast greedy_subset M order
    · exact hI.subset_ground
  rw [hI.isBasis_iff_forall_insert_dep hsub]
  rintro e ⟨heX, heG⟩
  obtain ⟨heOrd, heE⟩ := heX
  have heOrdL : e ∈ order := by
    have : e ∈ order.toFinset := by exact_mod_cast heOrd
    exact List.mem_toFinset.1 this
  have heGF : e ∉ greedy M order := by
    intro h; exact heG (by exact_mod_cast h)
  have hdep : ¬ M.Indep (insert e (↑(greedy M order)) : Set α) := by
    unfold greedy at heGF ⊢
    exact foldl_gstep_skip M order ∅ e heOrdL heGF
  rw [Matroid.dep_iff]
  exact ⟨hdep, Set.insert_subset heE hI.subset_ground⟩

/-! ## Restricting greedy to a high-weight prefix -/

/-- Folding `gstep` over a list all of whose elements fail predicate `p` does not
change the `p`-filtered accumulator. -/
lemma filter_foldl_gstep (p : α → Prop) [DecidablePred p]
    (l : List α) (A : Finset α) (hl : ∀ e ∈ l, ¬ p e) :
    (l.foldl (gstep M) A).filter p = A.filter p := by
  induction l generalizing A with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons]
    rw [ih (gstep M A x) (fun e he => hl e (List.mem_cons_of_mem x he))]
    have hx : ¬ p x := hl x (by simp)
    unfold gstep
    split
    · rw [Finset.filter_insert, if_neg hx]
    · rfl

/-- On a nonincreasing-weight list, the elements of weight `> t` form a *prefix*:
`order = pre ++ suf` with every element of `pre` above the threshold and every
element of `suf` at or below it. -/
lemma sorted_threshold_split (order : List α)
    (hsort : List.Pairwise (fun a b => w b ≤ w a) order) (t : ℕ) :
    ∃ pre suf, order = pre ++ suf ∧ (∀ e ∈ pre, t < w e) ∧ (∀ e ∈ suf, ¬ t < w e) := by
  induction order with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons x xs ih =>
    rw [List.pairwise_cons] at hsort
    obtain ⟨hhead, htail⟩ := hsort
    by_cases hx : t < w x
    · obtain ⟨pre, suf, heq, hpre, hsuf⟩ := ih htail
      refine ⟨x :: pre, suf, by rw [heq, List.cons_append], ?_, hsuf⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he'
      · exact hx
      · exact hpre e he'
    · refine ⟨[], x :: xs, rfl, by simp, ?_⟩
      intro e he
      rcases List.mem_cons.1 he with rfl | he'
      · exact hx
      · have hwe : w e ≤ w x := hhead e he'
        have hxt : w x ≤ t := Nat.not_lt.1 hx
        exact Nat.not_lt.2 (le_trans hwe hxt)

/-- **Per-threshold domination.**  For every weight threshold `t`, the greedy set
contains at least as many elements of weight `> t` as any independent set `B`.
This is because greedy restricted to the weight-`> t` prefix is again a greedy
run, hence a basis of the weight-`> t` ground elements, so no independent set can
have more elements there. -/
lemma greedy_filter_card_ge (order : List α)
    (hsort : List.Pairwise (fun a b => w b ≤ w a) order)
    (hcov : ∀ e, e ∈ M.E → e ∈ order)
    (B : Finset α) (hB : M.Indep (↑B : Set α)) (t : ℕ) :
    (B.filter (fun e => t < w e)).card ≤ ((greedy M order).filter (fun e => t < w e)).card := by
  obtain ⟨pre, suf, heq, hpre, hsuf⟩ := sorted_threshold_split w order hsort t
  -- greedy restricted to the weight-`> t` prefix is greedy on that prefix
  have hrestr : (greedy M order).filter (fun e => t < w e) = greedy M pre := by
    have hsplit : greedy M order = suf.foldl (gstep M) (greedy M pre) := by
      unfold greedy; rw [heq, List.foldl_append]
    rw [hsplit, filter_foldl_gstep M (fun e => t < w e) suf (greedy M pre)
      (fun e he => hsuf e he)]
    apply Finset.filter_true_of_mem
    intro e he
    exact hpre e (List.mem_toFinset.1 (greedy_subset M pre he))
  have hbasis := greedy_isBasis M pre
  set Bt := B.filter (fun e => t < w e) with hBt
  have hBtsub : (↑Bt : Set α) ⊆ ↑pre.toFinset ∩ M.E := by
    intro e he
    have he' : e ∈ Bt := by exact_mod_cast he
    rw [hBt, Finset.mem_filter] at he'
    obtain ⟨heB, hwt⟩ := he'
    have heE : e ∈ M.E := hB.subset_ground (by exact_mod_cast heB)
    have heOrd : e ∈ order := hcov e heE
    have hmem : e ∈ pre ∨ e ∈ suf := by
      rw [← List.mem_append, ← heq]; exact heOrd
    have hepre : e ∈ pre := by
      rcases hmem with h | h
      · exact h
      · exact absurd hwt (hsuf e h)
    refine ⟨?_, heE⟩
    exact_mod_cast List.mem_toFinset.2 hepre
  have hBtIndep : M.Indep (↑Bt : Set α) :=
    hB.subset (Finset.coe_subset.2 (Finset.filter_subset _ _))
  have h1 : (↑Bt : Set α).encard ≤ M.eRk (↑pre.toFinset ∩ M.E) :=
    hBtIndep.encard_le_eRk_of_subset hBtsub
  have h2 : M.eRk (↑pre.toFinset ∩ M.E) = (↑(greedy M pre) : Set α).encard :=
    hbasis.eRk_eq_encard
  have h3 : (↑Bt : Set α).encard ≤ (↑(greedy M pre) : Set α).encard := h1.trans_eq h2
  rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at h3
  rw [hrestr]
  exact_mod_cast h3

/-! ## Layer-cake identity -/

/-- For nonnegative integer weights bounded by `N`, the total weight of a set is
the sum over thresholds `t < N` of how many elements exceed `t`
(the "layer-cake" / superlevel-set decomposition). -/
lemma sum_eq_sum_range_card_filter (s : Finset α) (f : α → ℕ) (N : ℕ)
    (hN : ∀ a ∈ s, f a ≤ N) :
    ∑ a ∈ s, f a = ∑ t ∈ Finset.range N, (s.filter (fun a => t < f a)).card := by
  have h1 : ∑ t ∈ Finset.range N, (s.filter (fun a => t < f a)).card
      = ∑ a ∈ s, ∑ t ∈ Finset.range N, (if t < f a then (1 : ℕ) else 0) := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [h1]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.card_filter]
  have hfilter : (Finset.range N).filter (fun t => t < f a) = Finset.range (f a) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h; exact ⟨lt_of_lt_of_le h (hN a ha), h⟩
  rw [hfilter, Finset.card_range]

/-! ## Main theorem: greedy is optimal (CLRS Theorem 16.10) -/

/-- **CLRS Theorem 16.10 / Corollary 16.11.**  If `order` lists the ground set in
nonincreasing weight order, then `greedy` returns a maximum-weight independent
set: no independent `Finset` `B` has larger total weight than `greedy M order`.

The proof decomposes each side by the layer-cake identity into a sum over weight
thresholds and applies the per-threshold cardinality domination
`greedy_filter_card_ge`. -/
theorem greedy_optimal (order : List α)
    (hsort : List.Pairwise (fun a b => w b ≤ w a) order)
    (hcov : ∀ e, e ∈ M.E → e ∈ order)
    (B : Finset α) (hB : M.Indep (↑B : Set α)) :
    gweight w B ≤ gweight w (greedy M order) := by
  set N := order.toFinset.sup w with hNdef
  have hBmem : ∀ e ∈ B, e ∈ order.toFinset := by
    intro e he
    exact List.mem_toFinset.2 (hcov e (hB.subset_ground (by exact_mod_cast he)))
  have hGmem : greedy M order ⊆ order.toFinset := greedy_subset M order
  have hBweight : ∀ e ∈ B, w e ≤ N := fun e he => Finset.le_sup (hBmem e he)
  have hGweight : ∀ e ∈ greedy M order, w e ≤ N := fun e he => Finset.le_sup (hGmem he)
  unfold gweight
  rw [sum_eq_sum_range_card_filter B w N hBweight,
      sum_eq_sum_range_card_filter (greedy M order) w N hGweight]
  apply Finset.sum_le_sum
  intro t _
  exact greedy_filter_card_ge M w order hsort hcov B hB t

/-! ## Greedy-choice property (CLRS Theorem 16.6) -/

/-- Any independent set `I` can be enlarged, using elements of a bigger
independent set `J`, to an independent set of size `|J|` still contained in
`I ∪ J`.  This is the finite matroid augmentation packaged as a size-matching
extension, and is the engine of the greedy-choice exchange argument. -/
lemma indep_extend_to_card (J : Finset α) (hJ : M.Indep (↑J : Set α)) :
    ∀ (n : ℕ) (I : Finset α), M.Indep (↑I : Set α) → I.card ≤ J.card →
      J.card - I.card = n →
      ∃ A : Finset α, I ⊆ A ∧ A ⊆ I ∪ J ∧ M.Indep (↑A : Set α) ∧ A.card = J.card := by
  intro n
  induction n with
  | zero =>
    intro I hI hcard hn
    exact ⟨I, subset_rfl, Finset.subset_union_left, hI, by omega⟩
  | succ k ih =>
    intro I hI hcard hn
    obtain ⟨e, heJ, heI, hins⟩ := hI.augment_finset hJ (by omega)
    have hins' : M.Indep (↑(insert e I) : Set α) := by rw [Finset.coe_insert]; exact hins
    have hcard' : (insert e I).card ≤ J.card := by
      rw [Finset.card_insert_of_notMem heI]; omega
    have hn' : J.card - (insert e I).card = k := by
      rw [Finset.card_insert_of_notMem heI]; omega
    obtain ⟨A, hIA, hAsub, hAind, hAcard⟩ := ih (insert e I) hins' hcard' hn'
    refine ⟨A, (Finset.subset_insert e I).trans hIA, ?_, hAind, hAcard⟩
    intro a ha
    have hain := hAsub ha
    rw [Finset.mem_union, Finset.mem_insert] at hain
    rw [Finset.mem_union]
    rcases hain with (rfl | h) | h
    · right; exact heJ
    · left; exact h
    · right; exact h

/-- **CLRS Theorem 16.6 (greedy-choice property).**  Let `x` be a
maximum-weight element for which `{x}` is independent.  Then some maximum-weight
independent set contains `x`.

We take a global optimum `G` (the greedy output) and, if `x ∉ G`, swap `x` into
`G`: augment `{x}` up to size `|G|` using elements of `G`, obtaining `A ∋ x` with
`|A| = |G|` and `A \ {x} ⊆ G`.  The single element `y` of `G` not reused is
singleton-independent, so `w y ≤ w x`, giving `gweight A ≥ gweight G`; hence `A`
is also optimal. -/
theorem greedy_choice (x : α) (hx : M.Indep ({x} : Set α))
    (hmax : ∀ e, M.Indep ({e} : Set α) → w e ≤ w x)
    (order : List α)
    (hsort : List.Pairwise (fun a b => w b ≤ w a) order)
    (hcov : ∀ e, e ∈ M.E → e ∈ order) :
    ∃ A : Finset α, x ∈ A ∧ M.Indep (↑A : Set α) ∧
      ∀ B : Finset α, M.Indep (↑B : Set α) → gweight w B ≤ gweight w A := by
  set G := greedy M order with hGdef
  have hGind : M.Indep (↑G : Set α) := greedy_indep M order
  have hGopt : ∀ B : Finset α, M.Indep (↑B : Set α) → gweight w B ≤ gweight w G :=
    fun B hB => greedy_optimal M w order hsort hcov B hB
  by_cases hxG : x ∈ G
  · exact ⟨G, hxG, hGind, hGopt⟩
  · -- `x` is a nonloop, so `x` lies in the ground set and is scanned.
    have hxE : x ∈ M.E := hx.subset_ground (by simp)
    -- `1 ≤ |G|` because `{x}` is an independent subset of the scanned basis.
    have hxsingle : M.Indep (↑({x} : Finset α) : Set α) := by simpa using hx
    have hxmem : (x : α) ∈ (↑order.toFinset ∩ M.E : Set α) := by
      refine ⟨?_, hxE⟩
      exact_mod_cast List.mem_toFinset.2 (hcov x hxE)
    have hcardpos : 1 ≤ G.card := by
      have hle : (↑({x} : Finset α) : Set α).encard ≤ M.eRk (↑order.toFinset ∩ M.E) :=
        hxsingle.encard_le_eRk_of_subset (by
          intro e he
          have : e = x := by simpa using he
          simpa [this] using hxmem)
      have heq : M.eRk (↑order.toFinset ∩ M.E) = (↑G : Set α).encard :=
        (greedy_isBasis M order).eRk_eq_encard
      rw [heq, Set.encard_coe_eq_coe_finsetCard, Set.encard_coe_eq_coe_finsetCard] at hle
      have : ({x} : Finset α).card ≤ G.card := by exact_mod_cast hle
      simpa using this
    -- Augment `{x}` to a size-`|G|` independent set inside `{x} ∪ G`.
    obtain ⟨A, hxA, hAsub, hAind, hAcard⟩ :=
      indep_extend_to_card M G hGind (G.card - 1) {x} hxsingle
        (by simpa using hcardpos) (by simp)
    have hxA' : x ∈ A := hxA (by simp)
    refine ⟨A, hxA', hAind, fun B hB => ?_⟩
    -- Show `gweight G ≤ gweight A`, hence `A` is optimal.
    have hGA : gweight w G ≤ gweight w A := by
      -- `S = A \ {x} ⊆ G`, with `|S| = |G| - 1`.
      set S := A.erase x with hSdef
      have hSsub : S ⊆ G := by
        intro a ha
        rw [hSdef, Finset.mem_erase] at ha
        obtain ⟨hax, haA⟩ := ha
        have := hAsub haA
        rw [Finset.mem_union, Finset.mem_singleton] at this
        rcases this with h | h
        · exact absurd h hax
        · exact h
      have hScard : S.card = G.card - 1 := by
        rw [hSdef, Finset.card_erase_of_mem hxA', hAcard]
      have hxS : x ∉ S := by rw [hSdef]; exact Finset.notMem_erase x A
      have hAeq : A = insert x S := by
        rw [hSdef, Finset.insert_erase hxA']
      -- `G \ S` is a single element `y`.
      have hdiffcard : (G \ S).card = 1 := by
        rw [Finset.card_sdiff_of_subset hSsub, hScard]; omega
      obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hdiffcard
      have hyG : y ∈ G := by
        have : y ∈ G \ S := by rw [hy]; simp
        exact (Finset.mem_sdiff.1 this).1
      -- `y` is singleton-independent, so `w y ≤ w x`.
      have hyindep : M.Indep ({y} : Set α) := by
        apply hGind.subset
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact_mod_cast hyG
      have hwy : w y ≤ w x := hmax y hyindep
      -- Weight bookkeeping.
      have hGsum : gweight w G = gweight w S + w y := by
        have hsd : gweight w (G \ S) + gweight w S = gweight w G := by
          unfold gweight; exact Finset.sum_sdiff hSsub
        have hdy : gweight w (G \ S) = w y := by
          rw [hy]; unfold gweight; simp
        rw [hdy] at hsd; omega
      have hAsum : gweight w A = w x + gweight w S := by
        rw [hAeq]; unfold gweight; rw [Finset.sum_insert hxS]
      rw [hGsum, hAsum]; omega
    exact le_trans (hGopt B hB) hGA

/-! ## Optimal substructure through contraction (CLRS Lemma 16.7) -/

/-- **CLRS Lemma 16.7 (matroids have optimal substructure).**  Let `x` be a
nonloop (`M.Indep {x}`).  Independent sets of the contraction `M ／ {x}`
correspond exactly to the independent sets of `M` obtained by adding `x`, and the
weights decompose additively.  Thus finding a maximum-weight independent set
containing `x` reduces to finding one in `M ／ {x}` — the optimal-substructure
property that legitimizes the greedy recursion. -/
theorem optimal_substructure (x : α) (hx : M.Indep ({x} : Set α)) (I : Finset α)
    (hxI : x ∉ I) :
    ((M ／ ({x} : Set α)).Indep (↑I : Set α) ↔ M.Indep (↑(insert x I) : Set α)) ∧
      gweight w (insert x I) = w x + gweight w I := by
  have hnl : M.IsNonloop x := Matroid.indep_singleton.1 hx
  refine ⟨?_, ?_⟩
  · rw [hnl.contractElem_indep_iff]
    constructor
    · rintro ⟨-, h⟩; rwa [Finset.coe_insert]
    · intro h
      refine ⟨by simpa using hxI, ?_⟩
      rwa [Finset.coe_insert] at h
  · unfold gweight; rw [Finset.sum_insert hxI]

/-! ## Self-contained greedy over a finite ground set -/

/-- The ground set sorted in nonincreasing weight order, used by the
self-contained `greedyRun`. -/
noncomputable def greedySortedOrder [Fintype α] (w : α → ℕ) : List α :=
  (Finset.univ.toList).mergeSort (fun a b => w b ≤ w a)

/-- The fully self-contained greedy run over a finite ground set: it sorts the
whole type by nonincreasing weight and applies `GREEDY`. -/
noncomputable def greedyRun [Fintype α] : Finset α :=
  greedy M (greedySortedOrder w)

/-- **`greedyRun` is optimal.**  With no ordering hypotheses required from the
caller, the self-contained greedy run returns a maximum-weight independent set.
This is `greedy_optimal` specialized to the internally sorted ground-set order. -/
theorem greedyRun_optimal [Fintype α] (B : Finset α) (hB : M.Indep (↑B : Set α)) :
    gweight w B ≤ gweight w (greedyRun M w) := by
  haveI : IsTrans α (fun a b => w b ≤ w a) := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  haveI : Std.Total (fun a b => w b ≤ w a) := ⟨fun a b => le_total (w b) (w a)⟩
  unfold greedyRun greedySortedOrder
  refine greedy_optimal M w _ ?_ ?_ B hB
  · exact List.pairwise_mergeSort' (fun a b => w b ≤ w a) _
  · intro e _
    exact (List.mergeSort_perm _ _).mem_iff.2 (Finset.mem_toList.2 (Finset.mem_univ e))

end CLRS.Matroid16
