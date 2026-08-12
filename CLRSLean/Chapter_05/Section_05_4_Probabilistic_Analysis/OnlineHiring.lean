import CLRSLean.Probability.FiniteExpectation
import Mathlib

/-!
# CLRS §5.4.4 — The On-line Hiring Problem

We model the on-line hiring problem (CLRS §5.4.4).  {lit}`n` candidates arrive
in random order (uniform over all {lit}`n!` permutations).  After each interview
the algorithm must decide immediately whether to hire the current candidate and
stop, or to continue.  The goal is to maximize the probability of hiring the
**best** candidate.

The threshold strategy interviews the first {lit}`k` applicants without hiring
(the *observation phase*), then hires the first applicant who is better than
every applicant seen so far.

**Status:** The finite record-selection strategy is executable and comes with
exact {lit}`some` and {lit}`none` contracts, and its success probability has
the harmonic closed form {lit}`(k/n) * (H_{n-1} - H_{k-1})`
({lit}`probHireBest_eq`).  The {lit}`1/e` asymptotic is proved for the
threshold {lit}`⌊n/e⌋` ({lit}`probHireBest_asymptotic`).
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability
open Filter
open scoped Topology

namespace OnlineHiring

/-! ## Model

The sample space is the uniform distribution over {lit}`Equiv.Perm (Fin n)`.
Candidate {lit}`i` has **score** {lit}`π i` ({lit}`0` = best, {lit}`n-1` =
worst).  The absolute best candidate is the one with score {lit}`0`.
-/

/--
The absolute best candidate: the one mapped to {lit}`0` (smallest score) by
the permutation.
-/
def isAbsoluteBest {n : ℕ} (π : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (π i).val = 0

/--
Candidate {lit}`j` is a record when its score is better (numerically smaller)
than every earlier candidate's score.
-/
def isRecordAt {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) : Prop :=
  ∀ i : Fin n, i.val < j.val → (π j).val < (π i).val

/-- `isRecordAt` is decidable: it is a finite universal over the scores. -/
instance {n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin n) :
    Decidable (isRecordAt π j) := by
  unfold isRecordAt
  infer_instance

/--
The record positions at or after the natural-number observation threshold.
-/
def eligiblePositions {n : ℕ} (k : ℕ)
    (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => k ≤ j.val ∧ isRecordAt π j

/-- The executable threshold strategy selects the earliest eligible record. -/
def hiringStrategy {n : ℕ} (k : ℕ)
    (π : Equiv.Perm (Fin n)) : Option (Fin n) :=
  let eligible := eligiblePositions k π
  if h : eligible.Nonempty then some (eligible.min' h) else none

/-- Membership in the executable candidate set is exactly the threshold and
record condition. -/
theorem mem_eligiblePositions_iff {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n} :
    j ∈ eligiblePositions k π ↔ k ≤ j.val ∧ isRecordAt π j := by
  simp [eligiblePositions]

/-- Exact contract for a successful threshold selection: the returned
position is an eligible record and is no later than any other eligible record.
-/
theorem hiringStrategy_some_iff {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n} :
    hiringStrategy k π = some j ↔
      k ≤ j.val ∧ isRecordAt π j ∧
        ∀ i : Fin n, k ≤ i.val → isRecordAt π i → j ≤ i := by
  classical
  unfold hiringStrategy
  dsimp only
  split_ifs with hne
  · constructor
    · intro h
      have hj : (eligiblePositions k π).min' hne = j := Option.some.inj h
      subst j
      have hmem : (eligiblePositions k π).min' hne ∈ eligiblePositions k π :=
        Finset.min'_mem _ hne
      have helig := mem_eligiblePositions_iff.mp hmem
      refine ⟨helig.1, helig.2, ?_⟩
      intro i hi hrecord
      exact Finset.min'_le _ i (mem_eligiblePositions_iff.mpr ⟨hi, hrecord⟩)
    · rintro ⟨hj, hrecord, hleast⟩
      apply congrArg some
      apply le_antisymm
      · exact Finset.min'_le _ j (mem_eligiblePositions_iff.mpr ⟨hj, hrecord⟩)
      · have hminmem :
            (eligiblePositions k π).min' hne ∈ eligiblePositions k π :=
          Finset.min'_mem _ hne
        have hmin := mem_eligiblePositions_iff.mp hminmem
        exact hleast _ hmin.1 hmin.2
  · constructor
    · intro h
      simp at h
    · rintro ⟨hj, hrecord, _⟩
      exact False.elim (hne ⟨j, mem_eligiblePositions_iff.mpr ⟨hj, hrecord⟩⟩)

/-- Exact contract for failure: there is no record position at or after the
observation threshold. -/
theorem hiringStrategy_none_iff {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} :
    hiringStrategy k π = none ↔
      ∀ j : Fin n, k ≤ j.val → ¬ isRecordAt π j := by
  classical
  constructor
  · intro hnone j hj hrecord
    have hne : (eligiblePositions k π).Nonempty :=
      ⟨j, mem_eligiblePositions_iff.mpr ⟨hj, hrecord⟩⟩
    simp [hiringStrategy, hne] at hnone
  · intro hnone
    have hempty : ¬ (eligiblePositions k π).Nonempty := by
      rintro ⟨j, hjmem⟩
      have hj := mem_eligiblePositions_iff.mp hjmem
      exact hnone j hj.1 hj.2
    simp [hiringStrategy, hempty]

/-- A successful hire occurs at or after the observation threshold. -/
theorem hiringStrategy_after_observation {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n}
    (h : hiringStrategy k π = some j) : k ≤ j.val :=
  (hiringStrategy_some_iff.mp h).1

/-- A successfully hired candidate is a record at their interview position. -/
theorem hiringStrategy_record {n : ℕ} {k : ℕ}
    {π : Equiv.Perm (Fin n)} {j : Fin n}
    (h : hiringStrategy k π = some j) : isRecordAt π j :=
  (hiringStrategy_some_iff.mp h).2.1

/-- Finite success probability of the threshold strategy under the uniform
distribution on permutations of the candidate positions. -/
noncomputable def probHireBest (n k : ℕ) : ℝ := by
  classical
  exact fintypeExpect fun π : Equiv.Perm (Fin n) =>
    match hiringStrategy k π with
    | some i => if isAbsoluteBest π i then 1 else 0
    | none => 0

/-! ## Closed form of the success probability

The strategy succeeds exactly when it hires the absolute best candidate.  We
prove the classic harmonic closed form (CLRS §5.4.4): the success probability
is `(k/n) * (H_{n-1} - H_{k-1})`, the product of `k/n` with the harmonic
difference.

The proof conditions on the position {lit}`j` of the best candidate.  Given the
best is at {lit}`j` (probability {lit}`1/n`), the strategy hires it exactly when
no record occurs in positions `{k, ..., j-1}`; a record is a left-to-right
minimum of the *scores* ({lit}`0` = best), so no record occurs there exactly
when the minimum score among the first {lit}`j.val` positions is already
achieved at a position `< k`.  The minimum's position is uniformly distributed
over the first {lit}`j.val` positions (transposition symmetry), giving
probability {lit}`k / j.val`.  Summing over {lit}`j` yields the harmonic closed
form.
-/

/-- Embed the first `m` positions `{0,...,m-1}` into `Fin n`. -/
def liftFirst {n m : ℕ} (hm : m ≤ n) (t : Fin m) : Fin n :=
  ⟨t.val, lt_of_lt_of_le t.isLt hm⟩

/-- Position `p` (among the first `m`) holds the minimum score among the first
`m` positions.  Scores are `Fin n` elements and `0` is the best. -/
def isMinInFirst {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) (p : Fin m) : Prop :=
  ∀ t : Fin m, (π (liftFirst hm p)).val ≤ (π (liftFirst hm t)).val

/-- `isMinInFirst` is decidable: it is a finite universal over the first `m`
positions. -/
instance isMinInFirst_decidable {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) (p : Fin m) :
    Decidable (isMinInFirst hm π p) := by
  unfold isMinInFirst
  infer_instance

/-- Two `Fin` elements with the same value are equal, whatever bound proofs
are supplied (proof irrelevance of the `val < n` witness). -/
@[simp] theorem Fin.mk_val_mk_val {n : ℕ} {a : ℕ} (h1 h2 : a < n) :
    (⟨a, h1⟩ : Fin n) = ⟨a, h2⟩ := by
  apply Fin.ext
  rfl

/-- `⟨x.val, h⟩` is `x` for any valid bound proof `h`. -/
theorem Fin.eq_of_val_mk {n : ℕ} (x : Fin n) (h : x.val < n) : (⟨x.val, h⟩ : Fin n) = x := by
  apply Fin.ext
  rfl

/-- A position holding the minimum among the first `j` positions is strictly
smaller in score than every other position of the first `j`. -/
lemma isMinInFirst_lt {n j : ℕ} (hjn : j ≤ n) (π : Equiv.Perm (Fin n)) (p : Fin j)
    (hp : isMinInFirst hjn π p) (i : Fin n) (hpi : i.val < j) (hne : i ≠ liftFirst hjn p) :
    (π ⟨p.val, lt_of_lt_of_le p.isLt hjn⟩).val < (π i).val := by
  have hle : (π ⟨p.val, lt_of_lt_of_le p.isLt hjn⟩).val ≤ (π i).val := by
    have hbi : liftFirst hjn ⟨i.val, hpi⟩ = i := by
      change ⟨i.val, lt_of_lt_of_le hpi hjn⟩ = i
      exact Fin.eq_of_val_mk i (lt_of_lt_of_le hpi hjn)
    rw [← hbi]
    exact hp ⟨i.val, hpi⟩
  have hne_val : (π ⟨p.val, lt_of_lt_of_le p.isLt hjn⟩).val ≠ (π i).val := by
    intro h
    have hπeq : π ⟨p.val, lt_of_lt_of_le p.isLt hjn⟩ = π i := Fin.ext h
    exact hne (π.injective hπeq).symm
  exact lt_of_le_of_ne hle hne_val

/-- Swap the scores at positions `a` and `b` of a permutation (right-composition
with the transposition). -/
def swapValues {n : ℕ} (a b : Fin n) (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  π * Equiv.swap a b

/-- Swapping the scores at `a` and `b` is the same as swapping `b` and `a`. -/
lemma swapValues_comm {n : ℕ} (a b : Fin n) (π : Equiv.Perm (Fin n)) :
    swapValues a b π = swapValues b a π := by
  unfold swapValues
  rw [Equiv.swap_comm a b]

/-- `swapValues` is an involution: swapping the same two positions twice is the
identity. -/
lemma swapValues_involutive {n : ℕ} (a b : Fin n) (π : Equiv.Perm (Fin n)) :
    swapValues a b (swapValues a b π) = π := by
  unfold swapValues
  simp [mul_assoc, Equiv.swap_inv]

/-- The minimum of the first `m` positions exists (for `0 < m`). -/
lemma isMinInFirst_exists {n m : ℕ} (hm : m ≤ n) (hmpos : 0 < m)
    (π : Equiv.Perm (Fin n)) : ∃ p : Fin m, isMinInFirst hm π p := by
  let S : Finset ℕ := Finset.image (fun t : Fin m => (π (liftFirst hm t)).val) Finset.univ
  have hne : S.Nonempty := by
    exact ⟨(π (liftFirst hm ⟨0, hmpos⟩)).val,
      Finset.mem_image.mpr ⟨⟨0, hmpos⟩, Finset.mem_univ _, rfl⟩⟩
  rcases Finset.mem_image.mp (Finset.min'_mem S hne) with ⟨p, hp, hpm⟩
  refine ⟨p, ?_⟩
  intro t
  have ht_mem : (π (liftFirst hm t)).val ∈ S :=
    Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩
  have hle : S.min' hne ≤ (π (liftFirst hm t)).val := Finset.min'_le S _ ht_mem
  rwa [← hpm] at hle

/-- `liftFirst` is injective: the embedding of the first `m` positions is
one-to-one. -/
lemma liftFirst_injective {n m : ℕ} (hm : m ≤ n) {a b : Fin m}
    (h : liftFirst hm a = liftFirst hm b) : a = b := by
  apply Fin.ext
  change (liftFirst hm a).val = (liftFirst hm b).val
  exact congrArg Fin.val h

/-- The minimum of the first `m` positions is unique (scores are distinct). -/
lemma isMinInFirst_unique {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) {p q : Fin m}
    (hp : isMinInFirst hm π p) (hq : isMinInFirst hm π q) : p = q := by
  have hle1 : (π (liftFirst hm p)).val ≤ (π (liftFirst hm q)).val := hp q
  have hle2 : (π (liftFirst hm q)).val ≤ (π (liftFirst hm p)).val := hq p
  have hval : (π (liftFirst hm p)).val = (π (liftFirst hm q)).val := le_antisymm hle1 hle2
  have hπeq : π (liftFirst hm p) = π (liftFirst hm q) := Fin.ext hval
  exact liftFirst_injective hm (π.injective hπeq)

/-- Swapping the scores at positions `p` and `q` (both in the first `m`) moves
the minimum of the first `m` positions from `p` to `q`. -/
lemma isMinInFirst_swap {n m : ℕ} (hm : m ≤ n) {p q : Fin m} (hne : p ≠ q)
    (π : Equiv.Perm (Fin n)) (hp : isMinInFirst hm π p) :
    isMinInFirst hm (swapValues (liftFirst hm p) (liftFirst hm q) π) q := by
  classical
  intro t
  -- new score at position q is the old minimum `π (liftFirst hm p)`
  have hL : (swapValues (liftFirst hm p) (liftFirst hm q) π (liftFirst hm q)).val
      = (π (liftFirst hm p)).val := by
    unfold swapValues
    simp [Equiv.swap_apply_right]
  rw [hL]
  by_cases htq : t = q
  · subst t
    -- new score at q equals the old minimum, so the inequality is reflexive
    simpa [hL]
  · by_cases htp : t = p
    · subst t
      -- new score at p is the old score at q, which is above the old minimum
      have hR : (swapValues (liftFirst hm p) (liftFirst hm q) π (liftFirst hm p)).val
          = (π (liftFirst hm q)).val := by
        unfold swapValues
        simp [Equiv.swap_apply_left]
      rw [hR]
      exact hp q
    · -- t is neither p nor q, so the swap fixes it
      have hfix : (Equiv.swap (liftFirst hm p) (liftFirst hm q)) (liftFirst hm t)
          = liftFirst hm t := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h
          exact htp (liftFirst_injective hm h)
        · intro h
          exact htq (liftFirst_injective hm h)
      have hR : (swapValues (liftFirst hm p) (liftFirst hm q) π (liftFirst hm t)).val
          = (π (liftFirst hm t)).val := by
        unfold swapValues
        simp [hfix]
      rw [hR]
      exact hp t

/-- The transposition of two positions other than `pos` preserves the property
"score `0` is at `pos`". -/
lemma bestAt_swap (pos : Fin n) {a b : Fin n} (hpa : a ≠ pos) (hpb : b ≠ pos)
    (π : Equiv.Perm (Fin n)) (h : (π pos).val = 0) :
    (swapValues a b π pos).val = 0 := by
  have hfix : (Equiv.swap a b) pos = pos :=
    Equiv.swap_apply_of_ne_of_ne (fun hx => hpa hx.symm) (fun hx => hpb hx.symm)
  unfold swapValues
  simp [hfix, h]

/-- The set of permutations with score `0` at `pos` and the minimum of the
first `m` positions at `p`. -/
noncomputable def bestMinSet (n m : ℕ) (hm : m ≤ n) (pos : Fin n) (p : Fin m) :
    Finset (Equiv.Perm (Fin n)) :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun π => (π pos).val = 0 ∧ isMinInFirst hm π p)

/-- The number of permutations with score `0` at `pos` and the minimum of the
first `m` positions at `p`. -/
noncomputable def bestMinCount (n m : ℕ) (hm : m ≤ n) (pos : Fin n) (p : Fin m) : ℕ :=
  (bestMinSet n m hm pos p).card

/-- The sets `bestMinSet ... p` for `p : Fin m` are pairwise disjoint, because
the minimum of the first `m` positions is unique. -/
lemma bestMinSet_disjoint {n m : ℕ} (hm : m ≤ n) (pos : Fin n) :
    (Set.univ : Set (Fin m)).PairwiseDisjoint (fun p => bestMinSet n m hm pos p) := by
  intro p _ q _ hpq
  change Disjoint (bestMinSet n m hm pos p) (bestMinSet n m hm pos q)
  rw [Finset.disjoint_left]
  intro π hπ hπ'
  rw [bestMinSet, Finset.mem_filter] at hπ hπ'
  exact hpq (isMinInFirst_unique hm π hπ.2.2 hπ'.2.2)

/-- The sets `bestMinSet ... p` for `p : Fin m` cover the permutations with
score `0` at `pos` (for `0 < m`), since the minimum of the first `m` positions
always exists. -/
lemma bestMinSet_cover {n m : ℕ} (hm : m ≤ n) (hmpos : 0 < m) (pos : Fin n) :
    Finset.biUnion Finset.univ (fun p : Fin m => bestMinSet n m hm pos p)
      = (Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0) := by
  ext π
  constructor
  · intro hπ
    rcases Finset.mem_biUnion.mp hπ with ⟨p, _, hp⟩
    simp [bestMinSet] at hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.1⟩
  · intro hπ
    rw [Finset.mem_filter] at hπ
    rcases isMinInFirst_exists hm hmpos π with ⟨p, hpmin⟩
    refine Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, ?_⟩
    simp [bestMinSet, hπ.2, hpmin]

/-- The number of best-at-`pos` permutations with minimum at `p` is independent
of `p`: transposition symmetry moves the minimum position anywhere within the
first `m` positions. -/
lemma bestMinCount_eq {n m : ℕ} (hm : m ≤ n) (pos : Fin n) (hpos : m ≤ pos.val)
    {p q : Fin m} (hne : p ≠ q) :
    bestMinCount n m hm pos p = bestMinCount n m hm pos q := by
  classical
  apply Finset.card_bij (fun π hπ => swapValues (liftFirst hm p) (liftFirst hm q) π) ?_ ?_ ?_
  · intro π hπ
    rw [bestMinSet, Finset.mem_filter] at hπ ⊢
    rcases hπ with ⟨hπu, hbest, hmin⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    have hpos_ne_p : liftFirst hm p ≠ pos := by
      intro h
      have : p.val < pos.val := by omega
      exact (ne_of_lt this) (congrArg Fin.val h)
    have hpos_ne_q : liftFirst hm q ≠ pos := by
      intro h
      have : q.val < pos.val := by omega
      exact (ne_of_lt this) (congrArg Fin.val h)
    exact ⟨bestAt_swap pos hpos_ne_p hpos_ne_q π hbest,
      isMinInFirst_swap hm hne π hmin⟩
  · intro π₁ _ π₂ _ h
    -- swap is an involution, so apply it again on both sides
    have h₁ : swapValues (liftFirst hm p) (liftFirst hm q) (swapValues (liftFirst hm p) (liftFirst hm q) π₁)
        = swapValues (liftFirst hm p) (liftFirst hm q) (swapValues (liftFirst hm p) (liftFirst hm q) π₂) := by
      rw [h]
    simpa [swapValues_involutive] using h₁
  · intro π hπ
    rw [bestMinSet, Finset.mem_filter] at hπ
    rcases hπ with ⟨hπu, hbest, hmin⟩
    have hpos_ne_p : liftFirst hm p ≠ pos := by
      intro h
      have : p.val < pos.val := by omega
      exact (ne_of_lt this) (congrArg Fin.val h)
    have hpos_ne_q : liftFirst hm q ≠ pos := by
      intro h
      have : q.val < pos.val := by omega
      exact (ne_of_lt this) (congrArg Fin.val h)
    refine ⟨swapValues (liftFirst hm p) (liftFirst hm q) π, ?_, ?_⟩
    · rw [bestMinSet, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact ⟨bestAt_swap pos hpos_ne_p hpos_ne_q π hbest,
        by simpa [swapValues_comm] using isMinInFirst_swap hm (Ne.symm hne) π hmin⟩
    · simp [swapValues_involutive]

/-- The sets `bestMinSet ... p` for `p : Fin m` partition the best-at-`pos`
permutations, so their counts sum to the number of best-at-`pos` permutations. -/
lemma sum_bestMinCount {n m : ℕ} (hm : m ≤ n) (hmpos : 0 < m) (pos : Fin n) :
    (∑ p : Fin m, bestMinCount n m hm pos p)
      = ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card := by
  have hpair : (((Finset.univ : Finset (Fin m)) : Set (Fin m))).PairwiseDisjoint
      (fun p => bestMinSet n m hm pos p) := by
    simpa using bestMinSet_disjoint hm pos
  calc
    (∑ p : Fin m, bestMinCount n m hm pos p)
        = ∑ p : Fin m, (bestMinSet n m hm pos p).card := by simp [bestMinCount]
    _ = (Finset.biUnion Finset.univ (fun p : Fin m => bestMinSet n m hm pos p)).card := by
      rw [Finset.card_biUnion (h := hpair)]
    _ = ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card := by
      rw [bestMinSet_cover hm hmpos pos]

/-- The number of best-at-`pos` permutations is the same for every position:
swapping the scores at `a` and `b` maps the score-`0`-at-`a` permutations
bijectively onto the score-`0`-at-`b` permutations. -/
lemma card_bestAt_eq (n : ℕ) (a b : Fin n) :
    ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π a).val = 0)).card
      = ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π b).val = 0)).card := by
  classical
  apply Finset.card_bij (fun π hπ => swapValues a b π) ?_ ?_ ?_
  · intro π hπ
    rw [Finset.mem_filter] at hπ ⊢
    rcases hπ with ⟨hπu, h⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold swapValues
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right]
    exact h
  · intro π₁ _ π₂ _ h
    have h₁ : swapValues a b (swapValues a b π₁) = swapValues a b (swapValues a b π₂) := by
      rw [h]
    simpa [swapValues_involutive] using h₁
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    rcases hπ with ⟨hπu, h⟩
    refine ⟨swapValues a b π, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      unfold swapValues
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      exact h
    · simp [swapValues_involutive]

/-- Each permutation has score `0` at exactly one position, so the best-at-`a`
counts over all positions sum to `n!` (for `0 < n`, so that `Fin n` is
nonempty). -/
lemma sum_card_bestAt (n : ℕ) (hn : 0 < n) :
    (∑ a : Fin n, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π a).val = 0)).card)
      = n.factorial := by
  classical
  haveI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  calc
    (∑ a : Fin n, ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π a).val = 0)).card)
        = ∑ a : Fin n, ∑ π : Equiv.Perm (Fin n), (if (π a).val = 0 then (1 : ℕ) else 0) := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [Finset.card_filter]
    _ = ∑ π : Equiv.Perm (Fin n), ∑ a : Fin n, (if (π a).val = 0 then (1 : ℕ) else 0) := by
          rw [Finset.sum_comm]
    _ = ∑ π : Equiv.Perm (Fin n), (1 : ℕ) := by
          refine Finset.sum_congr rfl (fun π _ => ?_)
          let a0 : Fin n := π.symm (0 : Fin n)
          have hmem : (π a0).val = 0 := by simp [a0]
          have hiff : ∀ a : Fin n, (π a).val = 0 ↔ a = a0 := by
            intro a
            constructor
            · intro h
              have hπeq : π a = π a0 := by
                apply Fin.ext
                rw [h, hmem]
              exact (Equiv.bijective π).1 hπeq
            · intro h; rw [h]; exact hmem
          calc
            ∑ a : Fin n, (if (π a).val = 0 then (1 : ℕ) else 0)
                = ∑ a : Fin n, (if a = a0 then (1 : ℕ) else 0) := by
                  refine Finset.sum_congr rfl (fun a _ => ?_)
                  exact if_congr (hiff a) rfl rfl
            _ = 1 := by simp
    _ = n.factorial := by
          simp [Fintype.card_perm]

/-! ## The per-position probabilities

We combine the counting lemmas into the two probabilities the closed form
needs: score `0` is at `pos` with probability `1/n`, and (given the minimum of
the first `m` positions is at `p`) that joint event has probability `1/(nm)`.
-/

/-- A position other than the best has nonzero score. -/
lemma val_ne_zero_of_ne_best {n : ℕ} (j i : Fin n) (π : Equiv.Perm (Fin n))
    (hbest : (π j).val = 0) (hne : i ≠ j) : (π i).val ≠ 0 := by
  intro h
  apply hne
  apply π.injective
  apply Fin.ext
  rw [hbest, h]

/-- The real-valued sum of indicators over a finite type is the cardinality of
the corresponding filtered set. -/
lemma sum_indicator_eq_card {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p] :
    (∑ a : α, indicator (p a)) = (((Finset.univ : Finset α).filter p).card : ℝ) := by
  unfold indicator
  rw [Finset.card_filter]
  push_cast
  rfl

/-- **The best score `0` is at position `pos` with probability `1/n`**, by the
uniformity of the position of score `0` over the `n` positions. -/
theorem prob_bestAt (n : ℕ) (pos : Fin n) (hn : 0 < n) :
    fintypeExpect (fun π : Equiv.Perm (Fin n) => indicator ((π pos).val = 0)) = 1 / (n : ℝ) := by
  classical
  have hfac_card : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (n.factorial : ℝ) := by
    rw [Fintype.card_perm]
    simp
  have hnum : (∑ π : Equiv.Perm (Fin n), indicator ((π pos).val = 0))
      = (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card : ℝ) := by
    exact sum_indicator_eq_card (fun π : Equiv.Perm (Fin n) => (π pos).val = 0)
  rw [fintypeExpect, hnum, hfac_card]
  let c : ℕ := ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card
  have h_uniform : (∑ a : Fin n, (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π a).val = 0)).card : ℝ))
      = (n : ℝ) * (c : ℝ) := by
    calc
      (∑ a : Fin n, (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π a).val = 0)).card : ℝ))
          = ∑ a : Fin n, (c : ℝ) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            have h := card_bestAt_eq n a pos
            exact_mod_cast h
      _ = (n : ℝ) * (c : ℝ) := by simp
  have h_sum : (∑ a : Fin n, (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π a).val = 0)).card : ℝ))
      = (n.factorial : ℝ) := by
    exact_mod_cast sum_card_bestAt n hn
  have h_eq : (n : ℝ) * (c : ℝ) = (n.factorial : ℝ) := by
    rw [← h_uniform]
    exact h_sum
  have hposn : (n : ℝ) ≠ 0 := by positivity
  have hposfact : (n.factorial : ℝ) ≠ 0 := by positivity
  have hfrac : (c : ℝ) / (n.factorial : ℝ) = 1 / (n : ℝ) := by
    field_simp [hposn, hposfact]
    linarith [h_eq]
  change (c : ℝ) / (n.factorial : ℝ) = 1 / (n : ℝ)
  exact hfrac

/-- **Given score `0` at `pos` and the minimum of the first `m` positions at
`p`, the probability is `1/(n·m)`**: the joint event counts, for each of the
`n` choices of the position of score `0` and the `m` choices of the minimum
position, the same number of permutations. -/
theorem prob_bestMin (n m : ℕ) (hm : m ≤ n) (hmpos : 0 < m) (pos : Fin n) (hpos : m ≤ pos.val)
    (hn : 0 < n) (p : Fin m) :
    fintypeExpect (fun π : Equiv.Perm (Fin n) =>
      indicator ((π pos).val = 0 ∧ isMinInFirst hm π p))
    = (1 : ℝ) / (n : ℝ) * (1 : ℝ) / (m : ℝ) := by
  classical
  have hfac_card : (Fintype.card (Equiv.Perm (Fin n)) : ℝ) = (n.factorial : ℝ) := by
    rw [Fintype.card_perm]
    simp
  have hnum : (∑ π : Equiv.Perm (Fin n), indicator ((π pos).val = 0 ∧ isMinInFirst hm π p))
      = (bestMinCount n m hm pos p : ℝ) := by
    rw [bestMinCount, bestMinSet]
    exact sum_indicator_eq_card (fun π : Equiv.Perm (Fin n) => (π pos).val = 0 ∧ isMinInFirst hm π p)
  rw [fintypeExpect, hnum, hfac_card]
  let T : ℕ := bestMinCount n m hm pos p
  have h_uniform : (∑ q : Fin m, (bestMinCount n m hm pos q : ℝ)) = (m : ℝ) * (T : ℝ) := by
    calc
      (∑ q : Fin m, (bestMinCount n m hm pos q : ℝ))
          = ∑ q : Fin m, (T : ℝ) := by
            refine Finset.sum_congr rfl (fun q _ => ?_)
            have h : bestMinCount n m hm pos p = bestMinCount n m hm pos q := by
              by_cases hpq : p = q
              · subst q; rfl
              · exact bestMinCount_eq hm pos hpos hpq
            exact_mod_cast h.symm
      _ = (m : ℝ) * (T : ℝ) := by simp
  have h_sum : (∑ q : Fin m, (bestMinCount n m hm pos q : ℝ))
      = (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card : ℝ) := by
    exact_mod_cast sum_bestMinCount hm hmpos pos
  have h_eq : (m : ℝ) * (T : ℝ)
      = (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card : ℝ) := by
    rw [← h_uniform]
    exact h_sum
  -- restate prob_bestAt as `#(bestAt pos)/n! = 1/n`
  have h_pb : (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card : ℝ)
      / (n.factorial : ℝ) = 1 / (n : ℝ) := by
    have h' := prob_bestAt n pos hn
    rw [fintypeExpect, hfac_card] at h'
    have hnum' : (∑ π : Equiv.Perm (Fin n), indicator ((π pos).val = 0))
        = (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card : ℝ) := by
      exact sum_indicator_eq_card (fun π : Equiv.Perm (Fin n) => (π pos).val = 0)
    rw [hnum'] at h'
    exact h'
  have hposn : (n : ℝ) ≠ 0 := by positivity
  have hposm : (m : ℝ) ≠ 0 := by positivity
  have hposfact : (n.factorial : ℝ) ≠ 0 := by positivity
  have hfrac : (T : ℝ) / (n.factorial : ℝ) = (1 : ℝ) / (n : ℝ) * (1 : ℝ) / (m : ℝ) := by
    field_simp [hposn, hposm, hposfact]
    -- goal: T * n * m = n! ; from h_eq: m·T = B and h_pb: B/n! = 1/n
    have h_pb_mul : (((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun π => (π pos).val = 0)).card : ℝ)
        * (n : ℝ) = (n.factorial : ℝ) := by
      field_simp [hposn, hposfact] at h_pb
      exact h_pb
    nlinarith [h_eq, h_pb_mul]
  change (T : ℝ) / (n.factorial : ℝ) = (1 : ℝ) / (n : ℝ) * (1 : ℝ) / (m : ℝ)
  exact hfrac

/-! ## Characterizing when the best candidate is hired

Given the best candidate is at position `j`, the strategy hires it exactly when
no record occurs in positions `{k, ..., j-1}`.  A record is a left-to-right
minimum of the scores, so this is equivalent to the minimum score among the
first `j.val` positions already being achieved at a position below `k`. -/

/-- The minimum score among the first `j.val` positions is achieved at a
position below the threshold `k`. -/
def minInFirstK (n k : ℕ) (j : Fin n) (hkj : k ≤ j.val) (hjn : j.val ≤ n)
    (π : Equiv.Perm (Fin n)) : Prop :=
  ∃ p : Fin k, isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩

/-- `minInFirstK` is decidable: it is a finite existential over `Fin k`. -/
instance minInFirstK_decidable (n k : ℕ) (j : Fin n) (hkj : k ≤ j.val) (hjn : j.val ≤ n)
    (π : Equiv.Perm (Fin n)) : Decidable (minInFirstK n k j hkj hjn π) := by
  unfold minInFirstK
  infer_instance

/-- **Best-candidate characterization.**  The strategy hires the best candidate
at position `j` if and only if the best is at `j` and the minimum score among
the first `j.val` positions is among the first `k` positions. -/
theorem hiringStrategy_some_iff_minInFirstK (n k : ℕ) (hk : 0 < k) (j : Fin n) (hkj : k ≤ j.val)
    (hjn : j.val ≤ n) (π : Equiv.Perm (Fin n)) :
    (hiringStrategy k π = some j ∧ isAbsoluteBest π j) ↔
      (isAbsoluteBest π j ∧ minInFirstK n k j hkj hjn π) := by
  classical
  constructor
  · intro h
    rcases h with ⟨hsj, hbest⟩
    refine ⟨hbest, ?_⟩
    have hs := hiringStrategy_some_iff.mp hsj
    rcases hs with ⟨_, _, hno_rec⟩
    have hjpos : 0 < j.val := lt_of_lt_of_le hk hkj
    rcases isMinInFirst_exists hjn hjpos π with ⟨m, hm⟩
    have hmln : m.val < n := lt_of_lt_of_le m.isLt hjn
    have hk_le_m : ¬ k ≤ m.val := by
      intro hkm
      have hrec_m : isRecordAt π ⟨m.val, hmln⟩ := by
        unfold isRecordAt
        intro i hi
        change i.val < m.val at hi
        exact isMinInFirst_lt hjn π m hm i (lt_trans hi m.isLt)
          (by intro h
              have hval : m.val = i.val := by simpa [liftFirst] using congrArg Fin.val h.symm
              exact (ne_of_lt hi) hval.symm)
      have hjm : j ≤ ⟨m.val, hmln⟩ := hno_rec ⟨m.val, hmln⟩ hkm hrec_m
      have hjm_val : j.val ≤ m.val := Fin.le_def.mp hjm
      omega
    exact ⟨⟨m.val, lt_of_not_ge hk_le_m⟩, hm⟩
  · intro h
    rcases h with ⟨hbest, hmin⟩
    refine ⟨?_, hbest⟩
    refine (hiringStrategy_some_iff.mpr ⟨hkj, ?_, ?_⟩)
    · unfold isRecordAt
      intro i hi
      have h0 : (π i).val ≠ 0 := by
        apply val_ne_zero_of_ne_best j i π hbest
        intro hij
        have : i.val = j.val := congrArg Fin.val hij
        omega
      have hpos : 0 < (π i).val := Nat.pos_of_ne_zero h0
      rw [hbest]
      exact hpos
    · intro i hki hrec_i
      by_contra hji
      have hiltj : i.val < j.val := Fin.lt_def.mp (lt_of_not_ge hji)
      rcases hmin with ⟨p, hp⟩
      have hplj : p.val < j.val := lt_of_lt_of_le p.isLt hkj
      have hplti : p.val < i.val := by omega
      have hne : i ≠ liftFirst hjn ⟨p.val, hplj⟩ := by
        intro h
        have : p.val = i.val := congrArg Fin.val h.symm
        omega
      have hlt : (π ⟨p.val, lt_of_lt_of_le hplj hjn⟩).val < (π i).val :=
        isMinInFirst_lt hjn π ⟨p.val, hplj⟩ hp i hiltj hne
      have hpln : p.val < n := lt_of_lt_of_le hplj hjn
      have hlt2 : (π i).val < (π ⟨p.val, hpln⟩).val := hrec_i ⟨p.val, hpln⟩ hplti
      exact (lt_asymm hlt (by simpa using hlt2)).elim

/-- The indicator of `minInFirstK` is the sum over `p : Fin k` of the
indicators of the individual minimum positions (the minimum is unique). -/
lemma indicator_minInFirstK_eq (n k : ℕ) (hk : 0 < k) (j : Fin n) (hkj : k ≤ j.val)
    (hjn : j.val ≤ n) (π : Equiv.Perm (Fin n)) :
    indicator (minInFirstK n k j hkj hjn π)
      = ∑ p : Fin k, indicator (isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩) := by
  classical
  unfold minInFirstK indicator
  by_cases h : ∃ p : Fin k, isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩
  · rcases h with ⟨p0, hp0⟩
    have honly : ∀ p : Fin k, isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩ ↔ p = p0 := by
      intro p
      constructor
      · intro hpp
        have he := isMinInFirst_unique hjn π hpp hp0
        exact Fin.ext (by simpa using congrArg Fin.val he)
      · intro hpp; subst p; exact hp0
    have hsum : (∑ p : Fin k, indicator (isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)) = 1 := by
      have hre : (∑ p : Fin k, indicator (isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩))
          = ∑ p : Fin k, indicator (p = p0) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        unfold indicator
        exact if_congr (honly p) rfl rfl
      rw [hre]
      simp [indicator]
    rw [if_pos ⟨p0, hp0⟩]
    exact hsum.symm
  · have hsum : (∑ p : Fin k, indicator (isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have : ¬ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩ := by
        intro hpp
        exact h ⟨p, hpp⟩
      simp [indicator, this]
    rw [if_neg h]
    exact hsum.symm

/-! ## The closed form

Combining the per-position probability with the harmonic sum gives the
textbook closed form for the on-line hiring success probability. -/

/-- The event "the strategy hires the best at position `j`" is decidable. -/
noncomputable instance hiringStrategy_best_decidable (n k : ℕ) (j : Fin n) (π : Equiv.Perm (Fin n)) :
    Decidable (hiringStrategy k π = some j ∧ isAbsoluteBest π j) :=
  Classical.propDecidable _

/-- **Per-position success probability.**  The probability that the strategy
hires the best candidate at position `j` is `k/(n·j.val)`: the best is at `j`
with probability `1/n`, and given that, the minimum of the first `j.val`
positions is below `k` with probability `k/j.val`. -/
theorem probBestAt (n k : ℕ) (hk : 0 < k) (j : Fin n) (hkj : k ≤ j.val) :
    fintypeExpect (fun π : Equiv.Perm (Fin n) =>
      indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j))
    = (1 : ℝ) / (n : ℝ) * (k : ℝ) / (j.val : ℝ) := by
  classical
  let hjn : j.val ≤ n := j.isLt.le
  have hn : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le hk hkj) j.isLt.le
  have hrewrite :
      fintypeExpect (fun π => indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j))
      = fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ minInFirstK n k j hkj hjn π)) := by
    apply congrArg fintypeExpect
    funext π
    unfold indicator
    exact if_congr (hiringStrategy_some_iff_minInFirstK n k hk j hkj hjn π) rfl rfl
  rw [hrewrite]
  have hsplit : ∀ π : Equiv.Perm (Fin n),
      indicator (isAbsoluteBest π j ∧ minInFirstK n k j hkj hjn π)
      = ∑ p : Fin k, indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩) := by
    intro π
    have hmul : indicator (isAbsoluteBest π j ∧ minInFirstK n k j hkj hjn π)
        = indicator (isAbsoluteBest π j) * indicator (minInFirstK n k j hkj hjn π) := by
      by_cases hb : isAbsoluteBest π j <;> by_cases hmin : minInFirstK n k j hkj hjn π <;> simp [indicator, hb, hmin]
    rw [hmul]
    rw [indicator_minInFirstK_eq n k hk j hkj hjn π]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hb : isAbsoluteBest π j <;> by_cases hmin : isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩ <;> simp [indicator, hb, hmin]
  have hEsum : fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ minInFirstK n k j hkj hjn π))
      = ∑ p : Fin k, fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)) := by
    rw [show fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ minInFirstK n k j hkj hjn π))
        = fintypeExpect (fun π => ∑ p : Fin k, indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)) from by
          apply congrArg fintypeExpect
          funext π
          exact hsplit π]
    simpa [fintypeExpect_sum]
  rw [hEsum]
  have hterm : ∀ p : Fin k,
      fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩))
      = (1 : ℝ) / (n : ℝ) * (1 : ℝ) / (j.val : ℝ) := by
    intro p
    have hif : ∀ π, indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)
        = indicator ((π j).val = 0 ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩) := by
      intro π
      unfold indicator
      exact if_congr Iff.rfl rfl rfl
    have heq : fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩))
        = fintypeExpect (fun π => indicator ((π j).val = 0 ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)) := by
      apply congrArg fintypeExpect
      funext π
      exact hif π
    rw [heq]
    exact prob_bestMin n (j.val) hjn (lt_of_lt_of_le hk hkj) j (le_refl (j.val)) hn ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩
  rw [show (∑ p : Fin k, fintypeExpect (fun π => indicator (isAbsoluteBest π j ∧ isMinInFirst hjn π ⟨p.val, lt_of_lt_of_le p.isLt hkj⟩)))
      = (k : ℝ) * ((1 : ℝ) / (n : ℝ) * (1 : ℝ) / (j.val : ℝ)) from by
        rw [Finset.sum_congr rfl (fun p _ => hterm p)]
        simp]
  ring

/-- The sum `Σ_{j=k}^{n-1} 1/j` equals the harmonic difference `H_{n-1} - H_{k-1}`. -/
lemma sum_recip_Icc_eq_harmonic_sub (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ∑ j ∈ Finset.Icc k (n - 1), (1 : ℝ) / (j : ℝ) = (harmonic (n - 1) : ℝ) - (harmonic (k - 1) : ℝ) := by
  have hharm : ∀ m : ℕ, (harmonic m : ℝ) = ∑ i ∈ Finset.range m, (1 : ℝ) / ((i : ℝ) + 1) := by
    intro m
    unfold harmonic
    simp [one_div]
  have hset : Finset.Icc k (n - 1) = Finset.Ico k n := by
    ext j
    constructor
    · intro hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_Ico]
      rcases hj with ⟨hkj, hjn1⟩
      refine ⟨hkj, ?_⟩
      omega
    · intro hj
      rw [Finset.mem_Ico] at hj
      rw [Finset.mem_Icc]
      rcases hj with ⟨hkj, hjn⟩
      refine ⟨hkj, ?_⟩
      omega
  calc
    ∑ j ∈ Finset.Icc k (n - 1), (1 : ℝ) / (j : ℝ)
        = ∑ j ∈ Finset.Ico k n, (1 : ℝ) / (j : ℝ) := by rw [hset]
    _ = (harmonic (n - 1) : ℝ) - (harmonic (k - 1) : ℝ) := by
          have hleft : ∑ j ∈ Finset.Ico k n, (1 : ℝ) / (j : ℝ)
              = ∑ t ∈ Finset.range (n - k), (1 : ℝ) / ((k + t : ℕ) : ℝ) := by
            rw [Finset.sum_Ico_eq_sum_range]
          have hright : (harmonic (n - 1) : ℝ) - (harmonic (k - 1) : ℝ)
              = ∑ t ∈ Finset.range (n - k), (1 : ℝ) / ((k + t : ℕ) : ℝ) := by
            rw [hharm (n - 1), hharm (k - 1)]
            rw [← Finset.sum_Ico_eq_sub (f := fun i : ℕ => (1 : ℝ) / ((i : ℝ) + 1)) (m := k - 1) (n := n - 1) (by omega : k - 1 ≤ n - 1)]
            rw [Finset.sum_Ico_eq_sum_range]
            have hsub : (n - 1) - (k - 1) = n - k := by omega
            rw [hsub]
            refine Finset.sum_congr rfl (fun t _ => ?_)
            have hden : (↑((k - 1) + t) : ℝ) + 1 = ↑(k + t) := by
              have hnat : ((k - 1) + t) + 1 = k + t := by omega
              exact_mod_cast hnat
            rw [hden]
          rw [hleft, hright]

/-- **On-line hiring closed form (CLRS §5.4.4).**  The success probability of
the threshold strategy that observes the first `k` candidates and then hires
the first record is `(k/n) · (H_{n-1} - H_{k-1})`. -/
theorem probHireBest_eq (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    probHireBest n k = (k : ℝ) / (n : ℝ) * ((harmonic (n - 1) : ℝ) - (harmonic (k - 1) : ℝ)) := by
  classical
  have hn : 0 < n := lt_of_lt_of_le hk hkn
  have hsuccess : ∀ π : Equiv.Perm (Fin n),
      (match hiringStrategy k π with
        | some i => if isAbsoluteBest π i then 1 else 0
        | none => 0)
      = ∑ j : Fin n, indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j) := by
    intro π
    by_cases hs : ∃ j0 : Fin n, hiringStrategy k π = some j0
    · rcases hs with ⟨j0, hsj0⟩
      have hL : (match hiringStrategy k π with
          | some i => if isAbsoluteBest π i then (1 : ℝ) else 0
          | none => 0) = if isAbsoluteBest π j0 then (1 : ℝ) else 0 := by
        rw [hsj0]
      have hR : (∑ j : Fin n, indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j))
          = if isAbsoluteBest π j0 then (1 : ℝ) else 0 := by
        have h0 : indicator (hiringStrategy k π = some j0 ∧ isAbsoluteBest π j0)
            = if isAbsoluteBest π j0 then (1 : ℝ) else 0 := by
          simp [indicator, hsj0]
        rw [← h0]
        exact Finset.sum_eq_single (s := Finset.univ) (a := j0)
          (by intro j _ hne
              have hnot : ¬ (hiringStrategy k π = some j ∧ isAbsoluteBest π j) := by
                intro h
                rcases h with ⟨hsj, _⟩
                exact hne (Option.some.inj (hsj0.symm.trans hsj)).symm
              simp [indicator, hnot])
          (by intro hj0; exact False.elim (hj0 (Finset.mem_univ _)))
      exact hL.trans hR.symm
    · have hnone : hiringStrategy k π = none := by
        cases hg : hiringStrategy k π with
        | none => rfl
        | some j => exact False.elim (hs ⟨j, hg⟩)
      have hL : (match hiringStrategy k π with
          | some i => if isAbsoluteBest π i then (1 : ℝ) else 0
          | none => 0) = 0 := by
        rw [hnone]
      have hR : (∑ j : Fin n, indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j)) = 0 := by
        have hnot : ∀ j : Fin n, ¬ (hiringStrategy k π = some j ∧ isAbsoluteBest π j) := by
          intro j h
          rcases h with ⟨hsj, _⟩
          rw [hnone] at hsj
          simp at hsj
        rw [Finset.sum_eq_zero]
        intro j _
        simp [indicator, hnot j]
      exact hL.trans hR.symm
  have hsum : probHireBest n k
      = ∑ j : Fin n, fintypeExpect (fun π : Equiv.Perm (Fin n) =>
          indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j)) := by
    unfold probHireBest
    rw [show fintypeExpect (fun π : Equiv.Perm (Fin n) =>
          (match hiringStrategy k π with
            | some i => if isAbsoluteBest π i then 1 else 0
            | none => 0))
        = fintypeExpect (fun π : Equiv.Perm (Fin n) =>
            ∑ j : Fin n, indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j)) from by
          apply congrArg fintypeExpect
          funext π
          exact hsuccess π]
    rw [fintypeExpect_sum (S := Finset.univ)
      (f := fun j π => indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j))]
  rw [hsum]
  have hterm_zero : ∀ j : Fin n, j.val < k →
      fintypeExpect (fun π => indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j)) = 0 := by
    intro j hjlt
    have hzero : ∀ π, indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j) = 0 := by
      intro π
      have hnot : ¬ (hiringStrategy k π = some j ∧ isAbsoluteBest π j) := by
        intro h
        rcases h with ⟨hsj, _⟩
        have hk_le : k ≤ j.val := hiringStrategy_after_observation hsj
        omega
      simp [indicator, hnot]
    have hcongr : fintypeExpect (fun π => indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j))
        = fintypeExpect (fun π : Equiv.Perm (Fin n) => (0 : ℝ)) := by
      apply congrArg fintypeExpect
      funext π
      exact hzero π
    rw [hcongr]
    rw [fintypeExpect_const Fintype.card_ne_zero]
  have hsum_range :
      (∑ j : Fin n, fintypeExpect (fun π => indicator (hiringStrategy k π = some j ∧ isAbsoluteBest π j)))
      = ∑ m ∈ Finset.range n, (if m < k then (0 : ℝ) else (1 : ℝ) / (n : ℝ) * (k : ℝ) / (m : ℝ)) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    have hmn : m < n := Finset.mem_range.mp hm
    rw [dif_pos hmn]
    by_cases hmk : m < k
    · simp [hmk, hterm_zero ⟨m, hmn⟩ hmk]
    · have hterm := probBestAt n k hk ⟨m, hmn⟩ (Nat.le_of_not_lt hmk)
      simp [hmk, hterm]
  rw [hsum_range]
  have hdrop :
      (∑ m ∈ Finset.range n, (if m < k then (0 : ℝ) else (1 : ℝ) / (n : ℝ) * (k : ℝ) / (m : ℝ)))
      = ∑ m ∈ Finset.Icc k (n - 1), (1 : ℝ) / (n : ℝ) * (k : ℝ) / (m : ℝ) := by
    have hite : (∑ m ∈ Finset.range n, (if m < k then (0 : ℝ) else (1 : ℝ) / (n : ℝ) * (k : ℝ) / (m : ℝ)))
        = ∑ m ∈ Finset.range n, (if ¬ m < k then (1 : ℝ) / (n : ℝ) * (k : ℝ) / (m : ℝ) else (0 : ℝ)) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      by_cases hmk : m < k <;> simp [hmk]
    rw [hite]
    rw [← Finset.sum_filter]
    have hset : (Finset.range n).filter (fun m => ¬ m < k) = Finset.Icc k (n - 1) := by
      ext m
      constructor
      · intro hm
        rw [Finset.mem_filter, Finset.mem_range] at hm
        rw [Finset.mem_Icc]
        rcases hm with ⟨hmn, hk_le⟩
        refine ⟨Nat.le_of_not_lt hk_le, ?_⟩
        omega
      · intro hm
        rw [Finset.mem_Icc] at hm
        rw [Finset.mem_filter, Finset.mem_range]
        rcases hm with ⟨hkm, hmn1⟩
        refine ⟨by omega, ?_⟩
        exact Nat.not_lt_of_ge hkm
    rw [hset]
  rw [hdrop]
  have hfactor :
      (∑ m ∈ Finset.Icc k (n - 1), (1 : ℝ) / (n : ℝ) * (k : ℝ) / (m : ℝ))
      = (k : ℝ) / (n : ℝ) * (∑ m ∈ Finset.Icc k (n - 1), (1 : ℝ) / (m : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    field_simp
  rw [hfactor]
  rw [sum_recip_Icc_eq_harmonic_sub k n hk hkn]

/-! ## The `1/e` asymptotic

The classic secretary-problem optimum threshold `k ≈ n/e` makes the success
probability tend to `1/e` (CLRS §5.4.4).  The closed form
{name}`probHireBest_eq` gives `(k/n)(H_{n-1} - H_{k-1})`; the factor `k/n`
tends to `1/e` (floor asymptotics), and the harmonic difference tends to `1`
(the Euler-Mascheroni asymptotics of the harmonic numbers cancel the shared
`γ`, leaving `log(n/k) → log e = 1`).
-/

/-- Euler's number `e`. -/
noncomputable def e0 : ℝ := Real.exp 1
noncomputable section

/-- The optimal threshold `⌊n/e⌋`. -/
def optThreshold (n : ℕ) : ℕ := ⌊(n : ℝ) / e0⌋₊

/-- `e > 0`. -/
lemma e0_pos : 0 < e0 := by
  unfold e0
  positivity

/-- `e ≠ 0`. -/
lemma e0_ne_zero : e0 ≠ 0 := ne_of_gt e0_pos

/-- `log e = 1`. -/
lemma log_e0 : Real.log e0 = 1 := by
  unfold e0
  rw [Real.log_exp]

/-- `(n : ℝ) / e` tends to infinity. -/
lemma tendsto_div_e0_atTop : Tendsto (fun n : ℕ => (n : ℝ) / e0) atTop atTop := by
  simpa [div_eq_mul_inv] using
    (Filter.Tendsto.atTop_mul_const (inv_pos.mpr e0_pos) tendsto_natCast_atTop_atTop)

/-- `⌊n/e⌋` tends to infinity. -/
lemma tendsto_optThreshold_atTop : Tendsto (fun n : ℕ => optThreshold n) atTop atTop := by
  unfold optThreshold
  exact tendsto_nat_floor_atTop.comp tendsto_div_e0_atTop

/-- `⌊n/e⌋ / n` tends to `1/e`. -/
lemma tendsto_optThreshold_div_n :
    Tendsto (fun n : ℕ => (optThreshold n : ℝ) / (n : ℝ)) atTop (𝓝 (1 / e0)) := by
  let x : ℕ → ℝ := fun n => (n : ℝ) / e0
  have hx_atTop : Tendsto x atTop atTop := tendsto_div_e0_atTop
  have hf : Tendsto (fun n : ℕ => (⌊x n⌋₊ : ℝ) / x n) atTop (𝓝 1) :=
    tendsto_nat_floor_div_atTop.comp hx_atTop
  have hg : Tendsto (fun n : ℕ => x n / (n : ℝ)) atTop (𝓝 (1 / e0)) := by
    have h : (fun n : ℕ => x n / (n : ℝ)) =ᶠ[atTop] fun _ : ℕ => 1 / e0 := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      unfold x
      field_simp [e0_ne_zero, (show (n : ℝ) ≠ 0 from by exact_mod_cast (Nat.ne_of_gt hn))]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 / e0) atTop (𝓝 (1 / e0))).congr' h.symm
  have hmul : Tendsto (fun n : ℕ => (⌊x n⌋₊ : ℝ) / x n * (x n / (n : ℝ))) atTop (𝓝 (1 * (1 / e0))) :=
    hf.mul hg
  have hid : (fun n : ℕ => (⌊x n⌋₊ : ℝ) / x n * (x n / (n : ℝ))) =ᶠ[atTop]
      fun n : ℕ => (optThreshold n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hx0 : x n ≠ 0 := by
      unfold x
      exact div_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) e0_ne_zero
    field_simp [hx0, (show (n : ℝ) ≠ 0 from by exact_mod_cast (Nat.ne_of_gt hn))]
    unfold optThreshold x
    ring
  simpa using hmul.congr' hid

/-- `log (n - 1) - log n` tends to `0`. -/
lemma tendsto_log_pred_sub_log :
    Tendsto (fun n : ℕ => Real.log (n - 1 : ℕ) - Real.log (n : ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_log_comp_add_sub_log (-1 : ℝ)
  have h' : Tendsto (fun n : ℕ => Real.log ((n : ℝ) - 1) - Real.log (n : ℝ)) atTop (𝓝 0) :=
    h.comp tendsto_natCast_atTop_atTop
  have hid : (fun n : ℕ => Real.log ((n : ℝ) - 1) - Real.log (n : ℝ)) =ᶠ[atTop]
      fun n : ℕ => Real.log (n - 1 : ℕ) - Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hcast : ((n : ℝ) - 1) = (n - 1 : ℕ) := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hcast]
  exact h'.congr' hid

/-- `log (n - 1) - log n` over the threshold tends to `0`. -/
lemma tendsto_log_opt_pred_sub_log :
    Tendsto (fun n : ℕ => Real.log (optThreshold n - 1 : ℕ) - Real.log (optThreshold n : ℝ)) atTop (𝓝 0) := by
  have h := Real.tendsto_log_comp_add_sub_log (-1 : ℝ)
  have h' : Tendsto (fun n : ℕ => Real.log ((n : ℝ) - 1) - Real.log (n : ℝ)) atTop (𝓝 0) :=
    h.comp tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun n : ℕ =>
      Real.log ((optThreshold n : ℝ) - 1) - Real.log (optThreshold n : ℝ)) atTop (𝓝 0) :=
    h'.comp tendsto_optThreshold_atTop
  have hid : (fun n : ℕ => Real.log ((optThreshold n : ℝ) - 1) - Real.log (optThreshold n : ℝ)) =ᶠ[atTop]
      fun n : ℕ => Real.log (optThreshold n - 1 : ℕ) - Real.log (optThreshold n : ℝ) := by
    filter_upwards [tendsto_optThreshold_atTop.eventually_gt_atTop 0] with n hn
    have hcast : ((optThreshold n : ℝ) - 1) = (optThreshold n - 1 : ℕ) := by
      rw [Nat.cast_sub hn]
      norm_num
    rw [hcast]
  exact hcomp.congr' hid

/-- `log n - log ⌊n/e⌋` tends to `1`. -/
lemma tendsto_log_sub_log_opt :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) - Real.log (optThreshold n : ℝ)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) / (optThreshold n : ℝ)) atTop (𝓝 e0) := by
    have h := tendsto_optThreshold_div_n
    -- inverse of k/n → 1/e0 is n/k → e0
    have hinv : Tendsto (fun n : ℕ => (((optThreshold n : ℝ) / (n : ℝ))⁻¹)) atTop (𝓝 (1 / e0)⁻¹) :=
      h.inv₀ (ne_of_gt (one_div_pos.mpr e0_pos))
    have hb : (1 / e0)⁻¹ = e0 := by field_simp [e0_ne_zero]
    -- (k/n)⁻¹ = n/k
    have hid : (fun n : ℕ => (((optThreshold n : ℝ) / (n : ℝ))⁻¹)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / (optThreshold n : ℝ) := by
      filter_upwards [eventually_ge_atTop 1, tendsto_optThreshold_atTop.eventually_gt_atTop 0] with n hn hk
      field_simp [(show (optThreshold n : ℝ) ≠ 0 from by exact_mod_cast (Nat.ne_of_gt hk)),
        (show (n : ℝ) ≠ 0 from by exact_mod_cast (Nat.ne_of_gt hn))]
    have hgoal : Tendsto (fun n : ℕ => (n : ℝ) / (optThreshold n : ℝ)) atTop (𝓝 ((1 / e0)⁻¹)) :=
      hinv.congr' hid
    rw [hb] at hgoal
    exact hgoal
  -- log(n/k) → log e0 = 1
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) / (optThreshold n : ℝ))) atTop (𝓝 (Real.log e0)) :=
    (ContinuousAt.tendsto (Real.continuousAt_log e0_ne_zero)).comp hn
  have hid : (fun n : ℕ => Real.log ((n : ℝ) / (optThreshold n : ℝ))) =ᶠ[atTop]
      fun n : ℕ => Real.log (n : ℝ) - Real.log (optThreshold n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1, tendsto_optThreshold_atTop.eventually_gt_atTop 0] with n hn hk
    rw [Real.log_div (by exact_mod_cast (Nat.ne_of_gt hn)) (by exact_mod_cast (Nat.ne_of_gt hk))]
  simpa [log_e0] using hlog.congr' hid

/-- `log (n-1) - log ⌊n/e⌋-1` tends to `1`. -/
lemma tendsto_log_pred_sub_log_opt :
    Tendsto (fun n : ℕ => Real.log (n - 1 : ℕ) - Real.log (optThreshold n - 1 : ℕ)) atTop (𝓝 1) := by
  -- decompose: (log(n-1)-log n) + (log n - log k) + (log k - log(k-1))
  have h1 := tendsto_log_pred_sub_log
  have h2 := tendsto_log_sub_log_opt
  have h3 : Tendsto (fun n : ℕ => Real.log (optThreshold n : ℝ) - Real.log (optThreshold n - 1 : ℕ)) atTop (𝓝 0) := by
    have h := tendsto_log_opt_pred_sub_log
    simpa using h.neg
  have hsum : Tendsto (fun n : ℕ =>
      (Real.log (n - 1 : ℕ) - Real.log (n : ℝ))
        + (Real.log (n : ℝ) - Real.log (optThreshold n : ℝ))
        + (Real.log (optThreshold n : ℝ) - Real.log (optThreshold n - 1 : ℕ)))
      atTop (𝓝 (0 + 1 + 0)) :=
    (h1.add h2).add h3
  have hid : (fun n : ℕ =>
      (Real.log (n - 1 : ℕ) - Real.log (n : ℝ))
        + (Real.log (n : ℝ) - Real.log (optThreshold n : ℝ))
        + (Real.log (optThreshold n : ℝ) - Real.log (optThreshold n - 1 : ℕ)))
      =ᶠ[atTop] fun n : ℕ => Real.log (n - 1 : ℕ) - Real.log (optThreshold n - 1 : ℕ) := by
    filter_upwards with n
    ring
  simpa using hsum.congr' hid

/-- `H_{n-1} - H_{⌊n/e⌋-1}` tends to `1`. -/
lemma tendsto_harmonic_diff :
    Tendsto (fun n : ℕ => (harmonic (n - 1) : ℝ) - (harmonic (optThreshold n - 1) : ℝ))
      atTop (𝓝 1) := by
  let γ : ℝ := Real.eulerMascheroniConstant
  have hpred : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    rw [tendsto_atTop]
    intro m
    filter_upwards [eventually_ge_atTop (m + 1)] with n hn
    omega
  have hpred_opt : Tendsto (fun n : ℕ => optThreshold n - 1) atTop atTop :=
    hpred.comp tendsto_optThreshold_atTop
  have h_n : Tendsto (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log (n - 1 : ℕ)) atTop (𝓝 γ) := by
    have h := Real.tendsto_harmonic_sub_log.comp hpred
    change Tendsto (fun n : ℕ => (harmonic (n - 1) : ℝ) - Real.log (↑(n - 1) : ℝ)) atTop (𝓝 γ)
    exact h
  have h_k : Tendsto (fun n : ℕ => (harmonic (optThreshold n - 1) : ℝ) - Real.log (optThreshold n - 1 : ℕ)) atTop (𝓝 γ) := by
    have h := Real.tendsto_harmonic_sub_log.comp hpred_opt
    change Tendsto (fun n : ℕ => (harmonic (optThreshold n - 1) : ℝ) - Real.log (↑(optThreshold n - 1) : ℝ)) atTop (𝓝 γ)
    exact h
  have h_log := tendsto_log_pred_sub_log_opt
  have hcomb : Tendsto (fun n : ℕ =>
      ((harmonic (n - 1) : ℝ) - Real.log (n - 1 : ℕ))
        - ((harmonic (optThreshold n - 1) : ℝ) - Real.log (optThreshold n - 1 : ℕ))
        + (Real.log (n - 1 : ℕ) - Real.log (optThreshold n - 1 : ℕ)))
      atTop (𝓝 (γ - γ + 1)) :=
    (h_n.sub h_k).add h_log
  have hid : (fun n : ℕ =>
      ((harmonic (n - 1) : ℝ) - Real.log (n - 1 : ℕ))
        - ((harmonic (optThreshold n - 1) : ℝ) - Real.log (optThreshold n - 1 : ℕ))
        + (Real.log (n - 1 : ℕ) - Real.log (optThreshold n - 1 : ℕ)))
      =ᶠ[atTop] fun n : ℕ => (harmonic (n - 1) : ℝ) - (harmonic (optThreshold n - 1) : ℝ) := by
    filter_upwards with n
    ring
  simpa using hcomb.congr' hid

/-- **On-line hiring `1/e` asymptotic.**  Choosing the threshold `k = ⌊n/e⌋`
makes the success probability tend to `1/e` as `n → ∞` (CLRS §5.4.4). -/
theorem probHireBest_asymptotic :
    Tendsto (fun n : ℕ => probHireBest n (optThreshold n)) atTop (𝓝 (1 / e0)) := by
  have hk_pos : ∀ᶠ n in atTop, 0 < optThreshold n :=
    tendsto_optThreshold_atTop.eventually_gt_atTop 0
  have hk_le : ∀ᶠ n in atTop, optThreshold n ≤ n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold optThreshold
    have h1 : (⌊(n : ℝ) / e0⌋₊ : ℝ) ≤ (n : ℝ) / e0 := Nat.floor_le (div_nonneg (by positivity) (le_of_lt e0_pos))
    have h2 : (n : ℝ) / e0 ≤ (n : ℝ) := by
      have he1 : 1 ≤ e0 := by
        have hlt : (1 : ℝ) < e0 := by
          unfold e0
          simpa using (Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1))
        exact le_of_lt hlt
      exact (div_le_iff₀ e0_pos).mpr (by nlinarith [he1])
    exact_mod_cast (le_trans h1 h2)
  have hclosed : (fun n : ℕ => probHireBest n (optThreshold n)) =ᶠ[atTop]
      fun n : ℕ => (optThreshold n : ℝ) / (n : ℝ)
        * ((harmonic (n - 1) : ℝ) - (harmonic (optThreshold n - 1) : ℝ)) := by
    filter_upwards [hk_pos, hk_le] with n hpos hle
    rw [probHireBest_eq n (optThreshold n) hpos hle]
  have ht : Tendsto (fun n : ℕ => (optThreshold n : ℝ) / (n : ℝ)
      * ((harmonic (n - 1) : ℝ) - (harmonic (optThreshold n - 1) : ℝ)))
      atTop (𝓝 ((1 / e0) * 1)) :=
    tendsto_optThreshold_div_n.mul tendsto_harmonic_diff
  have hfinal : (1 / e0) * 1 = 1 / e0 := by ring
  simpa [hfinal] using ht.congr' hclosed.symm

end
end OnlineHiring

end Chapter05
end CLRS
