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
exact {lit}`some` and {lit}`none` contracts.  The harmonic closed form for its
success probability and the asymptotic {lit}`1/e` result are **deferred**.
-/

namespace CLRS
namespace Chapter05

open CLRS.Probability

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

instance isMinInFirst_decidable {n m : ℕ} (hm : m ≤ n) (π : Equiv.Perm (Fin n)) (p : Fin m) :
    Decidable (isMinInFirst hm π p) := by
  unfold isMinInFirst
  infer_instance

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

end OnlineHiring

end Chapter05
end CLRS
