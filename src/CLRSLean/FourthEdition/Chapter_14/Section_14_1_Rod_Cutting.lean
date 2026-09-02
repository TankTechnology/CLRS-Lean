import CLRSLean.Chapter_15.Section_15_1_Rod_Cutting

/-!
# Section 14.1 — Rod cutting

This section completes the fourth-edition §14.1 algorithm boundary for rod
cutting on top of the legacy recurrence and bottom-up table
({lit}`CLRSLean.Chapter_15.Section_15_1_Rod_Cutting`).  It adds the optimal-cut
reconstruction of `EXTENDED-BOTTOM-UP-CUT-ROD`, the top-down
`MEMOIZED-CUT-ROD` cache-threading algorithm, and the explicit `O(n²)` step
count of `BOTTOM-UP-CUT-ROD`.

Main results:

- Definition {lit}`rodCutFirstCut` and theorems {lit}`rodCutFirstCut_mem`,
  {lit}`rodCutFirstCut_le`, {lit}`rodCutFirstCut_value`: the optimal first cut
  {lit}`s` of `EXTENDED-BOTTOM-UP-CUT-ROD` is a valid cut in {lit}`1 .. n` and
  attains the recurrence maximum.
- Definition {lit}`rodCutPlan` and theorems {lit}`rodCutPlan_correct`,
  {lit}`rodCutPlan_optimal`: `PRINT-CUT-ROD-SOLUTION` rebuilds an optimal
  cutting plan of length {lit}`n`.
- Definition {lit}`rodCutStepCount` and theorems {lit}`rodCutStepCount_eq`,
  {lit}`rodCutStepCount_le_quadratic`: `BOTTOM-UP-CUT-ROD` performs exactly
  {lit}`n (n + 1) / 2` first-cut evaluations, an `O(n²)` bound.
- Definition {lit}`memoizedRodCut` and theorems {lit}`memoizedRodCut_value`,
  {lit}`memoizedRodCut_correct`: the top-down `MEMOIZED-CUT-ROD` cache-threading
  algorithm returns the optimal revenue and keeps its cache consistent.

Status: `proved` for cut reconstruction, top-down memoization, and the `O(n²)`
step-count cost analysis.  The mutable-array bottom-up refinement and the Bellman
recurrence remain in the legacy source.

Notation conventions used in this section:

- `price` : the price table {lit}`price n` = revenue of an uncut piece of length {lit}`n`
- `n` : the rod length
-/

namespace CLRS
namespace Chapter15

/-! ## Optimal-cut reconstruction (CLRS §14.1 EXTENDED-BOTTOM-UP-CUT-ROD) -/

/-- The candidate first cuts for a rod of length `n`, listed in increasing order
    as `[1, 2, ..., n]`. -/
def rodCutCandidates (n : Nat) : List Nat :=
  (List.range n).map (fun i => i + 1)

/-- Membership in the candidate list is exactly a valid first cut in `1 .. n`. -/
theorem mem_rodCutCandidates (n cut : Nat) :
    cut ∈ rodCutCandidates n ↔ cut ∈ Finset.Icc 1 n := by
  simp [rodCutCandidates, List.mem_map, List.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    refine ⟨cut - 1, ?_, ?_⟩
    · omega
    · omega

/-- Pick the first cut with the larger first-cut revenue, breaking ties toward
    the smaller cut. -/
def betterRodCut (price : Nat → Nat) (n : Nat) (a b : Nat) : Nat :=
  if FirstCutValue price (bottomUpRodRevenue price) n a <
     FirstCutValue price (bottomUpRodRevenue price) n b then b else a

/-- The best first cut among a list of candidate cuts, or `none` for an empty
    list. -/
def bestRodCutOf (price : Nat → Nat) (n : Nat) : List Nat → Option Nat
  | [] => none
  | cut :: rest =>
      match bestRodCutOf price n rest with
      | none => some cut
      | some best => some (betterRodCut price n cut best)

/--
The list-based selector returns an element of the candidate list whose first-cut
revenue is at least every candidate's.
-/
theorem bestRodCutOf_correct (price : Nat → Nat) (n : Nat) {best : Nat} {cuts : List Nat}
    (hbest : bestRodCutOf price n cuts = some best) :
    best ∈ cuts ∧
      ∀ cut, cut ∈ cuts →
        FirstCutValue price (bottomUpRodRevenue price) n cut ≤
          FirstCutValue price (bottomUpRodRevenue price) n best := by
  induction cuts generalizing best with
  | nil =>
      simp [bestRodCutOf] at hbest
  | cons cut rest ih =>
      simp [bestRodCutOf] at hbest
      cases hrest : bestRodCutOf price n rest with
      | none =>
          have hrestNil : rest = [] := by
            cases rest with
            | nil => rfl
            | cons restCut restTail =>
                cases htail : bestRodCutOf price n restTail <;>
                  simp [bestRodCutOf, htail] at hrest
          simp [hrest] at hbest
          subst best
          subst rest
          constructor
          · simp
          · intro other hother
            simp at hother
            subst other
            exact le_rfl
      | some restBest =>
          simp [hrest] at hbest
          have hrestCorrect := ih hrest
          by_cases hlt : FirstCutValue price (bottomUpRodRevenue price) n cut <
            FirstCutValue price (bottomUpRodRevenue price) n restBest
          · simp [betterRodCut, hlt] at hbest
            subst best
            constructor
            · simp [hrestCorrect.1]
            · intro other hother
              simp at hother
              rcases hother with hsame | hinRest
              · subst other
                exact le_of_lt hlt
              · exact hrestCorrect.2 other hinRest
          · simp [betterRodCut, hlt] at hbest
            subst best
            constructor
            · simp
            · intro other hother
              simp at hother
              rcases hother with hsame | hinRest
              · subst other
                exact le_rfl
              · exact le_trans (hrestCorrect.2 other hinRest) (le_of_not_gt hlt)

/-- Every nonempty candidate list has a selected best first cut. -/
theorem bestRodCutOf_exists_of_ne_nil (price : Nat → Nat) (n : Nat) {cuts : List Nat}
    (hc : cuts ≠ []) : ∃ best, bestRodCutOf price n cuts = some best := by
  cases cuts with
  | nil =>
      exact False.elim (hc rfl)
  | cons cut rest =>
      simp [bestRodCutOf]
      cases hrest : bestRodCutOf price n rest with
      | none =>
          exact ⟨cut, rfl⟩
      | some restBest =>
          exact ⟨betterRodCut price n cut restBest, rfl⟩

/-- The optimal first cut for a rod of length `n` (junk value `0` when `n = 0`). -/
def rodCutFirstCut (price : Nat → Nat) (n : Nat) : Nat :=
  (bestRodCutOf price n (rodCutCandidates n)).getD 0

/-- The chosen first cut is a valid first cut for a positive-length rod. -/
theorem rodCutFirstCut_mem (price : Nat → Nat) {n : Nat} (hn : 0 < n) :
    rodCutFirstCut price n ∈ rodCutCandidates n := by
  unfold rodCutFirstCut
  have hne : rodCutCandidates n ≠ [] := by
    cases n with
    | zero => omega
    | succ m => simp [rodCutCandidates]
  rcases bestRodCutOf_exists_of_ne_nil price n hne with ⟨best, hbest⟩
  rw [hbest]
  simp
  exact (bestRodCutOf_correct price n hbest).1

/-- The chosen first cut has revenue at least every candidate's. -/
theorem rodCutFirstCut_le (price : Nat → Nat) {n : Nat} (hn : 0 < n) (cut : Nat)
    (hcut : cut ∈ rodCutCandidates n) :
    FirstCutValue price (bottomUpRodRevenue price) n cut ≤
      FirstCutValue price (bottomUpRodRevenue price) n (rodCutFirstCut price n) := by
  unfold rodCutFirstCut
  have hne : rodCutCandidates n ≠ [] := by
    cases n with
    | zero => omega
    | succ m => simp [rodCutCandidates]
  rcases bestRodCutOf_exists_of_ne_nil price n hne with ⟨best, hbest⟩
  rw [hbest]
  simp
  exact (bestRodCutOf_correct price n hbest).2 cut hcut

/-- The chosen first cut achieves the optimal revenue (CLRS §14.1: the `s` entry
    attains the maximum in the recurrence). -/
theorem rodCutFirstCut_value (price : Nat → Nat) {n : Nat} (hn : 0 < n) :
    FirstCutValue price (bottomUpRodRevenue price) n (rodCutFirstCut price n) =
      bottomUpRodRevenue price n := by
  have hs_mem : rodCutFirstCut price n ∈ Finset.Icc 1 n :=
    (mem_rodCutCandidates n _).mp (rodCutFirstCut_mem price hn)
  rcases n with _ | m
  · omega
  · rw [bottomUpRodRevenue_succ price m]
    apply le_antisymm
    · exact Finset.le_sup hs_mem
    · refine Finset.sup_le ?_
      intro cut hcut
      exact rodCutFirstCut_le price hn cut ((mem_rodCutCandidates (m + 1) cut).mpr hcut)

/--
Reconstruct an optimal cutting plan for a rod of length `n` by repeatedly taking
the optimal first cut (CLRS §14.1 `PRINT-CUT-ROD-SOLUTION`).
-/
def rodCutPlan (price : Nat → Nat) : Nat → List Nat
  | 0 => []
  | n@(_ + 1) => rodCutFirstCut price n :: rodCutPlan price (n - rodCutFirstCut price n)
termination_by n => n
decreasing_by
  simp_wf
  have hmem : rodCutFirstCut price n ∈ rodCutCandidates n := rodCutFirstCut_mem price (by omega)
  have hIcc := (mem_rodCutCandidates n (rodCutFirstCut price n)).mp hmem
  have hpos : 1 ≤ rodCutFirstCut price n := (Finset.mem_Icc.mp hIcc).1
  omega

/-- The reconstructed plan for a rod of length `n` has total length `n` and
    attains the optimal revenue. -/
theorem rodCutPlan_correct (price : Nat → Nat) (n : Nat) :
    planLength (rodCutPlan price n) = n ∧
    planValue price (rodCutPlan price n) = bottomUpRodRevenue price n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          rw [rodCutPlan]
          simp [planLength, planValue]
      | succ m =>
          set s : Nat := rodCutFirstCut price (m + 1) with hs_def
          have hs_mem : s ∈ rodCutCandidates (m + 1) := by
            rw [hs_def]
            exact rodCutFirstCut_mem price (by omega)
          have hs_Icc : s ∈ Finset.Icc 1 (m + 1) := (mem_rodCutCandidates (m + 1) s).mp hs_mem
          have hs_pos : 1 ≤ s := (Finset.mem_Icc.mp hs_Icc).1
          have hs_le : s ≤ m + 1 := (Finset.mem_Icc.mp hs_Icc).2
          have hs_sub : m + 1 - s < m + 1 := by omega
          have ih' := ih (m + 1 - s) hs_sub
          have hs_value : FirstCutValue price (bottomUpRodRevenue price) (m + 1) s =
              bottomUpRodRevenue price (m + 1) := by
            rw [hs_def]
            exact rodCutFirstCut_value price (by omega)
          constructor
          · rw [rodCutPlan]
            simp only [planLength, List.sum_cons]
            rw [← hs_def]
            change s + planLength (rodCutPlan price (m + 1 - s)) = m + 1
            rw [ih'.1]
            omega
          · rw [rodCutPlan]
            simp only [planValue, List.map_cons, List.sum_cons]
            rw [← hs_def]
            change price s + planValue price (rodCutPlan price (m + 1 - s)) =
                bottomUpRodRevenue price (m + 1)
            rw [ih'.2]
            simpa [FirstCutValue] using hs_value

/-- The reconstructed plan is optimal among all positive-piece plans of the same
    total length. -/
theorem rodCutPlan_optimal (price : Nat → Nat) (n : Nat) {other : List Nat}
    (hother_pos : PositivePieces other) (hlen : planLength other = n) :
    planValue price other ≤ planValue price (rodCutPlan price n) := by
  have hc := rodCutPlan_correct price n
  apply planValue_le_optimalPlanValue_of_same_length
    (price := price) (revenue := bottomUpRodRevenue price)
    (bottomUpRodRevenue_rodCutRecurrence price) hother_pos
  · rw [hc.1]
    exact hlen
  · rw [hc.2, hc.1]

/-! ## Cost analysis: BOTTOM-UP-CUT-ROD runs in O(n^2) -/

/-- The total number of first-cut candidates examined by BOTTOM-UP-CUT-ROD for a
    rod of length `n`: rod length `j` scans all `j` possible first cuts, so the
    total is `∑_{j = 1}^{n} j = n (n + 1) / 2`. -/
def rodCutStepCount (n : Nat) : Nat :=
  (Finset.range (n + 1)).sum (fun j => j)

/-- Closed form: the bottom-up step count is `n (n + 1) / 2`. -/
theorem rodCutStepCount_eq (n : Nat) : rodCutStepCount n = n * (n + 1) / 2 := by
  unfold rodCutStepCount
  have h : (Finset.range (n + 1)).sum (fun j => j) * 2 = (n + 1) * n := by
    simpa using (Finset.sum_range_id_mul_two (n + 1))
  rw [Nat.mul_comm n (n + 1)]
  rw [← h]
  omega

/-- The bottom-up rod-cutting algorithm performs O(n²) work: its step count is at
    most `n²`. -/
theorem rodCutStepCount_le_quadratic (n : Nat) : rodCutStepCount n ≤ n ^ 2 := by
  rw [rodCutStepCount_eq]
  by_cases hn : n = 0
  · simp [hn]
  · have hpos : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn)
    have hprod : n * (n + 1) ≤ 2 * n ^ 2 := by
      nlinarith
    have hdiv : n * (n + 1) / 2 ≤ (2 * n ^ 2) / 2 := by gcongr
    have htwo : (2 * n ^ 2) / 2 = n ^ 2 := by omega
    rwa [htwo] at hdiv

/-- The candidate first cuts `[1, ..., n]` as a list of subtypes carrying the
    bounds `1 ≤ c` and `c ≤ n`, used to thread the memoized cache through the scan. -/
def rodCutCandidatesBounded (n : Nat) : List {c : Nat // 1 ≤ c ∧ c ≤ n} :=
  (List.range n).attach.map (fun i => ⟨i.1 + 1, Nat.succ_pos i.1, by
    have hi : i.1 < n := List.mem_range.mp i.2
    omega⟩)

/-- A rod of length zero has no first-cut candidates. -/
@[simp] theorem rodCutCandidatesBounded_zero : rodCutCandidatesBounded 0 = [] := by
  simp [rodCutCandidatesBounded]

/-- Projecting the bounded candidates recovers the plain candidate list. -/
theorem rodCutCandidatesBounded_map_val (n : Nat) :
    (rodCutCandidatesBounded n).map (fun cut => cut.1) = rodCutCandidates n := by
  simp [rodCutCandidatesBounded, rodCutCandidates]

/-- A memoized cache is consistent when every stored revenue is the true optimal
    revenue for its rod length. -/
def ConsistentCache (price : Nat → Nat) (cache : Nat → Option Nat) : Prop :=
  ∀ k v, cache k = some v → v = bottomUpRodRevenue price k

/-- A single memoized step, given the sub-computation result. -/
def memoizedRodCutStep (price : Nat → Nat) (cur : Nat) (subval : Nat)
    (cacheSub : Nat → Option Nat) (cut : Nat) : Nat × (Nat → Option Nat) :=
  (max cur (price cut + subval), cacheSub)

/--
Top-down memoized rod cutting (CLRS `MEMOIZED-CUT-ROD`).  `memoizedRodCut price n
cache` returns the optimal revenue for a rod of length `n` together with a cache
extended with the revenue of `n` and every subproblem it needed.  Entries already
present in `cache` are reused without recomputation.
-/
def memoizedRodCut (price : Nat → Nat) : Nat → (Nat → Option Nat) → Nat × (Nat → Option Nat)
  | n, cache =>
      match cache n with
      | some v => (v, cache)
      | none =>
          let res := (rodCutCandidatesBounded n).foldl
            (fun acc cut =>
              let (cur, cacheAcc) := acc
              let (subval, cacheSub) := memoizedRodCut price (n - cut.1) cacheAcc
              memoizedRodCutStep price cur subval cacheSub cut.1)
            (0, cache)
          (res.1, Function.update res.2 n (some res.1))
termination_by n _ => n
decreasing_by
  simp_wf
  omega

/-- The memoized cache-threading fold over the candidate cuts of rod length `n`.
    Exposed so its correctness can be stated and proved by induction. -/
def memoizedRodCutFold (price : Nat → Nat) (n : Nat) (initVal : Nat) (cache : Nat → Option Nat)
    (cuts : List {c : Nat // 1 ≤ c ∧ c ≤ n}) : Nat × (Nat → Option Nat) :=
  cuts.foldl (fun acc cut =>
    let (cur, cacheAcc) := acc
    let (subval, cacheSub) := memoizedRodCut price (n - cut.1) cacheAcc
    memoizedRodCutStep price cur subval cacheSub cut.1) (initVal, cache)

/-! ## List max helpers -/

/-- Folding `max` is monotone in the accumulator. -/
theorem foldl_max_mono_init {l : List Nat} {a b : Nat} (h : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => simpa using h
  | cons c as ih =>
      simp only [List.foldl]
      exact ih (max_le_max_right c h)

/-- Folding `max` with an upper-bound accumulator keeps the result below the
    bound provided every element is below it. -/
theorem foldl_max_le_general {l : List Nat} {b init : Nat} (hb : init ≤ b)
    (h : ∀ x ∈ l, x ≤ b) : l.foldl max init ≤ b := by
  induction l generalizing init with
  | nil => simpa using hb
  | cons a as ih =>
      simp only [List.foldl]
      exact ih (max_le hb (h a (by simp))) (by
        intro x hx
        exact h x (by simp [hx]))

/-- Folding `max` from zero is bounded by any upper bound of the elements. -/
theorem foldl_max_le {l : List Nat} {b : Nat} (h : ∀ x ∈ l, x ≤ b) :
    l.foldl max 0 ≤ b :=
  foldl_max_le_general (b := b) (init := 0) (by omega) h

/-- Folding `max` from `x` stays above `x`. -/
theorem foldl_max_ge_init (l : List Nat) (x : Nat) : x ≤ l.foldl max x := by
  induction l with
  | nil => simp
  | cons a as ih =>
      simp only [List.foldl]
      exact le_trans ih (foldl_max_mono_init (l := as) (le_max_left x a))

/-- Any element of a list is below the fold-`max` value. -/
theorem foldl_max_mem {l : List Nat} {x : Nat} (hx : x ∈ l) : x ≤ l.foldl max 0 := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
      simp only [List.foldl] at hx ⊢
      rcases List.mem_cons.mp hx with hxa | has
      · subst x
        have h0a : max 0 a = a := by simp
        rw [h0a]
        exact foldl_max_ge_init as a
      · exact le_trans (ih has) (foldl_max_mono_init (l := as) (le_max_left 0 a))

/-- The maximum over the first-cut candidates for rod length `n` is the optimal
    revenue (this is exactly the CLRS first-cut recurrence). -/
theorem candidatesMax_eq_rev (price : Nat → Nat) (n : Nat) :
    ((rodCutCandidatesBounded n).map
        (fun cut => FirstCutValue price (bottomUpRodRevenue price) n cut.1)).foldl max 0
      = bottomUpRodRevenue price n := by
  apply le_antisymm
  · refine foldl_max_le ?_
    intro v hv
    rcases List.mem_map.mp hv with ⟨cut, hcut, rfl⟩
    exact firstCutValue_le_of_rodCutRecurrence
      (bottomUpRodRevenue_rodCutRecurrence price) (Finset.mem_Icc.mpr cut.2)
  · by_cases hn : n = 0
    · simp [hn, bottomUpRodRevenue_zero]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hs_value : FirstCutValue price (bottomUpRodRevenue price) n (rodCutFirstCut price n) =
          bottomUpRodRevenue price n := rodCutFirstCut_value price hpos
      rw [← hs_value]
      apply foldl_max_mem
      have hproj : (rodCutCandidatesBounded n).map (fun cut => cut.1) = rodCutCandidates n :=
        rodCutCandidatesBounded_map_val n
      have hrc : rodCutFirstCut price n ∈ (rodCutCandidatesBounded n).map (fun cut => cut.1) := by
        rw [hproj]
        exact rodCutFirstCut_mem price hpos
      rcases List.mem_map.mp hrc with ⟨cut, hcut, hval⟩
      apply List.mem_map.mpr
      exact ⟨cut, hcut, by rw [← hval]⟩

/-! ## Memoization correctness -/

/-- The memoized fold accumulates the best first-cut value and threads a
    consistent cache. -/
theorem memoizedRodCut_fold_correct (price : Nat → Nat) (n : Nat)
    (cuts : List {c : Nat // 1 ≤ c ∧ c ≤ n})
    (initVal : Nat) (cache : Nat → Option Nat) (hcons : ConsistentCache price cache)
    (hrec : ∀ cut ∈ cuts, ∀ c', ConsistentCache price c' →
        (memoizedRodCut price (n - cut.1) c').1 = bottomUpRodRevenue price (n - cut.1) ∧
        ConsistentCache price (memoizedRodCut price (n - cut.1) c').2) :
    (memoizedRodCutFold price n initVal cache cuts).1 =
      (cuts.map (fun cut => price cut.1 + bottomUpRodRevenue price (n - cut.1))).foldl max initVal ∧
    ConsistentCache price (memoizedRodCutFold price n initVal cache cuts).2 := by
  unfold memoizedRodCutFold
  induction cuts generalizing initVal cache with
  | nil =>
      constructor
      · simp
      · simpa using hcons
  | cons head rest ih =>
      have hval_head : (memoizedRodCut price (n - head.1) cache).1 = bottomUpRodRevenue price (n - head.1) :=
        (hrec head (by simp) cache hcons).1
      have hcons_head : ConsistentCache price (memoizedRodCut price (n - head.1) cache).2 :=
        (hrec head (by simp) cache hcons).2
      let s : Nat × (Nat → Option Nat) := memoizedRodCutStep price initVal
        (memoizedRodCut price (n - head.1) cache).1 (memoizedRodCut price (n - head.1) cache).2 head.1
      have hcons_s : ConsistentCache price s.2 := by simpa [s, memoizedRodCutStep] using hcons_head
      have ih' := ih s.1 s.2 hcons_s (fun cut' hcut' c'' hc'' => hrec cut'
        (List.mem_cons.mpr (Or.inr hcut')) c'' hc'')
      simp only [List.foldl]
      constructor
      · rw [ih'.1]
        have hs1 : s.1 = max initVal (price head.1 + bottomUpRodRevenue price (n - head.1)) := by
          simp [s, memoizedRodCutStep, hval_head]
        rw [hs1]
        simp only [List.map, List.foldl]
      · exact ih'.2

/-- When the cache misses length `n`, the uncached computation reduces to the
    cache-threading fold: its revenue component is the fold's first component. -/
theorem memoizedRodCut_none_fst {price : Nat → Nat} {n : Nat} {cache : Nat → Option Nat}
    (hc : cache n = none) :
    (memoizedRodCut price n cache).1 = (memoizedRodCutFold price n 0 cache (rodCutCandidatesBounded n)).1 := by
  rw [memoizedRodCut, hc]
  rfl

/-- When the cache misses length `n`, the uncached computation reduces to the
    cache-threading fold: its cache is the fold's cache with the entry at `n`
    stored. -/
theorem memoizedRodCut_none_snd {price : Nat → Nat} {n : Nat} {cache : Nat → Option Nat}
    (hc : cache n = none) :
    (memoizedRodCut price n cache).2 =
      Function.update (memoizedRodCutFold price n 0 cache (rodCutCandidatesBounded n)).2
        n (some (memoizedRodCutFold price n 0 cache (rodCutCandidatesBounded n)).1) := by
  rw [memoizedRodCut, hc]
  rfl

/-- Memoized top-down rod cutting is correct: it returns the optimal revenue and
    its output cache remains consistent. -/
theorem memoizedRodCut_correct (price : Nat → Nat) (n : Nat) (cache : Nat → Option Nat)
    (hcons : ConsistentCache price cache) :
    (memoizedRodCut price n cache).1 = bottomUpRodRevenue price n ∧
    ConsistentCache price (memoizedRodCut price n cache).2 := by
  revert hcons cache
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro cache hcons
      by_cases hc : cache n = none
      · rcases n with _ | m
        · -- n = 0, uncached
          constructor
          · rw [memoizedRodCut_none_fst hc]
            simp [memoizedRodCutFold]
          · rw [memoizedRodCut_none_snd hc]
            intro k v hkv
            by_cases hk : k = 0
            · subst k
              have hkv0 : 0 = v := by simpa [Function.update, memoizedRodCutFold] using hkv
              rw [← hkv0]
              simp
            · simp [Function.update, hk] at hkv
              exact hcons k v hkv
        · -- n = m + 1, uncached
          have hrec : ∀ cut ∈ rodCutCandidatesBounded (m + 1), ∀ c', ConsistentCache price c' →
              (memoizedRodCut price (m + 1 - cut.1) c').1 = bottomUpRodRevenue price (m + 1 - cut.1) ∧
              ConsistentCache price (memoizedRodCut price (m + 1 - cut.1) c').2 := by
            intro cut hcut c' hc'
            have hlt : m + 1 - cut.1 < m + 1 := by
              have h1 : 1 ≤ cut.1 := cut.2.1
              omega
            exact ih (m + 1 - cut.1) hlt c' hc'
          have hfold := memoizedRodCut_fold_correct price (m + 1) (rodCutCandidatesBounded (m + 1))
            0 cache hcons hrec
          constructor
          · rw [memoizedRodCut_none_fst hc, hfold.1]
            exact candidatesMax_eq_rev price (m + 1)
          · rw [memoizedRodCut_none_snd hc]
            intro k v hkv
            by_cases hk : k = m + 1
            · subst k
              simp [Function.update] at hkv
              rw [← hkv]
              rw [hfold.1]
              exact candidatesMax_eq_rev price (m + 1)
            · simp [Function.update, hk] at hkv
              exact hfold.2 k v hkv
      · -- cached
        cases hcv : cache n with
        | none => exact False.elim (hc hcv)
        | some v =>
            have hv' : v = bottomUpRodRevenue price n := hcons n v hcv
            constructor
            · rw [memoizedRodCut, hcv]
              simp
              exact hv'
            · rw [memoizedRodCut, hcv]
              simp
              exact hcons

/-- Memoized top-down rod cutting returns the optimal revenue. -/
theorem memoizedRodCut_value (price : Nat → Nat) (n : Nat) (cache : Nat → Option Nat)
    (hcons : ConsistentCache price cache) :
    (memoizedRodCut price n cache).1 = bottomUpRodRevenue price n :=
  (memoizedRodCut_correct price n cache hcons).1

end Chapter15
end CLRS
