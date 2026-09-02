import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Optimality.Trace.A3_CouplingCore

/-!
# Section 15.4 optimality: coupling correctness

This file proves that the recursive coupling is legal, preserves the exact
cache relation, and never spends more misses than the local credit permits.
-/

namespace CLRS

open Finset
open scoped BigOperators

namespace Caching

/-- Cache relation represented by each coupling phase. -/
def ModeRel : CouplingMode → Finset Page → Finset Page → Prop
  | .same, A, B => A = B
  | .ordered a b, A, B => OnePageDiff A B a b
  | .credited a b, A, B => OnePageDiff A B a b

/-- The miss indicator of one request against one cache. -/
def faultInCache (C : Finset Page) (request : Page) : ℕ :=
  if request ∈ C then 0 else 1

/-- A cache-only miss indicator used while the transformed trace is unpackaged. -/
def cacheFaultAt (cache : ℕ → Finset Page) (σ : List Page) (t : ℕ) : ℕ :=
  faultInCache (cache t) (σ.getD t 0)

/-- Misses of a cache sequence on a finite interval starting at `start`. -/
def cacheMissesFrom (cache : ℕ → Finset Page) (σ : List Page)
    (start count : ℕ) : ℕ :=
  ∑ n ∈ Finset.range count, cacheFaultAt cache σ (start + n)

/-- Ordered mode has no credit; credited mode has one saved source miss. -/
def AccountingRel : CouplingMode → ℕ → ℕ → Prop
  | .same, transformed, source => transformed ≤ source
  | .ordered _ _, transformed, source => transformed ≤ source
  | .credited _ _, transformed, source => transformed + 1 ≤ source

/-- Ordered mode is safe only while the source-only page is not requested. -/
def OrderedSafe : CouplingMode → Page → Prop
  | .ordered _ b, request => request ≠ b
  | _, _ => True

lemma faultInCache_le_one (C : Finset Page) (request : Page) :
    faultInCache C request ≤ 1 := by
  unfold faultInCache
  split <;> omega

lemma OnePageDiff.fault_eq_of_ne (h : OnePageDiff A B a b)
    (request : Page) (hrequesta : request ≠ a) (hrequestb : request ≠ b) :
    faultInCache A request = faultInCache B request := by
  have hmem := h.mem_iff hrequesta hrequestb
  unfold faultInCache
  by_cases hrequestA : request ∈ A
  · have hrequestB := hmem.mp hrequestA
    simp [hrequestA, hrequestB]
  · have hrequestB : request ∉ B := by
      intro hmemB
      exact hrequestA (hmem.mpr hmemB)
    simp [hrequestA, hrequestB]

lemma OnePageDiff.fault_le_of_ne_right (h : OnePageDiff A B a b)
    (request : Page) (hrequestb : request ≠ b) :
    faultInCache A request ≤ faultInCache B request := by
  by_cases hrequesta : request = a
  · subst request
    simp [faultInCache, h.left_mem, h.left_not_mem_right]
  · rw [h.fault_eq_of_ne request hrequesta hrequestb]

lemma faultInCache_le_add_one (A B : Finset Page) (request : Page) :
    faultInCache A request ≤ faultInCache B request + 1 := by
  have hA := faultInCache_le_one A request
  omega

/-- The common eviction rule used by both one-page-difference modes. -/
private def diffCoupledEvict (A B : Finset Page) (a b sourceEvict request : Page) : Page :=
  if request ∈ B ∧ request ∉ A then a
  else if sourceEvict = b then a else sourceEvict

/-- A transformed fault always removes a transformed resident. -/
lemma coupledEvict_mem (mode : CouplingMode) (A B : Finset Page)
    (sourceEvict request : Page) (hrel : ModeRel mode A B)
    (hsource : request ∉ B → sourceEvict ∈ B)
    (htransformed : request ∉ A) :
    coupledEvict mode A B sourceEvict request ∈ A := by
  cases mode with
  | same =>
      simp only [ModeRel] at hrel
      subst B
      simpa [coupledEvict] using hsource htransformed
  | ordered a b =>
      simp only [ModeRel] at hrel
      by_cases hunique : request ∈ B ∧ request ∉ A
      · simp [coupledEvict, hunique, hrel.left_mem]
      · have hrequestB : request ∉ B := by
          intro hmem
          exact hunique ⟨hmem, htransformed⟩
        have hsourceB : sourceEvict ∈ B := hsource hrequestB
        by_cases hsb : sourceEvict = b
        · simp [coupledEvict, hunique, hsb, hrel.left_mem]
        · have hsa : sourceEvict ≠ a := by
            intro hsa
            subst sourceEvict
            exact hrel.left_not_mem_right hsourceB
          have hsourceA : sourceEvict ∈ A := (hrel.mem_iff hsa hsb).2 hsourceB
          simpa [coupledEvict, hunique, hsb] using hsourceA
  | credited a b =>
      simp only [ModeRel] at hrel
      by_cases hunique : request ∈ B ∧ request ∉ A
      · simp [coupledEvict, hunique, hrel.left_mem]
      · have hrequestB : request ∉ B := by
          intro hmem
          exact hunique ⟨hmem, htransformed⟩
        have hsourceB : sourceEvict ∈ B := hsource hrequestB
        by_cases hsb : sourceEvict = b
        · simp [coupledEvict, hunique, hsb, hrel.left_mem]
        · have hsa : sourceEvict ≠ a := by
            intro hsa
            subst sourceEvict
            exact hrel.left_not_mem_right hsourceB
          have hsourceA : sourceEvict ∈ A := (hrel.mem_iff hsa hsb).2 hsourceB
          simpa [coupledEvict, hunique, hsb] using hsourceA

/-- Complete transition classification for exact one-page-different caches. -/
lemma onePageDiff_step_cases (h : OnePageDiff A B a b)
    (sourceEvict request : Page)
    (hsource : request ∉ B → sourceEvict ∈ B) :
    let evict := diffCoupledEvict A B a b sourceEvict request
    let transformedNext := traceStepCache A evict request
    let sourceNext := traceStepCache B sourceEvict request
    transformedNext = sourceNext ∨
      (request = a ∧ sourceEvict ≠ b ∧
        OnePageDiff transformedNext sourceNext sourceEvict b) ∨
      (request ≠ a ∧ OnePageDiff transformedNext sourceNext a b) := by
  dsimp only
  by_cases hrequestA : request ∈ A
  · by_cases hrequestB : request ∈ B
    · have hrequesta : request ≠ a := by
        intro hrequesta
        subst request
        exact h.left_not_mem_right hrequestB
      right
      right
      refine ⟨hrequesta, ?_⟩
      simpa [traceStepCache, hrequestA, hrequestB]
    · have hrequestb : request ≠ b := by
        intro hrequestb
        subst request
        exact h.right_not_mem_left hrequestA
      have hrequesta : request = a := by
        by_contra hne
        exact hrequestB ((h.mem_iff hne hrequestb).1 hrequestA)
      subst request
      have hsourceB : sourceEvict ∈ B := hsource h.left_not_mem_right
      by_cases hsourceb : sourceEvict = b
      · subst sourceEvict
        left
        simpa [traceStepCache, h.left_mem, h.left_not_mem_right] using
          h.insert_left_erase_right.symm
      · right
        left
        refine ⟨rfl, hsourceb, ?_⟩
        simpa [traceStepCache, h.left_mem, h.left_not_mem_right] using
          h.hit_left_fault sourceEvict hsourceB hsourceb
  · by_cases hrequestB : request ∈ B
    · have hrequesta : request ≠ a := by
        intro hrequesta
        subst request
        exact hrequestA h.left_mem
      have hrequestb : request = b := by
        by_contra hne
        exact hrequestA ((h.mem_iff hrequesta hne).2 hrequestB)
      subst request
      left
      simpa [diffCoupledEvict, traceStepCache, h.right_not_mem_left,
        h.right_mem] using h.insert_right_erase_left
    · have hsourceB : sourceEvict ∈ B := hsource hrequestB
      by_cases hsourceb : sourceEvict = b
      · subst sourceEvict
        left
        simpa [diffCoupledEvict, traceStepCache, hrequestA, hrequestB] using
          h.merge request
      · have hsourcea : sourceEvict ≠ a := by
          intro hsourcea
          subst sourceEvict
          exact h.left_not_mem_right hsourceB
        have hrequesta : request ≠ a := by
          intro hrequesta
          subst request
          exact hrequestA h.left_mem
        right
        right
        refine ⟨hrequesta, ?_⟩
        simpa [diffCoupledEvict, traceStepCache, hrequestA, hrequestB,
          hsourceb] using
          h.fault_common sourceEvict request hsourcea hsourceb hrequestA hrequestB

/-- One coupling step preserves the relation represented by the next mode. -/
lemma modeRel_step (mode : CouplingMode) (A B : Finset Page)
    (sourceEvict request : Page) (hrel : ModeRel mode A B)
    (hsource : request ∉ B → sourceEvict ∈ B) :
    let transformedNext :=
      traceStepCache A (coupledEvict mode A B sourceEvict request) request
    let sourceNext := traceStepCache B sourceEvict request
    ModeRel (nextCouplingMode mode request sourceEvict transformedNext sourceNext)
      transformedNext sourceNext := by
  dsimp only
  cases mode with
  | same =>
      simp only [ModeRel] at hrel
      subst B
      simp [coupledEvict, nextCouplingMode, ModeRel]
  | ordered a b =>
      simp only [ModeRel] at hrel
      have hcases := onePageDiff_step_cases hrel sourceEvict request hsource
      simp only [diffCoupledEvict] at hcases
      rcases hcases with hequal | hchanged | hstable
      · have hequal' :
            traceStepCache A (coupledEvict (.ordered a b) A B sourceEvict request) request =
              traceStepCache B sourceEvict request := by
          simpa [coupledEvict] using hequal
        simp [nextCouplingMode, hequal', ModeRel]
      · rcases hchanged with ⟨hrequest, hsourceb, hdiff⟩
        subst request
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.ordered a b) A B sourceEvict a) a)
            (traceStepCache B sourceEvict a) sourceEvict b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        simpa [nextCouplingMode, hne, ModeRel] using hdiff'
      · rcases hstable with ⟨hrequest, hdiff⟩
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.ordered a b) A B sourceEvict request) request)
            (traceStepCache B sourceEvict request) a b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        simpa [nextCouplingMode, hne, hrequest, ModeRel] using hdiff'
  | credited a b =>
      simp only [ModeRel] at hrel
      have hcases := onePageDiff_step_cases hrel sourceEvict request hsource
      simp only [diffCoupledEvict] at hcases
      rcases hcases with hequal | hchanged | hstable
      · have hequal' :
            traceStepCache A (coupledEvict (.credited a b) A B sourceEvict request) request =
              traceStepCache B sourceEvict request := by
          simpa [coupledEvict] using hequal
        simp [nextCouplingMode, hequal', ModeRel]
      · rcases hchanged with ⟨hrequest, hsourceb, hdiff⟩
        subst request
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.credited a b) A B sourceEvict a) a)
            (traceStepCache B sourceEvict a) sourceEvict b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        simpa [nextCouplingMode, hne, ModeRel] using hdiff'
      · rcases hstable with ⟨hrequest, hdiff⟩
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.credited a b) A B sourceEvict request) request)
            (traceStepCache B sourceEvict request) a b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        simpa [nextCouplingMode, hne, hrequest, ModeRel] using hdiff'

/-- One request preserves the local miss-accounting invariant. -/
lemma accounting_step (mode : CouplingMode) (A B : Finset Page)
    (sourceEvict request : Page) (transformedMisses sourceMisses : ℕ)
    (hrel : ModeRel mode A B)
    (hsource : request ∉ B → sourceEvict ∈ B)
    (hsafe : OrderedSafe mode request)
    (haccount : AccountingRel mode transformedMisses sourceMisses) :
    let transformedNext :=
      traceStepCache A (coupledEvict mode A B sourceEvict request) request
    let sourceNext := traceStepCache B sourceEvict request
    AccountingRel
      (nextCouplingMode mode request sourceEvict transformedNext sourceNext)
      (transformedMisses + faultInCache A request)
      (sourceMisses + faultInCache B request) := by
  dsimp only
  cases mode with
  | same =>
      simp only [ModeRel] at hrel
      simp only [AccountingRel] at haccount
      subst B
      simp [coupledEvict, nextCouplingMode, AccountingRel]
      omega
  | ordered a b =>
      simp only [ModeRel] at hrel
      simp only [OrderedSafe] at hsafe
      simp only [AccountingRel] at haccount
      have hcases := onePageDiff_step_cases hrel sourceEvict request hsource
      simp only [diffCoupledEvict] at hcases
      rcases hcases with hequal | hchanged | hstable
      · have hequal' :
            traceStepCache A (coupledEvict (.ordered a b) A B sourceEvict request) request =
              traceStepCache B sourceEvict request := by
          simpa [coupledEvict] using hequal
        have hfault := hrel.fault_le_of_ne_right request hsafe
        simp [nextCouplingMode, hequal', AccountingRel]
        omega
      · rcases hchanged with ⟨hrequest, hsourceb, hdiff⟩
        subst request
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.ordered a b) A B sourceEvict a) a)
            (traceStepCache B sourceEvict a) sourceEvict b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        simp [nextCouplingMode, hne, AccountingRel, faultInCache,
          hrel.left_mem, hrel.left_not_mem_right]
        omega
      · rcases hstable with ⟨hrequesta, hdiff⟩
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.ordered a b) A B sourceEvict request) request)
            (traceStepCache B sourceEvict request) a b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        have hfault := hrel.fault_eq_of_ne request hrequesta hsafe
        simp [nextCouplingMode, hne, hrequesta, AccountingRel]
        omega
  | credited a b =>
      simp only [ModeRel] at hrel
      simp only [AccountingRel] at haccount
      have hcases := onePageDiff_step_cases hrel sourceEvict request hsource
      simp only [diffCoupledEvict] at hcases
      rcases hcases with hequal | hchanged | hstable
      · have hequal' :
            traceStepCache A (coupledEvict (.credited a b) A B sourceEvict request) request =
              traceStepCache B sourceEvict request := by
          simpa [coupledEvict] using hequal
        have hfault := faultInCache_le_add_one A B request
        simp [nextCouplingMode, hequal', AccountingRel]
        omega
      · rcases hchanged with ⟨hrequest, hsourceb, hdiff⟩
        subst request
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.credited a b) A B sourceEvict a) a)
            (traceStepCache B sourceEvict a) sourceEvict b := by
          simpa [coupledEvict] using hdiff
        have hne := hdiff'.cache_ne
        simp [nextCouplingMode, hne, AccountingRel, faultInCache,
          hrel.left_mem, hrel.left_not_mem_right]
        omega
      · rcases hstable with ⟨hrequesta, hdiff⟩
        have hdiff' : OnePageDiff
            (traceStepCache A (coupledEvict (.credited a b) A B sourceEvict request) request)
            (traceStepCache B sourceEvict request) a b := by
          simpa [coupledEvict] using hdiff
        have hrequestb : request ≠ b := by
          intro hrequestb
          subst request
          have hequal' :
              traceStepCache A (coupledEvict (.credited a b) A B sourceEvict b) b =
                traceStepCache B sourceEvict b := by
            simpa [coupledEvict, traceStepCache, hrel.right_not_mem_left,
              hrel.right_mem] using hrel.insert_right_erase_left
          exact hdiff'.cache_ne hequal'
        have hne := hdiff'.cache_ne
        have hfault := hrel.fault_eq_of_ne request hrequesta hrequestb
        simp [nextCouplingMode, hne, hrequesta, AccountingRel]
        omega
/-- For distinct pages, non-strict `Farther` yields a strict first-use order. -/
lemma farther_distinct_order {σ : List Page} {start : ℕ} {a b : Page}
    (hab : a ≠ b)
    (hfarther : Farther (nextUse σ start b) (nextUse σ start a)) :
    nextUse σ start b = none ∨
      ∃ ja jb, nextUse σ start a = some ja ∧
        nextUse σ start b = some jb ∧ ja < jb := by
  rcases farther_cases hfarther with hnone | ⟨jb, ja, hb, ha, hle⟩
  · exact Or.inl hnone
  · right
    refine ⟨ja, jb, ha, hb, ?_⟩
    have hne : ja ≠ jb := by
      intro heq
      subst jb
      have hgeta := getD_eq_nextUse ha
      have hgetb := getD_eq_nextUse hb
      exact hab (hgeta.symm.trans hgetb)
    omega

/-- No request of the farther page occurs up to the first nearer-page request. -/
lemma getD_ne_farther_until {σ : List Page} {start n : ℕ} {a b : Page}
    (hab : a ≠ b)
    (hfarther : Farther (nextUse σ start b) (nextUse σ start a))
    (hlen : start + n < σ.length)
    (hdeadline : ∀ j, nextUse σ start a = some j → n ≤ j) :
    σ.getD (start + n) 0 ≠ b := by
  rcases farther_distinct_order hab hfarther with hnone | ⟨ja, jb, ha, hb, hjlt⟩
  · have hnone' := nextUse_eq_none_iff.mp hnone
    apply hnone' (σ.getD (start + n) 0)
    have hnDrop : n < (σ.drop start).length := by
      rw [List.length_drop]
      omega
    have hget : (σ.drop start).getD n 0 = σ.getD (start + n) 0 := by
      rw [getD_drop]
    rw [← hget]
    rw [List.getD_eq_getElem _ 0 hnDrop]
    exact List.getElem_mem hnDrop
  · exact getD_ne_nextUse hb (by omega) (by
      have hnle := hdeadline ja ha
      omega)

/-- An ordered next mode can only come from the same ordered pair before `a`. -/
lemma nextCouplingMode_eq_ordered {mode : CouplingMode} {request sourceEvict a b : Page}
    {transformedNext sourceNext : Finset Page}
    (hnext : nextCouplingMode mode request sourceEvict transformedNext sourceNext =
      .ordered a b) :
    mode = .ordered a b ∧ request ≠ a := by
  by_cases hequal : transformedNext = sourceNext
  · simp [nextCouplingMode, hequal] at hnext
  · cases mode with
    | same => simp [nextCouplingMode, hequal] at hnext
    | ordered x y =>
        by_cases hrequest : request = x
        · simp [nextCouplingMode, hequal, hrequest] at hnext
        · simp [nextCouplingMode, hequal, hrequest] at hnext
          rcases hnext with ⟨rfl, rfl⟩
          exact ⟨rfl, hrequest⟩
    | credited x y =>
        by_cases hrequest : request = x <;>
          simp [nextCouplingMode, hequal, hrequest] at hnext

/-- Source misses over a suffix, expressed with the legal trace cache. -/
def traceMissesFrom (T : LegalTrace C₀ σ) (start count : ℕ) : ℕ :=
  cacheMissesFrom T.cache σ start count

/-- Misses of the unpackaged recursive transformed suffix. -/
def couplingMisses (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (count : ℕ) : ℕ :=
  ∑ n ∈ Finset.range count,
    faultInCache (couplingCore source start A mode n).cache (σ.getD (start + n) 0)

@[simp] lemma couplingCore_cache_succ (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (n : ℕ) :
    (couplingCore source start A mode (n + 1)).cache =
      traceStepCache (couplingCore source start A mode n).cache
        (couplingCore source start A mode n).evict (σ.getD (start + n) 0) := by
  rfl

@[simp] lemma couplingCore_mode_succ (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (n : ℕ) :
    (couplingCore source start A mode (n + 1)).mode =
      nextCouplingMode (couplingCore source start A mode n).mode
        (σ.getD (start + n) 0) (source.evict (start + n))
        (couplingCore source start A mode (n + 1)).cache
        (source.cache (start + n + 1)) := by
  rfl

lemma couplingCore_evict_eq (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (n : ℕ) :
    (couplingCore source start A mode n).evict =
      coupledEvict (couplingCore source start A mode n).mode
        (couplingCore source start A mode n).cache (source.cache (start + n))
        (source.evict (start + n)) (σ.getD (start + n) 0) := by
  cases n <;> rfl

/-- The recursive core preserves the cache relation at every in-range boundary. -/
lemma couplingCore_modeRel (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (a b : Page) (hdiff : OnePageDiff A (source.cache start) a b)
    (n : ℕ) (hbound : start + n ≤ σ.length) :
    ModeRel (couplingCore source start A (.ordered a b) n).mode
      (couplingCore source start A (.ordered a b) n).cache
      (source.cache (start + n)) := by
  induction n with
  | zero => simpa [couplingCore, ModeRel] using hdiff
  | succ n ih =>
      have hlt : start + n < σ.length := by omega
      have hprev : start + n ≤ σ.length := by omega
      have hrel := ih hprev
      have hsource : σ.getD (start + n) 0 ∉ source.cache (start + n) →
          source.evict (start + n) ∈ source.cache (start + n) :=
        source.evict_mem (start + n) hlt
      have hstep := modeRel_step
        (couplingCore source start A (.ordered a b) n).mode
        (couplingCore source start A (.ordered a b) n).cache
        (source.cache (start + n)) (source.evict (start + n))
        (σ.getD (start + n) 0) hrel hsource
      have hsourceStep : source.cache (start + n + 1) =
          traceStepCache (source.cache (start + n)) (source.evict (start + n))
            (σ.getD (start + n) 0) := by
        simpa [traceStepCache] using source.step (start + n) hlt
      have hsourceStep' : source.cache (start + (n + 1)) =
          traceStepCache (source.cache (start + n)) (source.evict (start + n))
            (σ.getD (start + n) 0) := by
        simpa [Nat.add_assoc] using hsourceStep
      rw [couplingCore_mode_succ, couplingCore_cache_succ]
      rw [hsourceStep, hsourceStep']
      rw [couplingCore_evict_eq]
      exact hstep

/-- Every transformed core fault evicts a transformed resident. -/
lemma couplingCore_evict_mem (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (a b : Page) (hdiff : OnePageDiff A (source.cache start) a b)
    (n : ℕ) (hbound : start + n < σ.length)
    (hmiss : σ.getD (start + n) 0 ∉
      (couplingCore source start A (.ordered a b) n).cache) :
    (couplingCore source start A (.ordered a b) n).evict ∈
      (couplingCore source start A (.ordered a b) n).cache := by
  rw [couplingCore_evict_eq]
  apply coupledEvict_mem
  · exact couplingCore_modeRel source start A a b hdiff n (by omega)
  · exact source.evict_mem (start + n) hbound
  · exact hmiss

/-- Ordered mode can only persist for the original pair and through `a`'s deadline. -/
lemma couplingCore_ordered_deadline (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (a b : Page) (n : ℕ) :
    ∀ x y, (couplingCore source start A (.ordered a b) n).mode = .ordered x y →
      x = a ∧ y = b ∧
        ∀ j, nextUse σ start a = some j → n ≤ j := by
  induction n with
  | zero =>
      intro x y hmode
      simp [couplingCore] at hmode
      rcases hmode with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl, by intro j hj; omega⟩
  | succ n ih =>
      intro x y hmode
      have hnext :
          nextCouplingMode (couplingCore source start A (.ordered a b) n).mode
            (σ.getD (start + n) 0) (source.evict (start + n))
            (couplingCore source start A (.ordered a b) (n + 1)).cache
            (source.cache (start + n + 1)) = .ordered x y := by
        simpa using hmode
      rcases nextCouplingMode_eq_ordered hnext with ⟨hprev, hrequest⟩
      rcases ih x y hprev with ⟨hx, hy, hdeadline⟩
      refine ⟨hx, hy, ?_⟩
      intro j hj
      have hnle := hdeadline j hj
      by_contra hnot
      have hnj : n = j := by omega
      subst j
      have hgeta := getD_eq_nextUse hj
      exact hrequest (hgeta.trans hx.symm)

/-- At every in-range ordered step, the source-only page is not requested. -/
lemma couplingCore_ordered_safe (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (a b : Page) (hdiff : OnePageDiff A (source.cache start) a b)
    (hfarther : Farther (nextUse σ start b) (nextUse σ start a))
    (n : ℕ) (hbound : start + n < σ.length) :
    OrderedSafe (couplingCore source start A (.ordered a b) n).mode
      (σ.getD (start + n) 0) := by
  cases hmode : (couplingCore source start A (.ordered a b) n).mode with
  | same => simp [OrderedSafe]
  | credited x y => simp [OrderedSafe]
  | ordered x y =>
      rcases couplingCore_ordered_deadline source start A a b n x y hmode with
        ⟨hx, hy, hdeadline⟩
      subst x
      subst y
      simpa [OrderedSafe, hmode] using
        getD_ne_farther_until hdiff.ne hfarther hbound hdeadline

@[simp] lemma couplingMisses_zero (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) :
    couplingMisses source start A mode 0 = 0 := by
  simp [couplingMisses]

lemma couplingMisses_succ (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (n : ℕ) :
    couplingMisses source start A mode (n + 1) =
      couplingMisses source start A mode n +
        faultInCache (couplingCore source start A mode n).cache
          (σ.getD (start + n) 0) := by
  simp [couplingMisses, Finset.sum_range_succ]

@[simp] lemma traceMissesFrom_zero (T : LegalTrace C₀ σ) (start : ℕ) :
    traceMissesFrom T start 0 = 0 := by
  simp [traceMissesFrom, cacheMissesFrom]

lemma traceMissesFrom_succ (T : LegalTrace C₀ σ) (start n : ℕ) :
    traceMissesFrom T start (n + 1) =
      traceMissesFrom T start n +
        faultInCache (T.cache (start + n)) (σ.getD (start + n) 0) := by
  simp [traceMissesFrom, cacheMissesFrom, cacheFaultAt, Finset.sum_range_succ]

/-- The recursive suffix maintains the local miss-accounting invariant. -/
lemma couplingCore_accounting (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (a b : Page) (hdiff : OnePageDiff A (source.cache start) a b)
    (hfarther : Farther (nextUse σ start b) (nextUse σ start a))
    (n : ℕ) (hbound : start + n ≤ σ.length) :
    AccountingRel (couplingCore source start A (.ordered a b) n).mode
      (couplingMisses source start A (.ordered a b) n)
      (traceMissesFrom source start n) := by
  induction n with
  | zero => simp [couplingCore, AccountingRel]
  | succ n ih =>
      have hlt : start + n < σ.length := by omega
      have hprev : start + n ≤ σ.length := by omega
      have haccount := ih hprev
      have hrel := couplingCore_modeRel source start A a b hdiff n hprev
      have hsource : σ.getD (start + n) 0 ∉ source.cache (start + n) →
          source.evict (start + n) ∈ source.cache (start + n) :=
        source.evict_mem (start + n) hlt
      have hsafe := couplingCore_ordered_safe source start A a b hdiff hfarther n hlt
      have hstep := accounting_step
        (couplingCore source start A (.ordered a b) n).mode
        (couplingCore source start A (.ordered a b) n).cache
        (source.cache (start + n)) (source.evict (start + n))
        (σ.getD (start + n) 0)
        (couplingMisses source start A (.ordered a b) n)
        (traceMissesFrom source start n) hrel hsource hsafe haccount
      have hsourceStep : source.cache (start + n + 1) =
          traceStepCache (source.cache (start + n)) (source.evict (start + n))
            (σ.getD (start + n) 0) := by
        simpa [traceStepCache] using source.step (start + n) hlt
      rw [couplingMisses_succ, traceMissesFrom_succ]
      rw [couplingCore_mode_succ, couplingCore_cache_succ]
      rw [hsourceStep, couplingCore_evict_eq]
      exact hstep

lemma AccountingRel.le {mode : CouplingMode} {transformed source : ℕ}
    (h : AccountingRel mode transformed source) : transformed ≤ source := by
  cases mode <;> simp only [AccountingRel] at h <;> omega

/-- The recursive transformed suffix has no more misses than the source suffix. -/
lemma couplingMisses_le (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (a b : Page) (hdiff : OnePageDiff A (source.cache start) a b)
    (hfarther : Farther (nextUse σ start b) (nextUse σ start a))
    (count : ℕ) (hbound : start + count ≤ σ.length) :
    couplingMisses source start A (.ordered a b) count ≤
      traceMissesFrom source start count :=
  (couplingCore_accounting source start A a b hdiff hfarther count hbound).le

/-! Focused executable checks for the three critical coupling branches. -/

example :
    traceStepCache ({1, 3} : Finset Page)
        (coupledEvict (.ordered 1 2) {1, 3} {2, 3} 2 4) 4 =
      traceStepCache ({2, 3} : Finset Page) 2 4 := by
  have hdiff : OnePageDiff ({1, 3} : Finset Page) {2, 3} 1 2 := by
    simp [OnePageDiff]
  simp [coupledEvict, traceStepCache, hdiff.erase_eq]

example : OnePageDiff
    ({1, 3} : Finset Page)
    (traceStepCache ({2, 3} : Finset Page) 3 1) 3 2 := by
  have hdiff : OnePageDiff ({1, 3} : Finset Page) {2, 3} 1 2 := by
    simp [OnePageDiff]
  simpa [traceStepCache] using hdiff.hit_left_fault 3 (by decide) (by decide)

example :
    traceStepCache ({1, 3} : Finset Page)
        (coupledEvict (.credited 1 2) {1, 3} {2, 3} 0 2) 2 =
      ({2, 3} : Finset Page) := by
  have hdiff : OnePageDiff ({1, 3} : Finset Page) {2, 3} 1 2 := by
    simp [OnePageDiff]
  change insert 2 (({1, 3} : Finset Page).erase 1) = ({2, 3} : Finset Page)
  exact hdiff.insert_right_erase_left

lemma coupledCache_of_le (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (s : ℕ) (hs : start ≤ s) :
    coupledCache source start A mode s =
      (couplingCore source start A mode (s - start)).cache := by
  simp [coupledCache, Nat.not_lt.mpr hs]

/-- Package the boundary-aware splice as a legal trace. -/
def coupledLegalTrace (source : LegalTrace C₀ σ) (start : ℕ)
    (hstartPos : 0 < start) (_hstart : start ≤ σ.length)
    (A : Finset Page) (boundaryEvict a b : Page)
    (hboundaryMem :
      σ.getD (start - 1) 0 ∉ source.cache (start - 1) →
        boundaryEvict ∈ source.cache (start - 1))
    (hboundaryStep :
      A = traceStepCache (source.cache (start - 1)) boundaryEvict
        (σ.getD (start - 1) 0))
    (hdiff : OnePageDiff A (source.cache start) a b) :
    LegalTrace C₀ σ where
  cache := coupledCache source start A (.ordered a b)
  evict := coupledTraceEvict source start boundaryEvict A (.ordered a b)
  init := by
    rw [coupledCache_of_lt source start A (.ordered a b) 0 hstartPos]
    exact source.init
  step := by
    intro t ht
    change coupledCache source start A (.ordered a b) (t + 1) =
      traceStepCache (coupledCache source start A (.ordered a b) t)
        (coupledTraceEvict source start boundaryEvict A (.ordered a b) t)
        (σ.getD t 0)
    by_cases hprefix : t + 1 < start
    · have htstart : t < start := by omega
      simpa [coupledCache, coupledTraceEvict, hprefix, htstart, traceStepCache] using
        source.step t ht
    · by_cases hboundary : t + 1 = start
      · have htEq : t = start - 1 := by omega
        subst t
        have hminus : start - 1 + 1 = start := by omega
        have hltprev : start - 1 < start := by omega
        simpa [coupledCache, coupledTraceEvict, hminus, hltprev] using hboundaryStep
      · have htge : start ≤ t := by omega
        have hsuccge : start ≤ t + 1 := by omega
        have hsubsucc : (t + 1) - start = (t - start) + 1 := by omega
        have habsolute : start + (t - start) = t := by omega
        rw [coupledCache_of_le source start A (.ordered a b) t htge]
        rw [coupledCache_of_le source start A (.ordered a b) (t + 1) hsuccge]
        have hevict :
            coupledTraceEvict source start boundaryEvict A (.ordered a b) t =
              (couplingCore source start A (.ordered a b) (t - start)).evict := by
          simp [coupledTraceEvict, hprefix, hboundary]
        rw [hevict, hsubsucc, couplingCore_cache_succ, habsolute]
  evict_mem := by
    intro t ht hmiss
    by_cases hprefix : t + 1 < start
    · have htstart : t < start := by omega
      have hmissSource : σ.getD t 0 ∉ source.cache t := by
        simpa [coupledCache, htstart] using hmiss
      simpa [coupledCache, coupledTraceEvict, hprefix, htstart] using
        source.evict_mem t ht hmissSource
    · by_cases hboundary : t + 1 = start
      · have htEq : t = start - 1 := by omega
        subst t
        have hminus : start - 1 + 1 = start := by omega
        have hltprev : start - 1 < start := by omega
        have hmissSource :
            σ.getD (start - 1) 0 ∉ source.cache (start - 1) := by
          simpa [coupledCache, hltprev] using hmiss
        simpa [coupledCache, coupledTraceEvict, hminus, hltprev] using
          hboundaryMem hmissSource
      · have htge : start ≤ t := by omega
        have habsolute : start + (t - start) = t := by omega
        have hmissCore : σ.getD (start + (t - start)) 0 ∉
            (couplingCore source start A (.ordered a b) (t - start)).cache := by
          simpa [habsolute, coupledCache, Nat.not_lt.mpr htge] using hmiss
        have hcore := couplingCore_evict_mem source start A a b hdiff (t - start)
          (by simpa [habsolute] using ht) hmissCore
        simpa [coupledCache, coupledTraceEvict, Nat.not_lt.mpr htge,
          hprefix, hboundary] using hcore

/-- Split a legal trace's total misses into a prefix and a shifted suffix. -/
lemma traceMisses_split (T : LegalTrace C₀ σ) (start : ℕ)
    (hstart : start ≤ σ.length) :
    traceMisses T =
      traceMissesFrom T 0 start +
        traceMissesFrom T start (σ.length - start) := by
  unfold traceMisses traceMissesFrom cacheMissesFrom cacheFaultAt traceFaultAt
  rw [show σ.length = start + (σ.length - start) by omega]
  rw [Finset.sum_range_add]
  simp [faultInCache]

/-- Suffix miss counts agree when the boundary caches agree pointwise. -/
lemma traceMissesFrom_congr (T U : LegalTrace C₀ σ) (start count : ℕ)
    (hcache : ∀ n, n < count → T.cache (start + n) = U.cache (start + n)) :
    traceMissesFrom T start count = traceMissesFrom U start count := by
  unfold traceMissesFrom cacheMissesFrom
  apply Finset.sum_congr rfl
  intro n hn
  unfold cacheFaultAt
  rw [hcache n (Finset.mem_range.mp hn)]

/-- The splice has the same strict-prefix miss count as the source. -/
lemma coupledLegalTrace_prefix_misses
    (source : LegalTrace C₀ σ) (start : ℕ)
    (hstartPos : 0 < start) (hstart : start ≤ σ.length)
    (A : Finset Page) (boundaryEvict a b : Page)
    (hboundaryMem :
      σ.getD (start - 1) 0 ∉ source.cache (start - 1) →
        boundaryEvict ∈ source.cache (start - 1))
    (hboundaryStep :
      A = traceStepCache (source.cache (start - 1)) boundaryEvict
        (σ.getD (start - 1) 0))
    (hdiff : OnePageDiff A (source.cache start) a b) :
    traceMissesFrom
        (coupledLegalTrace source start hstartPos hstart A boundaryEvict a b
          hboundaryMem hboundaryStep hdiff)
        0 start =
      traceMissesFrom source 0 start := by
  apply traceMissesFrom_congr
  intro n hn
  change coupledCache source start A (.ordered a b) (0 + n) = source.cache (0 + n)
  simpa using coupledCache_of_lt source start A (.ordered a b) n hn

/-- The splice's shifted suffix miss count is the recursive core miss count. -/
lemma coupledLegalTrace_suffix_misses
    (source : LegalTrace C₀ σ) (start : ℕ)
    (hstartPos : 0 < start) (hstart : start ≤ σ.length)
    (A : Finset Page) (boundaryEvict a b : Page)
    (hboundaryMem :
      σ.getD (start - 1) 0 ∉ source.cache (start - 1) →
        boundaryEvict ∈ source.cache (start - 1))
    (hboundaryStep :
      A = traceStepCache (source.cache (start - 1)) boundaryEvict
        (σ.getD (start - 1) 0))
    (hdiff : OnePageDiff A (source.cache start) a b)
    (count : ℕ) :
    traceMissesFrom
        (coupledLegalTrace source start hstartPos hstart A boundaryEvict a b
          hboundaryMem hboundaryStep hdiff)
        start count =
      couplingMisses source start A (.ordered a b) count := by
  unfold traceMissesFrom cacheMissesFrom couplingMisses
  apply Finset.sum_congr rfl
  intro n hn
  unfold cacheFaultAt
  change faultInCache (coupledCache source start A (.ordered a b) (start + n))
      (σ.getD (start + n) 0) =
    faultInCache (couplingCore source start A (.ordered a b) n).cache
      (σ.getD (start + n) 0)
  rw [coupledCache_of_le source start A (.ordered a b) (start + n) (by omega)]
  simp

/--
Boundary-aware ordered/credited coupling constructs a legal full trace and
does not increase total misses.
-/
theorem exists_coupled_suffix
    (source : LegalTrace C₀ σ) (start : ℕ)
    (hstartPos : 0 < start) (hstart : start ≤ σ.length)
    (A : Finset Page) (boundaryEvict a b : Page)
    (hboundaryMem :
      σ.getD (start - 1) 0 ∉ source.cache (start - 1) →
        boundaryEvict ∈ source.cache (start - 1))
    (hboundaryStep :
      A = traceStepCache (source.cache (start - 1)) boundaryEvict
        (σ.getD (start - 1) 0))
    (hdiff : OnePageDiff A (source.cache start) a b)
    (hfarther : Farther (nextUse σ start b) (nextUse σ start a)) :
    ∃ transformed : LegalTrace C₀ σ,
      (∀ s, s < start → transformed.cache s = source.cache s) ∧
      transformed.cache start = A ∧
      traceMisses transformed ≤ traceMisses source := by
  let transformed := coupledLegalTrace source start hstartPos hstart A boundaryEvict a b
    hboundaryMem hboundaryStep hdiff
  refine ⟨transformed, ?_, ?_, ?_⟩
  · intro s hs
    exact coupledCache_of_lt source start A (.ordered a b) s hs
  · exact coupledCache_start source start A (.ordered a b)
  · have hprefix := coupledLegalTrace_prefix_misses source start hstartPos hstart
      A boundaryEvict a b hboundaryMem hboundaryStep hdiff
    have hsuffixEq := coupledLegalTrace_suffix_misses source start hstartPos hstart
      A boundaryEvict a b hboundaryMem hboundaryStep hdiff (σ.length - start)
    have hbound : start + (σ.length - start) ≤ σ.length := by omega
    have hsuffix := couplingMisses_le source start A a b hdiff hfarther
      (σ.length - start) hbound
    calc
      traceMisses transformed =
          traceMissesFrom transformed 0 start +
            traceMissesFrom transformed start (σ.length - start) :=
        traceMisses_split transformed start hstart
      _ = traceMissesFrom source 0 start +
            couplingMisses source start A (.ordered a b) (σ.length - start) := by
        rw [hprefix, hsuffixEq]
      _ ≤ traceMissesFrom source 0 start +
            traceMissesFrom source start (σ.length - start) :=
        Nat.add_le_add_left hsuffix _
      _ = traceMisses source := (traceMisses_split source start hstart).symm

end Caching

end CLRS
