import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# 27.3 Online caching

This section formalizes the **online caching (paging)** problem of CLRS §27.3
and the classical competitive-analysis bound that the **LRU** (least-recently-used)
eviction policy is `k`-competitive.  A cache holds at most `k` pages.  A request
for a page already in the cache is a *hit* (free); a request for an absent page
is a *miss*, and the page is loaded, evicting some resident page when the cache
is full.  An online policy must decide evictions without knowing future
requests; the offline optimum knows the whole request sequence.

Main results:

- Definition `lruStep` / `lruRun` / `lruMisses`: the LRU policy (cache kept as a
  most-recent-first list) and its miss count.
- Structure `Algorithm`: an arbitrary eviction algorithm over a `Finset` cache,
  bundled with its validity laws (it loads the request, only adds the request,
  and keeps the cache at size ≤ `k`), and `misses`.
- Lemma `distinct_fault`: a segment requesting `k + 1` distinct pages forces a
  miss for any size-`k` algorithm.
- Lemma `resident_fault`: a page resident at the start of a segment that then
  requests `k` other distinct pages forces a miss.

Current gaps:

- Theorem 27.3 (`lru_k_competitive`, the `k`-competitive upper bound for LRU) is
  **not yet formalized**.  The two fault lemmas above and the `Algorithm` model
  are the phase-partition machinery for the Sleator–Tarjan proof; the
  `lru_head_evict` lemma connecting LRU's fault position to the distinct-page
  count, and the final summation, remain to be added.
- The matching lower bound — no deterministic online algorithm is better than
  `k`-competitive — is recorded but not formalized here (the framework is set up
  so the adversary argument can be added directly).

Notation conventions used in this section:

- `k` : the cache size
- `L` : LRU's cache, a `List Page` ordered most-recent-first
- `C` : an algorithm's cache, a `Finset Page`
- `σ` : the request sequence
- `q` : a page
- `A` : an arbitrary eviction algorithm
-/

namespace CLRS

namespace OnlineCaching

variable {Page : Type} [DecidableEq Page]
variable {k : ℕ}

/-- The cache size bound: a cache holds at most `k` pages. -/
def AtMost (k : ℕ) (C : Finset Page) : Prop := C.card ≤ k

-- ---------------------------------------------------------------------------
-- LRU: the cache is a most-recent-first list.

/--
The **LRU step**: request `p` against the most-recent-first cache `L`.  A hit
moves `p` to the front; a miss prepends `p`, evicting the least-recently-used
tail when the cache already has `k` pages.
-/
def lruStep (k : ℕ) (L : List Page) (p : Page) : List Page :=
  if p ∈ L then p :: L.erase p
  else if L.length < k then p :: L
  else p :: L.dropLast

/-- The LRU cache after processing the request list `σ`. -/
def lruRun (k : ℕ) : List Page → List Page → List Page
  | L, [] => L
  | L, p :: σ => lruRun k (lruStep k L p) σ

/-- The number of LRU misses over `σ`, threading the cache. -/
def lruMissesGo (k : ℕ) : List Page → List Page → ℕ
  | _, [] => 0
  | L, p :: σ => (if p ∈ L then 0 else 1) + lruMissesGo k (lruStep k L p) σ

/-- The number of LRU misses over `σ` from the initial cache `L₀`. -/
def lruMisses (k : ℕ) (L₀ : List Page) (σ : List Page) : ℕ := lruMissesGo k L₀ σ

/-- The 0-indexed position of `q` in a most-recent-first list: the number of
pages strictly more recent than `q` (junk when `q ∉ L`). -/
def lruPos (q : Page) (L : List Page) : ℕ := (L.takeWhile (fun x => x ≠ q)).length

-- ---------------------------------------------------------------------------
-- An arbitrary eviction algorithm (the "adversary" / offline optimum).

/--
A deterministic paging algorithm with cache size bound `k`.  `step C p` is the
cache after serving request `p` from cache `C`; the bundled laws say it loads
`p`, only ever adds `p`, and keeps at most `k` resident pages.  This is the
standing model of an online or offline adversary algorithm (CLRS §27.3).
-/
structure Algorithm (Page : Type) [DecidableEq Page] (k : ℕ) where
  step : Finset Page → Page → Finset Page
  step_loads : ∀ C p, p ∈ step C p
  step_subset : ∀ C p, step C p ⊆ insert p C
  step_size : ∀ C p, (step C p).card ≤ k

/-- The algorithm's cache after processing `σ`. -/
def runGo (A : Algorithm Page k) : Finset Page → List Page → Finset Page
  | C, [] => C
  | C, p :: σ => runGo A (A.step C p) σ

/-- The number of misses of `A` over `σ`, threading the cache. -/
def missesGo (A : Algorithm Page k) : Finset Page → List Page → ℕ
  | _, [] => 0
  | C, p :: σ => (if p ∈ C then 0 else 1) + missesGo A (A.step C p) σ

/-- The number of misses of `A` over `σ` from the initial cache `C₀`. -/
def misses (A : Algorithm Page k) (C₀ : Finset Page) (σ : List Page) : ℕ :=
  missesGo A C₀ σ

-- ---------------------------------------------------------------------------
-- Basic facts about the algorithm's cache.

/-- The algorithm's cache never shrinks the set of requested pages beyond the
initial cache: `runGo A C σ ⊆ C ∪ σ.toFinset`. -/
lemma runGo_subset (A : Algorithm Page k) (C : Finset Page) (σ : List Page) :
    runGo A C σ ⊆ C ∪ σ.toFinset := by
  induction σ generalizing C with
  | nil => simp [runGo]
  | cons p τ ih =>
      rw [runGo]
      refine subset_trans (ih (A.step C p)) ?_
      rw [List.toFinset_cons]
      intro x hx
      rw [Finset.mem_union] at hx ⊢
      rcases hx with hx | hx
      · rw [Finset.mem_insert]
        have hx' := A.step_subset C p hx
        rw [Finset.mem_insert] at hx'
        rcases hx' with rfl | hx'
        · right; simp
        · left; exact hx'
      · right
        rw [Finset.mem_insert]
        exact Or.inr hx

/-- The algorithm's cache has at most `k` pages throughout (given it starts
within the bound). -/
lemma runGo_size (A : Algorithm Page k) (C : Finset Page) (σ : List Page)
    (hC : C.card ≤ k) : (runGo A C σ).card ≤ k := by
  induction σ generalizing C with
  | nil => simpa [runGo] using hC
  | cons p τ ih =>
      rw [runGo]
      exact ih (A.step C p) (A.step_size C p)

/-- If a run has no misses, every requested page was already resident: the
requested pages are a subset of the initial cache. -/
lemma missesGo_eq_zero_subset (A : Algorithm Page k) (C : Finset Page) (σ : List Page)
    (h : missesGo A C σ = 0) : σ.toFinset ⊆ C := by
  induction σ generalizing C with
  | nil => simp
  | cons p τ ih =>
      rw [missesGo] at h
      have hp : p ∈ C := by
        by_cases hp : p ∈ C
        · exact hp
        · simp [hp] at h
      have hτ : missesGo A (A.step C p) τ = 0 := by
        by_cases hp' : p ∈ C
        · simpa [hp'] using h
        · simp [hp'] at h
      rw [List.toFinset_cons]
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hp
      · have hx' := ih (A.step C p) hτ hx
        have hx'' := A.step_subset C p hx'
        rw [Finset.mem_insert] at hx''
        rcases hx'' with rfl | hxC
        · exact hp
        · exact hxC

/-- A segment that requests `k + 1` distinct pages forces a miss for any
size-`k` algorithm. -/
lemma distinct_fault (A : Algorithm Page k) (C : Finset Page) (ρ : List Page)
    (hC : C.card ≤ k) (hk : k < ρ.toFinset.card) : 1 ≤ missesGo A C ρ := by
  by_contra hzero
  have h0 : missesGo A C ρ = 0 := by omega
  have hsub := missesGo_eq_zero_subset A C ρ h0
  have hcard : ρ.toFinset.card ≤ C.card := Finset.card_le_card hsub
  omega

/-- A page resident at the start of a segment that then requests `k` other
distinct pages forces a miss for any size-`k` algorithm. -/
lemma resident_fault (A : Algorithm Page k) (C : Finset Page) (p : Page) (ρ : List Page)
    (hC : C.card ≤ k) (hp : p ∈ C) (hk : k ≤ (ρ.toFinset.erase p).card) :
    1 ≤ missesGo A C ρ := by
  by_contra hzero
  have h0 : missesGo A C ρ = 0 := by omega
  have hsub := missesGo_eq_zero_subset A C ρ h0
  -- Every distinct page of ρ lies in C; since ρ also requests k pages other than
  -- p, those k pages live in C.erase p, but C has at most k pages and p already
  -- occupies one of them -- a contradiction.
  have hle : (ρ.toFinset.erase p).card ≤ (C.erase p).card := by
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, hsub hx.2⟩
  have hCardErase : (C.erase p).card = C.card - 1 := Finset.card_erase_of_mem hp
  have hCp : 0 < C.card := Finset.card_pos.mpr ⟨p, hp⟩
  omega

-- ---------------------------------------------------------------------------
-- Structural facts about the LRU list cache.

/-- The pages strictly more recent than `p` in a most-recent-first cache `L`
(the `takeWhile` prefix of `L` up to `p`), as a `Finset`. -/
def front (p : Page) (L : List Page) : Finset Page :=
  (L.takeWhile (fun x => x ≠ p)).toFinset

/-- The `Finset` of a no-duplicate list has its length as cardinality. -/
lemma toFinset_card_of_nodup {L : List Page} (h : L.Nodup) : L.toFinset.card = L.length := by
  unfold List.toFinset
  rw [List.dedup_eq_self.mpr h]

/-- `lruStep` preserves the no-duplicate invariant of the cache list. -/
lemma lruStep_nodup (k : ℕ) (L : List Page) (p : Page) (h : L.Nodup) :
    (lruStep k L p).Nodup := by
  unfold lruStep
  split_ifs with hp hl
  · exact List.nodup_cons.mpr ⟨by simp, h.erase p⟩
  · exact List.nodup_cons.mpr ⟨hp, h⟩
  · refine List.nodup_cons.mpr ⟨?_, (List.dropLast_sublist L).nodup h⟩
    intro hpd
    exact hp (List.mem_of_mem_dropLast hpd)

/-- `lruRun` preserves the no-duplicate invariant of the cache list. -/
lemma lruRun_nodup (k : ℕ) (L : List Page) (ρ : List Page) (h : L.Nodup) :
    (lruRun k L ρ).Nodup := by
  induction ρ generalizing L with
  | nil => simpa [lruRun] using h
  | cons p ρ' ih => simp [lruRun]; exact ih (lruStep k L p) (lruStep_nodup k L p h)

/-- The cache after a concatenation of request lists is the sequential run. -/
lemma lruRun_append (k : ℕ) (L : List Page) (σ τ : List Page) :
    lruRun k L (σ ++ τ) = lruRun k (lruRun k L σ) τ := by
  induction σ generalizing L with
  | nil => rfl
  | cons p σ' ih => simp [lruRun, ih]

/-- The miss count over a concatenation splits additively. -/
lemma lruMissesGo_append (k : ℕ) (L : List Page) (σ τ : List Page) :
    lruMissesGo k L (σ ++ τ) = lruMissesGo k L σ + lruMissesGo k (lruRun k L σ) τ := by
  induction σ generalizing L with
  | nil => simp [lruMissesGo, lruRun]
  | cons p σ' ih =>
      simp only [lruMissesGo]
      rw [ih]
      omega

/-- Membership after a single `lruStep`, unfolded into the hit / not-full miss /
full miss cases. -/
lemma mem_lruStep (k : ℕ) (L : List Page) (p q : Page) :
    q ∈ lruStep k L p ↔
      (if p ∈ L then q ∈ L
       else if L.length < k then q = p ∨ q ∈ L
       else q = p ∨ q ∈ L.dropLast) := by
  unfold lruStep
  split_ifs with hp hl
  · -- hit: q ∈ p :: L.erase p ↔ q ∈ L
    rw [List.mem_cons]
    constructor
    · intro h
      rcases h with h | h
      · exact h ▸ hp
      · exact List.mem_of_mem_erase h
    · intro h
      by_cases hqp : q = p
      · exact Or.inl hqp
      · exact Or.inr ((List.mem_erase_of_ne hqp).mpr h)
  · -- miss, not full: q ∈ p :: L ↔ q = p ∨ q ∈ L
    rw [List.mem_cons]
  · -- miss, full: q ∈ p :: L.dropLast ↔ q = p ∨ q ∈ L.dropLast
    rw [List.mem_cons]

/-- Removing `q ≠ p` cannot enlarge the `takeWhile (· ≠ p)` prefix. -/
lemma takeWhile_erase_subset {p q : Page} {L : List Page} (hqp : q ≠ p) :
    (L.erase q).takeWhile (fun x => x ≠ p) ⊆ L.takeWhile (fun x => x ≠ p) := by
  induction L with
  | nil => simp
  | cons x rest ih =>
      by_cases hxq : x = q
      · subst q
        by_cases hxp : x = p
        · exact (hqp hxp).elim
        · simp [hxp, List.erase_cons_head]
          intro a ha
          exact List.mem_cons_of_mem x (by simpa using ha)
      · by_cases hxp : x = p
        · subst p
          simp [hxq]
        · simp [hxq, hxp]
          intro a ha
          rw [List.mem_cons] at ha ⊢
          rcases ha with ha | ha
          · exact Or.inl ha
          · exact Or.inr (ih ha)

/-- Dropping the last element cannot enlarge the `takeWhile (· ≠ p)` prefix. -/
lemma takeWhile_dropLast_subset {p : Page} {L : List Page} :
    L.dropLast.takeWhile (fun x => x ≠ p) ⊆ L.takeWhile (fun x => x ≠ p) := by
  induction L with
  | nil => simp
  | cons x rest ih =>
      cases rest with
      | nil => simp
      | cons y ys =>
          have hrest : rest ≠ [] := by simp
          rw [List.dropLast_cons_of_ne_nil hrest]
          by_cases hxp : x = p
          · subst p; simp
          · simp [hxp]
            intro a ha
            rw [List.mem_cons] at ha ⊢
            rcases ha with ha | ha
            · exact Or.inl ha
            · exact Or.inr (ih ha)

/-- One step grows the front of a page by at most the requested page. -/
lemma lruStep_front_subset (k : ℕ) (L : List Page) (p q : Page) :
    front p (lruStep k L q) ⊆ {q} ∪ front p L := by
  by_cases hqp : q = p
  · subst q
    simp [front, lruStep]
  · unfold front lruStep
    by_cases hq : q ∈ L
    · simp [hq, hqp]
      intro x hx
      rw [List.mem_toFinset] at hx
      simp [hqp] at hx
      rcases hx with hx | hx
      · left; simp [hx]
      · right; rw [List.mem_toFinset]; exact takeWhile_erase_subset hqp hx
    · by_cases hl : L.length < k
      · simp [hq, hl]
        intro x hx
        rw [List.mem_toFinset] at hx
        simp [hqp] at hx
        rcases hx with hx | hx
        · left; simp [hx]
        · right; rw [List.mem_toFinset]; exact hx
      · simp [hq, hl]
        intro x hx
        rw [List.mem_toFinset] at hx
        simp [hqp] at hx
        rcases hx with hx | hx
        · left; simp [hx]
        · right; rw [List.mem_toFinset]; exact takeWhile_dropLast_subset hx

/-- The front of `p` after a run is a subset of the requested pages together with
the pages that were already in front of `p` initially. -/
lemma lru_front_bound (k : ℕ) (L : List Page) (p : Page) (ρ : List Page) :
    front p (lruRun k L ρ) ⊆ ρ.toFinset ∪ front p L := by
  induction ρ generalizing L with
  | nil => simp [lruRun]
  | cons q ρ' ih =>
      have hstep := lruStep_front_subset k L p q
      have hih := ih (L := lruStep k L q)
      intro x hx
      have hx' := hih hx
      rw [Finset.mem_union] at hx' ⊢
      rcases hx' with hxρ | hxf
      · left
        rw [List.toFinset_cons, Finset.mem_insert]
        exact Or.inr hxρ
      · have hxf' := hstep hxf
        rw [Finset.mem_union, Finset.mem_singleton] at hxf'
        rcases hxf' with hxq | hxfL
        · left
          rw [List.toFinset_cons, Finset.mem_insert]
          exact Or.inl hxq
        · right; exact hxfL

/-- When `h` is the last element of a list, the `takeWhile (· ≠ h)` prefix is
exactly the drop-last tail. -/
lemma takeWhile_ne_dropLast {h : Page} {L : List Page} (hL : h ∈ L)
    (hlast : h ∉ L.dropLast) :
    L.takeWhile (fun x => x ≠ h) = L.dropLast := by
  have hnil : L ≠ [] := by intro h0; subst h0; simp at hL
  have hget : h = L.getLast hnil := by
    have hmem : h ∈ L.dropLast ++ [L.getLast hnil] := by
      rw [List.dropLast_append_getLast hnil]
      exact hL
    rw [List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact False.elim (hlast hmem)
    · simpa using hmem
  rw [← List.dropLast_append_getLast hnil]
  rw [← hget]
  rw [List.takeWhile_append_of_pos (p := fun x => x ≠ h)]
  · simp
  · intro x hx
    apply decide_eq_true
    intro hxeq
    exact hlast (by simpa [hxeq] using hx)

/-- When a page `h` is evicted in a single step, the front of `h` (which then has
`k - 1` distinct pages) together with the evicting request has at least `k` pages. -/
lemma lruStep_evict_card (k : ℕ) (L : List Page) (h q : Page)
    (hNodup : L.Nodup) (hL : h ∈ L) (hev : h ∉ lruStep k L q) :
    k ≤ (front h L ∪ {q}).card := by
  have hnot : ¬ (if q ∈ L then h ∈ L
      else if L.length < k then h = q ∨ h ∈ L
      else h = q ∨ h ∈ L.dropLast) := by
    intro h'
    exact hev ((mem_lruStep k L q h).mpr h')
  have hqL : q ∉ L := by intro hq; apply hnot; simp [hq, hL]
  have hfull : k ≤ L.length := by
    by_contra hn
    have hl : L.length < k := by omega
    apply hnot; simp [hqL, hl, hL]
  have hlast : h ∉ L.dropLast := by intro hd; apply hnot; simp [hqL, hfull, hd]
  have hfront : front h L = L.dropLast.toFinset := by
    unfold front
    congr 1
    exact takeWhile_ne_dropLast hL hlast
  have hfront_card : k - 1 ≤ (front h L).card := by
    rw [hfront]
    rw [toFinset_card_of_nodup ((List.dropLast_sublist L).nodup hNodup)]
    rw [List.dropLast_eq_take, List.length_take]
    omega
  have hq_front : q ∉ front h L := by
    intro hq'
    rw [hfront] at hq'
    exact hqL (List.mem_of_mem_dropLast (by simpa using hq'))
  have hcard : (front h L ∪ {q}).card = (front h L).card + 1 := by
    rw [Finset.card_insert_of_notMem hq_front]
  omega

/-- If a page `h ∈ L` is not in the cache after a run, then the distinct pages of
`ρ` other than `h`, together with the pages initially in front of `h`, number at
least `k`.  For `h` at the front this is the "head eviction" lemma: evicting the
most-recently-used page needs `k` other distinct requests. -/
lemma lru_evict_ge (k : ℕ) (L : List Page) (h : Page) (ρ : List Page)
    (hNodup : L.Nodup) (hL : h ∈ L) (hev : h ∉ lruRun k L ρ) :
    k ≤ (front h L ∪ ρ.toFinset.erase h).card := by
  induction ρ generalizing L with
  | nil => simp [lruRun] at hev
  | cons q ρ' ih =>
      let L' := lruStep k L q
      by_cases hL' : h ∈ L'
      · have hih := ih (L := L') (lruStep_nodup k L q hNodup) hL' (by simpa [lruRun, L'] using hev)
        have hle : (front h L' ∪ ρ'.toFinset.erase h).card ≤
            (front h L ∪ (q :: ρ').toFinset.erase h).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_union] at hx ⊢
          rcases hx with hx | hx
          · have hx' := lruStep_front_subset k L h q hx
            rw [Finset.mem_union, Finset.mem_singleton] at hx'
            rcases hx' with hxq | hxf
            · right
              rw [List.toFinset_cons, Finset.mem_erase, Finset.mem_insert]
              refine ⟨?_, Or.inl hxq⟩
              intro hqh
              subst q
              have : x ∉ front h (lruStep k L h) := by simp [front, lruStep]
              exact this hx
            · left; exact hxf
          · left
            rw [List.toFinset_cons, Finset.mem_erase, Finset.mem_insert]
            exact ⟨(Finset.mem_erase.mp hx).1, Or.inr (Finset.mem_erase.mp hx).2⟩
        omega
      · have hcard := lruStep_evict_card k L h q hNodup hL hL'
        have hqh : q ≠ h := by
          intro hqh
          subst q
          exact hL' (by simp [lruStep, hL])
        have hle : (front h L ∪ {q}).card ≤ (front h L ∪ (q :: ρ').toFinset.erase h).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_union] at hx ⊢
          rcases hx with hxf | hxq
          · left; exact hxf
          · right
            rw [Finset.mem_singleton] at hxq
            rw [List.toFinset_cons, Finset.mem_erase, Finset.mem_insert]
            refine ⟨by simpa [hxq] using hqh, Or.inl hxq⟩
        omega

/--
**LRU head eviction.**  If `h` is the most-recently-used page of a full cache at
the start of a segment, and `h` is evicted during the segment, then the segment
requests at least `k` other distinct pages.  This is the key fact that a single
page can only be faulted once within any segment of at most `k` distinct pages.
-/
lemma lru_head_evict (k : ℕ) (h : Page) (rest ρ : List Page) :
    h ∉ lruRun k (h :: rest) ρ → k ≤ (ρ.toFinset.erase h).card := by
  intro hev
  have hge := lru_evict_ge k (h :: rest) h ρ (by
    rw [List.nodup_cons]
    exact ⟨by simp, by simp⟩) (by simp) hev
  simpa [front] using hge

/-- Erasing `p` before or after dropping the last element commutes, when `p` is
not the last element. -/
lemma erase_dropLast {p : Page} {L : List Page} (hp : p ∈ L.dropLast) :
    (L.dropLast).erase p = (L.erase p).dropLast := by
  have hnil : L ≠ [] := by intro h0; subst h0; simp at hp
  have hL : L = L.dropLast ++ [L.getLast hnil] := (List.dropLast_append_getLast hnil).symm
  have herase : L.erase p = (L.dropLast).erase p ++ [L.getLast hnil] := by
    rw [hL]
    exact List.erase_append_left [L.getLast hnil] hp
  rw [herase]
  rw [List.dropLast_append_of_ne_nil]
  · rfl
  · intro h
    exact List.noConfusion h

/-- When `p` survives a step `q ≠ p`, erasing `p` from the resulting cache equals
running the step on the size-`(k - 1)` cache with `p` already erased. -/
lemma lruStep_erase (k : ℕ) (L : List Page) (q p : Page)
    (hNodup : L.Nodup) (hp : p ∈ L) (hqp : q ≠ p) (hkeep : p ∈ lruStep k L q) :
    (lruStep k L q).erase p = lruStep (k - 1) (L.erase p) q := by
  unfold lruStep
  by_cases hq : q ∈ L
  · have hq_erase : q ∈ L.erase p := (List.mem_erase_of_ne hqp).mpr hq
    simp [hq, hqp, hq_erase]
    rw [List.erase_comm q p]
    rfl
  · by_cases hl : L.length < k
    · have hq_erase : q ∉ L.erase p := by
        intro h; exact hq (List.mem_of_mem_erase h)
      have hlen : (L.erase p).length < k - 1 := by
        rw [List.length_erase_of_mem hp]
        omega
      simp [hq, hl, hqp, hq_erase, hlen]
    · have hq_erase : q ∉ L.erase p := by
        intro h; exact hq (List.mem_of_mem_erase h)
      have hlen : ¬ (L.erase p).length < k - 1 := by
        rw [List.length_erase_of_mem hp]
        omega
      have hp_dropLast : p ∈ L.dropLast := by
        have : p ∈ q :: L.dropLast := by simpa [hq, hl] using hkeep
        rw [List.mem_cons] at this
        rcases this with this | this
        · exact (hqp this.symm).elim
        · exact this
      simp [hq, hl, hqp, hq_erase, hlen]
      exact erase_dropLast hp_dropLast

/-- The miss count commutes with erasing a page that is never evicted: with the
page `p` pinned in the cache, LRU over a size-`k` cache from `L` has the same
misses as a size-`(k - 1)` cache from `L.erase p` over `ρ.erase p`. -/
lemma lru_miss_shrink (k : ℕ) (L : List Page) (ρ : List Page) (p : Page)
    (hNodup : L.Nodup) (hp : p ∈ L) (hkeep : ∀ τ, List.IsPrefix τ ρ → p ∈ lruRun k L τ) :
    lruMissesGo k L ρ = lruMissesGo (k - 1) (L.erase p) (ρ.erase p) := by
  induction ρ generalizing L with
  | nil => simp
  | cons q rest ih =>
      have hq : p ∈ lruStep k L q := by
        have h := hkeep [q] (⟨rest, by simp⟩ : List.IsPrefix [q] (q :: rest))
        simpa [lruRun] using h
      have hkeep' : ∀ τ, List.IsPrefix τ rest → p ∈ lruRun k (lruStep k L q) τ := by
        intro τ hτ
        rcases hτ with ⟨t, ht⟩
        have hprefix : List.IsPrefix ([q] ++ τ) (q :: rest) := ⟨t, by simp [ht]⟩
        have h := hkeep ([q] ++ τ) hprefix
        rwa [lruRun_append] at h
      have hih := ih (L := lruStep k L q) (lruStep_nodup k L q hNodup) hq hkeep'
      by_cases hqp : q = p
      · subst q
        rw [lruMissesGo]
        simp [hp]
        rw [hih]
        simp
      · have hq_in : q ∈ L ↔ q ∈ L.erase p := (List.mem_erase_of_ne hqp).symm
        have hstep_erase := lruStep_erase k L q p hNodup hp hqp hq
        rw [lruMissesGo]
        rw [hih]
        rw [hstep_erase]
        have herase : (q :: rest).erase p = q :: rest.erase p := by simp [hqp]
        rw [herase]
        rw [lruMissesGo]
        rw [hq_in]

/-- LRU makes at most one fault per distinct requested page, whenever at most
`k` distinct pages are requested. -/
lemma lru_miss_le_distinct (k : ℕ) (L : List Page) (ρ : List Page)
    (hNodup : L.Nodup) (hcard : ρ.toFinset.card ≤ k) :
    lruMissesGo k L ρ ≤ ρ.toFinset.card := by
  induction ρ generalizing k L with
  | nil => simp
  | cons p ρ' ih =>
      let L' : List Page := lruStep k L p
      have hNodup' : L'.Nodup := lruStep_nodup k L p hNodup
      rw [lruMissesGo, List.toFinset_cons]
      by_cases hpL : p ∈ L
      · have hrec := ih (k := k) (L := L') hNodup' (by
          have : ρ'.toFinset.card ≤ (p :: ρ').toFinset.card := by
            rw [List.toFinset_cons]
            exact Finset.card_le_card (Finset.subset_insert _ _)
          omega)
        simp [hpL]
        calc
          lruMissesGo k L' ρ' ≤ ρ'.toFinset.card := hrec
          _ ≤ (insert p ρ'.toFinset).card := Finset.card_le_card (Finset.subset_insert _ _)
      · by_cases hpρ : p ∈ ρ'.toFinset
        · -- p is re-requested: it is pinned, so shrink to a size-(k-1) cache
          have hcard' : (ρ'.toFinset.erase p).card ≤ k - 1 := by
            have hρ : ρ'.toFinset.card ≤ k := by
              have hins : (insert p ρ'.toFinset).card ≤ k := by simpa [List.toFinset_cons] using hcard
              have : (insert p ρ'.toFinset).card = ρ'.toFinset.card := Finset.card_insert_of_mem hpρ
              omega
            rw [Finset.card_erase_of_mem hpρ]
            omega
          have hL'head : ∃ t, L' = p :: t := by
            unfold L' lruStep
            by_cases hl : L.length < k
            · simp [hpL, hl]; exact ⟨L, rfl⟩
            · simp [hpL, hl]; exact ⟨L.dropLast, rfl⟩
          rcases hL'head with ⟨t, rfl⟩
          have hkeep : ∀ τ, List.IsPrefix τ ρ' → p ∈ lruRun k (p :: t) τ := by
            intro τ hτ
            have hcardτ : (τ.toFinset.erase p).card ≤ k - 1 := by
              have hsub : τ.toFinset.erase p ⊆ ρ'.toFinset.erase p := by
                intro x hx
                rw [Finset.mem_erase] at hx ⊢
                refine ⟨hx.1, ?_⟩
                rcases hτ with ⟨t', ht'⟩
                have hsub' : τ.toFinset ⊆ ρ'.toFinset := by
                  rw [ht', List.toFinset_append]
                  exact Finset.subset_union_left
                exact hsub' hx.2
              exact le_trans (Finset.card_le_card hsub) hcard'
            by_contra hnot
            have hge := lru_head_evict k p t τ hnot
            omega
          have hshrink := lru_miss_shrink k (p :: t) ρ' p (by simpa using hNodup') (by simp) hkeep
          have hrec := ih (k := k - 1) (L := t) (by
            have : (p :: t).Nodup := hNodup'
            exact (List.sublist_cons_self p t).nodup this) (by
              have : (ρ'.erase p).toFinset.card ≤ k - 1 := by
                have hto : (ρ'.erase p).toFinset = ρ'.toFinset.erase p := by
                  ext x
                  by_cases hxp : x = p <;> simp [hxp]
                rw [hto]
                exact hcard'
              exact this)
          simp [hpL]
          calc
            lruMissesGo k (p :: t) ρ' = lruMissesGo (k - 1) t (ρ'.erase p) := by
              simpa using hshrink
            _ ≤ (ρ'.erase p).toFinset.card := hrec
            _ = (ρ'.toFinset.erase p).card := by
              ext x
              by_cases hxp : x = p <;> simp [hxp]
            _ = ρ'.toFinset.card - 1 := Finset.card_erase_of_mem hpρ
            _ ≤ (insert p ρ'.toFinset).card := by
              rw [Finset.card_insert_of_mem hpρ]
              exact Nat.sub_le _ _
        · have hrec := ih (k := k) (L := L') hNodup' (by
            have : ρ'.toFinset.card ≤ (p :: ρ').toFinset.card := by
              rw [List.toFinset_cons]
              exact Finset.card_le_card (Finset.subset_insert _ _)
            omega)
          simp [hpL]
          have hins : (insert p ρ'.toFinset).card = ρ'.toFinset.card + 1 := by
            rw [Finset.card_insert_of_notMem hpρ]
          rw [hins]
          omega

end OnlineCaching

end CLRS

