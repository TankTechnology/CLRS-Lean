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

end OnlineCaching

end CLRS
