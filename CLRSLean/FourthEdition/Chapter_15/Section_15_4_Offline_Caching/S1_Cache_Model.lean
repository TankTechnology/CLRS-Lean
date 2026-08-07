import Mathlib

/-!
# S1. Cache model

The eviction-cache model for the offline caching problem of CLRS §15.4
("Offline caching"): a request sequence is a list of pages, the cache is a
finite set of resident pages, and an eviction policy is a total function that
decides, at each fault, which resident page to evict.  Misses and hits are
counted position by position over the request list, and `nextUse` locates the
next request of a given page at or after a given position.

Main results:

- `Policy`: an eviction policy (a total eviction function, validity bundled)
- `Policy.step`: the cache transition induced by a policy on a request
- `cacheSeq`: the cache after each prefix of the request list
- `faultAt` / `misses` / `hits`: per-request miss indicator and the total
  miss and hit counts over the request list
- `misses_add_hits`: every request is a hit or a miss
- `step_card` / `cacheSeq_card`: policies preserve the cache size, so a cache
  of size `k` stays of size `k` throughout the run
- `nextUse`: the offset of the first request of a page at or after a given
  position, `none` when the page is never requested again

Notation conventions used in this section:

- `C` : cache (a finite set of resident pages)
- `σ` : request sequence
- `p`, `q` : pages
- `i`, `t` : positions in the request sequence
-/

namespace CLRS

open Finset
open scoped BigOperators

namespace Caching

/-- Pages are natural numbers; any countably infinite page universe is
equivalent. -/
abbrev Page := ℕ

/-- A cache of size `k` holds exactly `k` pages (CLRS §15.4). -/
def CacheSize (k : ℕ) (C : Finset Page) : Prop :=
  C.card = k

/--
An eviction policy is a total function that, at each request position `i`,
given the current cache `C` and the requested page `p`, returns the page to
evict when `p` is not resident.  The bundled `evict_mem` field records that a
fault evicts a resident page; on a hit the eviction value is junk.  Policies
are offline: they may use the position `i` (and hence the full request
sequence) when making the decision (CLRS §15.4).
-/
structure Policy where
  evict : ℕ → Finset Page → Page → Page
  evict_mem : ∀ i C p, p ∉ C → evict i C p ∈ C

/--
The cache transition of a policy: a hit keeps the cache unchanged, a fault
evicts the policy's chosen page and loads the requested page.
-/
def Policy.step (π : Policy) (i : ℕ) (C : Finset Page) (p : Page) : Finset Page :=
  if p ∈ C then C else insert p (C.erase (π.evict i C p))

/-- The cache after the first `t` requests (requests beyond the end of the
list are junk, so the sequence extends arbitrarily). -/
def cacheSeq (π : Policy) (C₀ : Finset Page) (σ : List Page) : ℕ → Finset Page
  | 0 => C₀
  | t + 1 => π.step t (cacheSeq π C₀ σ t) (σ.getD t 0)

/-- The transition preserves the number of resident pages. -/
lemma step_card (π : Policy) (i : ℕ) (C : Finset Page) (p : Page) :
    (π.step i C p).card = C.card := by
  unfold Policy.step
  by_cases hp : p ∈ C
  · rw [if_pos hp]
  · rw [if_neg hp]
    have he := π.evict_mem i C p hp
    rw [Finset.card_insert_of_notMem (by
      intro hmem
      exact hp (Finset.mem_erase.mp hmem).2)]
    rw [Finset.card_erase_of_mem he]
    have hcard : 0 < C.card := Finset.card_pos.mpr ⟨π.evict i C p, he⟩
    omega

/-- Every cache in the run of a policy has the same size as the initial
cache, so a cache of size `k` stays of size `k` throughout (CLRS §15.4). -/
lemma cacheSeq_card (π : Policy) (C₀ : Finset Page) (σ : List Page) (t : ℕ) :
    (cacheSeq π C₀ σ t).card = C₀.card := by
  induction t with
  | zero => rfl
  | succ t ih =>
      unfold cacheSeq
      rw [step_card]
      exact ih

/-- Whether the request at position `t` is a miss for the run of `π` from
`C₀` on `σ` (`0` or `1`). -/
def faultAt (π : Policy) (C₀ : Finset Page) (σ : List Page) (t : ℕ) : ℕ :=
  if σ.getD t 0 ∈ cacheSeq π C₀ σ t then 0 else 1

/-- The number of misses (faults) incurred by policy `π` on the request list
`σ` starting from the initial cache `C₀` (CLRS §15.4). -/
def misses (π : Policy) (C₀ : Finset Page) (σ : List Page) : ℕ :=
  ∑ t ∈ Finset.range σ.length, faultAt π C₀ σ t

/-- The number of hits (requests served from the cache) incurred by policy
`π` on the request list `σ` starting from the initial cache `C₀`. -/
def hits (π : Policy) (C₀ : Finset Page) (σ : List Page) : ℕ :=
  ∑ t ∈ Finset.range σ.length, if σ.getD t 0 ∈ cacheSeq π C₀ σ t then 1 else 0

/-- A sum over a shifted range splits into its first term and the shifted
tail. -/
lemma sum_range_shift {n : ℕ} (f : ℕ → ℕ) :
    (∑ t ∈ Finset.range (n + 1), f t) = f 0 + ∑ t ∈ Finset.range n, f (t + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      omega

/-- Every request is either a hit or a miss, so the two counts add up to the
length of the request list. -/
lemma misses_add_hits (π : Policy) (C₀ : Finset Page) (σ : List Page) :
    misses π C₀ σ + hits π C₀ σ = σ.length := by
  unfold misses hits
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ t ∈ Finset.range σ.length,
      faultAt π C₀ σ t + (if σ.getD t 0 ∈ cacheSeq π C₀ σ t then 1 else 0) = 1 := by
    intro t _
    unfold faultAt
    split <;> omega
  rw [Finset.sum_congr rfl hterm]
  simp

/-- The offset of the first request of `p` at or after position `i` in `σ`:
`nextUse σ i p = some j` means the request at absolute position `i + j` is
the first request of `p` at or after `i`; `none` means `p` is never requested
again (CLRS §15.4). -/
def nextUse (σ : List Page) (i : ℕ) (p : Page) : Option ℕ :=
  (σ.drop i).findIdx? (fun q => q = p)

/-- `nextUse σ i p = some j` exactly when the request at relative position
`j` of the suffix `σ.drop i` is `p` and no earlier request of the suffix is
`p`. -/
lemma nextUse_eq_some_iff {σ : List Page} {i p j : ℕ} :
    nextUse σ i p = some j ↔
      ∃ h : j < (σ.drop i).length, (σ.drop i)[j] = p ∧
        ∀ k (hk : k < j), (σ.drop i)[k] ≠ p := by
  unfold nextUse
  rw [List.findIdx?_eq_some_iff_getElem (p := fun q => q = p) (xs := σ.drop i)]
  simp

/-- `nextUse σ i p = none` exactly when no request at or after position `i`
is `p`. -/
lemma nextUse_eq_none_iff {σ : List Page} {i p : ℕ} :
    nextUse σ i p = none ↔ ∀ q, q ∈ σ.drop i → q ≠ p := by
  unfold nextUse
  rw [List.findIdx?_eq_none_iff]
  simp

/-- The element of a drop at a relative position is the element of the
original list at the shifted absolute position. -/
lemma getD_drop (l : List Page) (d : Page) (i j : ℕ) :
    (l.drop i).getD j d = l.getD (i + j) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  simp

/-- If `nextUse σ i p = some j`, then the request at absolute position
`i + j` is `p`, and no request strictly between `i` and `i + j` is `p`. -/
lemma getD_nextUse {σ : List Page} {i p j : ℕ} (h : nextUse σ i p = some j) :
    σ.getD (i + j) 0 = p ∧ ∀ k, i ≤ k → k < i + j → σ.getD k 0 ≠ p := by
  rcases (nextUse_eq_some_iff.mp h) with ⟨hlt, hget, hmin⟩
  constructor
  · rw [← getD_drop σ 0 i j]
    rw [List.getD_eq_getElem _ 0 hlt]
    exact hget
  · intro k hik hkj
    have hki : k - i < j := by omega
    have hne := hmin (k - i) hki
    have hget' : (σ.drop i).getD (k - i) 0 = σ.getD k 0 := by
      have hsub : (σ.drop i).getD (k - i) 0 = σ.getD (i + (k - i)) 0 := by
        rw [getD_drop σ 0 i (k - i)]
      rw [hsub]
      rw [Nat.add_sub_of_le hik]
    rw [← hget']
    rw [List.getD_eq_getElem _ 0 (Nat.lt_trans hki hlt)]
    exact hne

/-- If `nextUse σ i p = some j`, then the request at absolute position
`i + j` is `p`. -/
lemma getD_eq_nextUse {σ : List Page} {i p j : ℕ} (h : nextUse σ i p = some j) :
    σ.getD (i + j) 0 = p :=
  (getD_nextUse h).1

/-- If `nextUse σ i p = some j`, then no request strictly between `i` and
`i + j` is `p`. -/
lemma getD_ne_nextUse {σ : List Page} {i p j : ℕ} (h : nextUse σ i p = some j) {k : ℕ}
    (hik : i ≤ k) (hkj : k < i + j) :
    σ.getD k 0 ≠ p :=
  (getD_nextUse h).2 k hik hkj

end Caching

end CLRS
