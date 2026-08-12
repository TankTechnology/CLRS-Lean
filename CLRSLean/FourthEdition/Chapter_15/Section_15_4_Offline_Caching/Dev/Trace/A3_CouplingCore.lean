import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Dev.Trace.A2_OnePageDiff

/-!
# Chapter 15.4 development: recursive coupling core

This file defines the transformed execution used by the local exchange.  The
definitions are total; their legality and miss accounting are proved in A4.
-/

namespace CLRS

open Finset

namespace Caching

/-- The phase of the one-page coupling. -/
inductive CouplingMode where
  | same
  | ordered (a b : Page)
  | credited (a b : Page)
deriving DecidableEq, Repr

/-- Apply one recorded eviction decision to a cache request. -/
def traceStepCache (C : Finset Page) (evict request : Page) : Finset Page :=
  if request ∈ C then C else insert request (C.erase evict)

/--
Choose the transformed eviction while mirroring the source.  If the source
hits its unique page, or evicts its unique page, the transformed side removes
its own unique page so that the caches merge.
-/
def coupledEvict (mode : CouplingMode) (A B : Finset Page)
    (sourceEvict request : Page) : Page :=
  match mode with
  | .same => sourceEvict
  | .ordered a b =>
      if request ∈ B ∧ request ∉ A then a
      else if sourceEvict = b then a else sourceEvict
  | .credited a b =>
      if request ∈ B ∧ request ∉ A then a
      else if sourceEvict = b then a else sourceEvict

/-- Update the coupling phase after both caches take one step. -/
def nextCouplingMode (mode : CouplingMode) (request sourceEvict : Page)
    (transformedNext sourceNext : Finset Page) : CouplingMode :=
  if transformedNext = sourceNext then .same
  else
    match mode with
    | .same => .same
    | .ordered a b =>
        if request = a then .credited sourceEvict b else .ordered a b
    | .credited a b =>
        if request = a then .credited sourceEvict b else .credited a b

/-- State of the transformed execution at one request boundary. -/
structure CouplingState where
  cache : Finset Page
  evict : Page
  mode : CouplingMode

/--
The transformed suffix at relative boundary `n`; absolute request positions
are `start + n`.
-/
def couplingCore (source : LegalTrace C₀ σ) (start : ℕ)
    (initialCache : Finset Page) (initialMode : CouplingMode) :
    ℕ → CouplingState
  | 0 =>
      let sourceCache := source.cache start
      let request := σ.getD start 0
      let evict := coupledEvict initialMode initialCache sourceCache
        (source.evict start) request
      ⟨initialCache, evict, initialMode⟩
  | n + 1 =>
      let previous := couplingCore source start initialCache initialMode n
      let absolute := start + n
      let request := σ.getD absolute 0
      let transformedNext := traceStepCache previous.cache previous.evict request
      let sourceNext := source.cache (absolute + 1)
      let modeNext := nextCouplingMode previous.mode request (source.evict absolute)
        transformedNext sourceNext
      let nextAbsolute := absolute + 1
      let nextRequest := σ.getD nextAbsolute 0
      let nextEvict := coupledEvict modeNext transformedNext sourceNext
        (source.evict nextAbsolute) nextRequest
      ⟨transformedNext, nextEvict, modeNext⟩

@[simp] lemma couplingCore_zero (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) :
    (couplingCore source start A mode 0).cache = A := by
  rfl

/-- Cache states of the full trace splice: source prefix, transformed suffix. -/
def coupledCache (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (s : ℕ) : Finset Page :=
  if s < start then source.cache s
  else (couplingCore source start A mode (s - start)).cache

/--
Evictions of the full trace splice.  The replacement boundary decision is at
`start - 1`; core decisions begin at `start`.
-/
def coupledTraceEvict (source : LegalTrace C₀ σ) (start : ℕ)
    (boundaryEvict : Page) (A : Finset Page) (mode : CouplingMode)
    (s : ℕ) : Page :=
  if s + 1 < start then source.evict s
  else if s + 1 = start then boundaryEvict
  else (couplingCore source start A mode (s - start)).evict

@[simp] lemma coupledCache_of_lt (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) (s : ℕ) (hs : s < start) :
    coupledCache source start A mode s = source.cache s := by
  simp [coupledCache, hs]

@[simp] lemma coupledCache_start (source : LegalTrace C₀ σ) (start : ℕ)
    (A : Finset Page) (mode : CouplingMode) :
    coupledCache source start A mode start = A := by
  simp [coupledCache]

end Caching

end CLRS
