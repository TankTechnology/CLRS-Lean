import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Optimality.Trace.A4_CouplingCorrect

/-!
# Section 15.4 optimality: one-step FIF exchange

At the first transition where a legal trace differs from farthest-in-future,
replace that eviction and couple the remaining suffix without increasing
misses.
-/

namespace CLRS

open Finset

namespace Caching

/-- Agreement of cache boundaries with farthest-in-future through `n`. -/
def TraceAgreesWithFIF (T : LegalTrace C₀ σ) (n : ℕ) : Prop :=
  ∀ s, s ≤ n → T.cache s = cacheSeq (fifoPolicy σ) C₀ σ s

/-- One local exchange extends FIF agreement by one boundary without more misses. -/
theorem exchange_trace
    (T : LegalTrace C₀ σ) (t : ℕ) (ht : t < σ.length)
    (hagree : TraceAgreesWithFIF T t)
    (hdis : T.cache (t + 1) ≠ cacheSeq (fifoPolicy σ) C₀ σ (t + 1)) :
    ∃ T' : LegalTrace C₀ σ,
      TraceAgreesWithFIF T' (t + 1) ∧
      traceMisses T' ≤ traceMisses T := by
  have hpre : T.cache t = cacheSeq (fifoPolicy σ) C₀ σ t := hagree t (by omega)
  have hmiss : σ.getD t 0 ∉ T.cache t := by
    intro hmem
    have hTnext := T.cache_succ_of_mem t ht hmem
    have hFmem : σ.getD t 0 ∈ cacheSeq (fifoPolicy σ) C₀ σ t := by
      rw [← hpre]
      exact hmem
    have hFnext : cacheSeq (fifoPolicy σ) C₀ σ (t + 1) =
        cacheSeq (fifoPolicy σ) C₀ σ t := by
      change (fifoPolicy σ).step t (cacheSeq (fifoPolicy σ) C₀ σ t)
          (σ.getD t 0) = cacheSeq (fifoPolicy σ) C₀ σ t
      exact fifo_step_of_mem σ t _ _ hFmem
    apply hdis
    calc
      T.cache (t + 1) = T.cache t := hTnext
      _ = cacheSeq (fifoPolicy σ) C₀ σ t := hpre
      _ = cacheSeq (fifoPolicy σ) C₀ σ (t + 1) := hFnext.symm

  let q : Page := T.evict t
  let p : Page := farthestInFuture (T.cache t) σ t
  have hq : q ∈ T.cache t := T.evict_mem t ht hmiss
  have hnonempty : (T.cache t).Nonempty := ⟨q, hq⟩
  have hp : p ∈ T.cache t := mem_farthestInFuture hnonempty
  have hTnext : T.cache (t + 1) =
      insert (σ.getD t 0) ((T.cache t).erase q) := by
    simpa [q] using T.cache_succ_of_not_mem t ht hmiss
  have hFnext : cacheSeq (fifoPolicy σ) C₀ σ (t + 1) =
      insert (σ.getD t 0) ((T.cache t).erase p) := by
    change (fifoPolicy σ).step t (cacheSeq (fifoPolicy σ) C₀ σ t)
        (σ.getD t 0) = _
    rw [← hpre]
    simpa [p] using fifo_step_fault σ t (T.cache t) (σ.getD t 0) hmiss
  have hqp : q ≠ p := by
    intro hqp
    apply hdis
    rw [hTnext, hFnext, hqp]
  have hdiff : OnePageDiff
      (cacheSeq (fifoPolicy σ) C₀ σ (t + 1)) (T.cache (t + 1)) q p := by
    rw [hFnext, hTnext]
    exact OnePageDiff.of_common_fault hmiss hp hq hqp
  have hfarther :
      Farther (nextUse σ (t + 1) p) (nextUse σ (t + 1) q) := by
    simpa [p] using farthestInFuture_max (σ := σ) (i := t) (p := q) hq
  have hsub : t + 1 - 1 = t := by omega
  have hboundaryMem :
      σ.getD (t + 1 - 1) 0 ∉ T.cache (t + 1 - 1) →
        p ∈ T.cache (t + 1 - 1) := by
    simpa [hsub] using fun _ : σ.getD t 0 ∉ T.cache t => hp
  have hboundaryStep :
      cacheSeq (fifoPolicy σ) C₀ σ (t + 1) =
        traceStepCache (T.cache (t + 1 - 1)) p (σ.getD (t + 1 - 1) 0) := by
    rw [hsub, hFnext]
    unfold traceStepCache
    split
    · contradiction
    · rfl
  rcases exists_coupled_suffix T (t + 1) (by omega) (by omega)
      (cacheSeq (fifoPolicy σ) C₀ σ (t + 1)) p q p
      hboundaryMem hboundaryStep hdiff hfarther with
    ⟨T', hprefix, hstartCache, hmisses⟩
  refine ⟨T', ?_, hmisses⟩
  intro s hs
  by_cases hsend : s = t + 1
  · subst s
    exact hstartCache
  · have hslt : s < t + 1 := by omega
    calc
      T'.cache s = T.cache s := hprefix s hslt
      _ = cacheSeq (fifoPolicy σ) C₀ σ s := hagree s (by omega)

end Caching

end CLRS
