import CLRSLean.FourthEdition.Chapter_15.Section_15_4_Offline_Caching.Optimality.Trace.A5_Exchange

/-!
# Section 15.4 optimality: finite exchange iteration

Repeatedly extend agreement by one request boundary.  The remaining number of
boundaries is the sole termination measure.
-/

namespace CLRS

open Finset
open scoped BigOperators

namespace Caching

/-- Full cache-boundary agreement with FIF gives exactly the FIF miss count. -/
lemma traceMisses_eq_fifo_of_agree
    (T : LegalTrace C₀ σ)
    (hagree : TraceAgreesWithFIF T σ.length) :
    traceMisses T = misses (fifoPolicy σ) C₀ σ := by
  unfold traceMisses misses traceFaultAt faultAt
  apply Finset.sum_congr rfl
  intro t ht
  rw [hagree t (by
    have := Finset.mem_range.mp ht
    omega)]

/-- Complete FIF agreement when `k` request boundaries remain. -/
lemma exists_fully_agreeing_trace_aux
    (k n : ℕ) (hkn : n + k = σ.length)
    (T : LegalTrace C₀ σ) (hagree : TraceAgreesWithFIF T n) :
    ∃ T' : LegalTrace C₀ σ,
      TraceAgreesWithFIF T' σ.length ∧
      traceMisses T' ≤ traceMisses T := by
  induction k generalizing n T with
  | zero =>
      have hn : n = σ.length := by omega
      refine ⟨T, ?_, le_rfl⟩
      simpa [hn] using hagree
  | succ k ih =>
      have hnlt : n < σ.length := by omega
      by_cases hnext :
          T.cache (n + 1) = cacheSeq (fifoPolicy σ) C₀ σ (n + 1)
      · have hagreeNext : TraceAgreesWithFIF T (n + 1) := by
          intro s hs
          by_cases hsn : s = n + 1
          · subst s
            exact hnext
          · exact hagree s (by omega)
        exact ih (n + 1) (by omega) T hagreeNext
      · rcases exchange_trace T n hnlt hagree hnext with
          ⟨T₁, hagree₁, hmiss₁⟩
        rcases ih (n + 1) (by omega) T₁ hagree₁ with
          ⟨T₂, hagree₂, hmiss₂⟩
        exact ⟨T₂, hagree₂, Nat.le_trans hmiss₂ hmiss₁⟩

/-- Every legal trace can be exchanged into a fully FIF-agreeing trace. -/
theorem exists_fully_agreeing_trace (T : LegalTrace C₀ σ) :
    ∃ T' : LegalTrace C₀ σ,
      TraceAgreesWithFIF T' σ.length ∧
      traceMisses T' ≤ traceMisses T := by
  have hagreeZero : TraceAgreesWithFIF T 0 := by
    intro s hs
    have hs0 : s = 0 := by omega
    subst s
    change T.cache 0 = C₀
    exact T.init
  exact exists_fully_agreeing_trace_aux σ.length 0 (by simp) T hagreeZero

/-- Development theorem: farthest-in-future is optimal among all policies. -/
theorem fifo_optimal_trace
    (π : Policy) (C₀ : Finset Page) (σ : List Page)
    (hC₀ : C₀.Nonempty) :
    misses (fifoPolicy σ) C₀ σ ≤ misses π C₀ σ := by
  rcases exists_fully_agreeing_trace (policyTrace π C₀ σ hC₀) with
    ⟨T, hagree, hmisses⟩
  calc
    misses (fifoPolicy σ) C₀ σ = traceMisses T :=
      (traceMisses_eq_fifo_of_agree T hagree).symm
    _ ≤ traceMisses (policyTrace π C₀ σ hC₀) := hmisses
    _ = misses π C₀ σ := traceMisses_policyTrace π C₀ σ hC₀

end Caching

end CLRS
