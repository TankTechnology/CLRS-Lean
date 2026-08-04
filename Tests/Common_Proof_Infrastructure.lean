import CLRSLean.Probability.FiniteExpectation
import CLRSLean.Chapter_04.Section_04_6_Master_Theorem_All_Input
import CLRSLean.Chapter_05.Section_05_4_Probabilistic_Analysis
import CLRSLean.Chapter_08.Section_08_2_Counting_Sort
import CLRSLean.Chapter_11.Section_11_5_Perfect_Hashing
import CLRSLean.Chapter_22.Section_22_3_DFS.S2_Intervals
import CLRSLean.Chapter_27.Section_27_2_4_Algorithms

/-!
# Common proof infrastructure interface

This test fixes the intended ownership and compatibility surface for proof
principles shared across chapters.  Representation bridges and compatibility
wrappers are public API, but they do not represent additional textbook theorem
groups.
-/

#check CLRS.Probability.fintypeExpect_mono
#check CLRS.Probability.fintypeExpect_neg
#check CLRS.Chapter04.monotoneAbs_natCast
#check CLRS.Chapter04.monotone_power_sandwich
#check CLRS.Chapter08.bucket_eq_fiber
#check CLRS.Chapter22.Graph.dfsInterval
#check CLRS.Chapter22.Graph.finishesBeforeDiscovered_iff_strictlyBefore
#check CLRS.Chapter22.Graph.intervalNestedInside_iff_nestedInside
#check CLRS.Chapter22.Graph.intervalNestedInside_asymm

-- Established chapter-facing names remain available with their original types.
#check CLRS.Chapter05.fintypeExpect_mono
#check CLRS.Chapter11.fintypeExpect_mono
#check CLRS.Chapter11.fintypeExpect_neg

namespace CLRS

example {Ω : Type} [Fintype Ω] [DecidableEq Ω] {X Y : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hY : ∀ ω, 0 ≤ Y ω) (hXY : ∀ ω, X ω ≤ Y ω) :
    Probability.fintypeExpect X ≤ Probability.fintypeExpect Y :=
  Chapter05.fintypeExpect_mono hX hY hXY

example (n : ℕ) (hn : 0 < n) :
    Chapter27.pMergeWork (2 ^ Nat.log 2 n) ≤ Chapter27.pMergeWork n ∧
      Chapter27.pMergeWork n ≤ Chapter27.pMergeWork (2 ^ (Nat.log 2 n + 1)) :=
  Chapter04.monotone_power_sandwich Chapter27.pMergeWork_monotone 2 n
    (by omega) hn.ne'

example {α : Type} (key : α → Nat) (xs : List α) (k : Nat) :
    Chapter08.bucket key xs k = ProofPatterns.fiber key xs k :=
  Chapter08.bucket_eq_fiber key xs k

namespace Chapter22.Graph

variable {V : Type} [DecidableEq V]

example {s : DFSState V} {u v : V} (h : intervalNestedInside s u v) :
    ¬ intervalNestedInside s v u :=
  intervalNestedInside_asymm h

end Chapter22.Graph
end CLRS
