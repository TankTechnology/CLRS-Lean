import CLRSLean.Chapter_30.Section_30_3_Efficient_FFT_Implementations.IterativeFFT.Definitions
import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Correctness
import Mathlib.Tactic

/-! # Chapter 30.3: Iterative FFT correctness

The ordered stage prefix factors over the two contiguous halves until the final
stage.  That invariant gives the recursive FFT equation and transfers the
proved recursive transform to the generic DFT.
-/

namespace CLRS
namespace Chapter30

theorem fftStage_join_castSucc [Ring K] {k : Nat} (omega : K)
    (lower upper : PowTwoVec K k) (s : Fin k) :
    fftStage omega (joinHalves lower upper) s.castSucc =
      joinHalves (fftStage (omega ^ 2) lower s)
        (fftStage (omega ^ 2) upper s) := by
  rw [fftStage_nonfinal]
  simp

/-- Every requested nonfinal stage prefix acts independently on the two halves. -/
theorem runFFTStagePrefix_join [Ring K] {k m : Nat} (hm : m ≤ k)
    (omega : K) (lower upper : PowTwoVec K k) :
    runFFTStagePrefix omega (joinHalves lower upper) m
        (hm.trans (Nat.le_succ k)) =
      joinHalves
        (runFFTStagePrefix (omega ^ 2) lower m hm)
        (runFFTStagePrefix (omega ^ 2) upper m hm) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [runFFTStagePrefix_succ, runFFTStagePrefix_succ,
        runFFTStagePrefix_succ]
      rw [ih (by omega)]
      exact fftStage_join_castSucc omega _ _ ⟨m, by omega⟩

/-- Specialization of the stage invariant to all child-size stages. -/
theorem runInitialFFTStages_join [Ring K] {k : Nat} (omega : K)
    (lower upper : PowTwoVec K k) :
    runFFTStagePrefix omega (joinHalves lower upper) k (Nat.le_succ k) =
      joinHalves
        (runAllFFTStages (omega ^ 2) lower)
        (runAllFFTStages (omega ^ 2) upper) := by
  simpa [runAllFFTStages, runAllFFTStagesExec, runFFTStagePrefix] using
    runFFTStagePrefix_join (m := k) le_rfl omega lower upper

/-- The iterative transform exposes the same even/odd recurrence as the
recursive radix-2 FFT. -/
theorem iterativeRadix2FFT_succ [Ring K] {k : Nat} (omega : K)
    (a : PowTwoVec K (k + 1)) :
    iterativeRadix2FFT omega a =
      butterflyLayer omega
        (iterativeRadix2FFT (omega ^ 2) (evenCoeffs a))
        (iterativeRadix2FFT (omega ^ 2) (oddCoeffs a)) := by
  rw [iterativeRadix2FFT_eq_runAll, runAllFFTStages_succ,
    bitReverseCopy_succ, runInitialFFTStages_join, fftStage_final]
  rw [iterativeRadix2FFT_eq_runAll, iterativeRadix2FFT_eq_runAll]
  simp

/-- The ordered iterative execution has the same value as the canonical
recursive radix-2 execution for every ring and every supplied root. -/
theorem iterativeRadix2FFT_eq_recursiveFFT [Ring K] {k : Nat}
    (omega : K) (a : PowTwoVec K k) :
    iterativeRadix2FFT omega a = recursiveFFT omega a := by
  induction k generalizing omega with
  | zero =>
      funext i
      have hi : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
      subst i
      rfl
  | succ k ih =>
      rw [iterativeRadix2FFT_succ]
      by_cases hk : k = 0
      · subst k
        simp [recursiveFFT, recursiveFFTExec, butterflyLayer,
          butterflyLayerExec]
      · have hchildRoot :
            twiddleChildRoot k omega
                (twiddlePowersAuxExec omega (2 ^ k) 1) = omega ^ 2 :=
          twiddleChildRoot_eq_square (Nat.pos_of_ne_zero hk) omega
        simp only [recursiveFFT, recursiveFFTExec]
        rw [hchildRoot]
        change butterflyLayer omega
            (iterativeRadix2FFT (omega ^ 2) (evenCoeffs a))
            (iterativeRadix2FFT (omega ^ 2) (oddCoeffs a)) =
          butterflyLayer omega
            (recursiveFFT (omega ^ 2) (evenCoeffs a))
            (recursiveFFT (omega ^ 2) (oddCoeffs a))
        rw [ih, ih]

/-- Under the existing primitive-root hypotheses, the iterative FFT computes
the generic DFT. -/
theorem iterativeRadix2FFT_eq_dft [Field K] [CharZero K] {k : Nat}
    {omega : K} (homega : IsPrimitiveRoot omega (2 ^ k))
    (a : PowTwoVec K k) :
    iterativeRadix2FFT omega a = dft omega a := by
  rw [iterativeRadix2FFT_eq_recursiveFFT]
  exact recursiveFFT_eq_dft homega a

end Chapter30
end CLRS
