import CLRSLean.Chapter_30.Section_30_2_DFT_And_FFT.RecursiveFFT.Definitions
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Chapter 30.3: Bit-reversal permutation

The executable copy and its index equivalence expose the bit-reversal step of
the iterative radix-2 FFT without introducing partial array indexing.
-/

namespace CLRS
namespace Chapter30

private def powTwoSuccToQuotBit (k : Nat) :
    Fin (2 ^ (k + 1)) ≃ Fin (2 ^ k) × Fin 2 :=
  (finCongr (by simp [pow_succ])).trans
    (finProdFinEquiv (m := 2 ^ k) (n := 2)).symm

private def bitRestToPowTwoSucc (k : Nat) :
    Fin 2 × Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
  (finProdFinEquiv (m := 2) (n := 2 ^ k)).trans
    (finCongr (by simp [pow_succ, Nat.mul_comm]))

/-- Reverse the declared low bits of a power-of-two index. -/
def bitReverseEquiv : (k : Nat) → Fin (2 ^ k) ≃ Fin (2 ^ k)
  | 0 => Equiv.refl _
  | k + 1 =>
      (powTwoSuccToQuotBit k).trans
        (((bitReverseEquiv k).prodCongr (Equiv.refl (Fin 2))).trans
          ((Equiv.prodComm (Fin (2 ^ k)) (Fin 2)).trans
            (bitRestToPowTwoSucc k)))

@[simp] theorem bitReverseEquiv_even {k : Nat} (i : Fin (2 ^ k)) :
    bitReverseEquiv (k + 1) (evenIndex i) =
      lowerHalfIndex (bitReverseEquiv k i) := by
  apply Fin.ext
  simp [bitReverseEquiv, powTwoSuccToQuotBit, bitRestToPowTwoSucc,
    evenIndex, lowerHalfIndex, powTwoSuccEquiv, Fin.divNat, Fin.modNat]

@[simp] theorem bitReverseEquiv_odd {k : Nat} (i : Fin (2 ^ k)) :
    bitReverseEquiv (k + 1) (oddIndex i) =
      upperHalfIndex (bitReverseEquiv k i) := by
  have hdiv : (2 * i.1 + 1) / 2 = i.1 := by omega
  apply Fin.ext
  simp [bitReverseEquiv, powTwoSuccToQuotBit, bitRestToPowTwoSucc,
    oddIndex, upperHalfIndex, powTwoSuccEquiv, Fin.divNat, Fin.modNat, hdiv]

/-- Reversal mirrors every bit position inside the declared fixed width. -/
theorem bitReverseEquiv_testBit {k : Nat} (i : Fin (2 ^ k))
    (j : Nat) (hj : j < k) :
    Nat.testBit (bitReverseEquiv k i).1 j =
      Nat.testBit i.1 (k - 1 - j) := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
      obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' i.1
      · have hq_lt : q < 2 ^ k := by
          have hi := i.2
          simp [pow_succ] at hi
          omega
        let qi : Fin (2 ^ k) := ⟨q, hq_lt⟩
        have hi : i = evenIndex qi := Fin.ext hq
        subst i
        by_cases htop : j = k
        · subst j
          rw [bitReverseEquiv_even]
          simp only [lowerHalfIndex_val, evenIndex_val]
          rw [show k + 1 - 1 - k = 0 by omega]
          rw [Nat.testBit_lt_two_pow (bitReverseEquiv k qi).2]
          simp [Nat.testBit_zero]
        · have hjk : j < k := by omega
          rw [bitReverseEquiv_even]
          simp only [lowerHalfIndex_val, evenIndex_val]
          rw [ih qi j hjk]
          rw [show k + 1 - 1 - j = (k - 1 - j) + 1 by omega]
          rw [Nat.testBit_add_one]
          congr 1
          omega
      · have hq_lt : q < 2 ^ k := by
          have hi := i.2
          simp [pow_succ] at hi
          omega
        let qi : Fin (2 ^ k) := ⟨q, hq_lt⟩
        have hi : i = oddIndex qi := Fin.ext hq
        subst i
        by_cases htop : j = k
        · subst j
          rw [bitReverseEquiv_odd]
          simp only [upperHalfIndex_val, oddIndex_val]
          rw [show k + 1 - 1 - k = 0 by omega]
          rw [Nat.testBit_two_pow_add_eq]
          rw [Nat.testBit_lt_two_pow (bitReverseEquiv k qi).2]
          simp [Nat.testBit_zero]
        · have hjk : j < k := by omega
          rw [bitReverseEquiv_odd]
          simp only [upperHalfIndex_val, oddIndex_val]
          rw [Nat.testBit_two_pow_add_gt hjk]
          rw [ih qi j hjk]
          rw [show k + 1 - 1 - j = (k - 1 - j) + 1 by omega]
          rw [Nat.testBit_add_one]
          congr 1
          omega

/-- Reversing the same fixed-width index twice is the identity. -/
theorem bitReverseEquiv_involutive (k : Nat) :
    Function.Involutive (bitReverseEquiv k) := by
  intro i
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < k
  · rw [bitReverseEquiv_testBit _ j hj]
    have hmirror : k - 1 - j < k := by omega
    rw [bitReverseEquiv_testBit _ _ hmirror]
    congr 1
    omega
  · have hkj : k ≤ j := Nat.le_of_not_gt hj
    have hpow : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hkj
    rw [Nat.testBit_lt_two_pow
      ((bitReverseEquiv k (bitReverseEquiv k i)).2.trans_le hpow)]
    rw [Nat.testBit_lt_two_pow (i.2.trans_le hpow)]

/-- Result and data-movement counter for bit-reversal copy. -/
structure BitReverseExecution (K : Type*) (k : Nat) where
  value : PowTwoVec K k
  moves : Nat

/-- Copy a vector into bit-reversed order by recursively grouping its even and
odd coefficients.  Every singleton leaf contributes one output move. -/
def bitReverseExec {K : Type*} :
    {k : Nat} → PowTwoVec K k → BitReverseExecution K k
  | 0, a => ⟨a, 1⟩
  | _k + 1, a =>
      let evenRun := bitReverseExec (evenCoeffs a)
      let oddRun := bitReverseExec (oddCoeffs a)
      ⟨joinHalves evenRun.value oddRun.value,
        evenRun.moves + oddRun.moves⟩

/-- Value projection of the bit-reversal execution. -/
def bitReverseCopy {K : Type*} {k : Nat} (a : PowTwoVec K k) :
    PowTwoVec K k :=
  (bitReverseExec a).value

@[simp] theorem bitReverseCopy_succ {K : Type*} {k : Nat}
    (a : PowTwoVec K (k + 1)) :
    bitReverseCopy a =
      joinHalves (bitReverseCopy (evenCoeffs a))
        (bitReverseCopy (oddCoeffs a)) := rfl

/-- The copied value at a reversed index is the original value. -/
theorem bitReverseCopy_apply {K : Type*} {k : Nat}
    (a : PowTwoVec K k) (i : Fin (2 ^ k)) :
    bitReverseCopy a (bitReverseEquiv k i) = a i := by
  induction k with
  | zero =>
      have hi : i = ⟨0, by norm_num⟩ := Fin.ext (by omega)
      subst i
      rfl
  | succ k ih =>
      obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' i.1
      · have hq_lt : q < 2 ^ k := by
          have hi := i.2
          simp [pow_succ] at hi
          omega
        let qi : Fin (2 ^ k) := ⟨q, hq_lt⟩
        have hi : i = evenIndex qi := Fin.ext hq
        subst i
        rw [bitReverseEquiv_even, bitReverseCopy_succ, joinHalves_lower]
        simpa using ih (evenCoeffs a) qi
      · have hq_lt : q < 2 ^ k := by
          have hi := i.2
          simp [pow_succ] at hi
          omega
        let qi : Fin (2 ^ k) := ⟨q, hq_lt⟩
        have hi : i = oddIndex qi := Fin.ext hq
        subst i
        rw [bitReverseEquiv_odd, bitReverseCopy_succ, joinHalves_upper]
        simpa using ih (oddCoeffs a) qi

/-- Applying bit-reversal copy twice returns the original vector. -/
theorem bitReverseCopy_involutive {K : Type*} {k : Nat} :
    Function.Involutive (@bitReverseCopy K k) := by
  intro a
  funext i
  have hsem := bitReverseCopy_apply (bitReverseCopy a) (bitReverseEquiv k i)
  rw [bitReverseEquiv_involutive k i] at hsem
  exact hsem.trans (bitReverseCopy_apply a i)

/-- Bit-reversal performs exactly one functional output move per element. -/
@[simp] theorem bitReverseExec_moves {K : Type*} {k : Nat}
    (a : PowTwoVec K k) :
    (bitReverseExec a).moves = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [bitReverseExec, ih, pow_succ]
      omega

end Chapter30
end CLRS
