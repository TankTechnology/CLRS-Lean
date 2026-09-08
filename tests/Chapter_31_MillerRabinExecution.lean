import CLRSLean.FourthEdition.Chapter_31.Section_31_8_Primality_Testing.Probability
import CLRSLean.Audit.Axioms

open CLRS.Chapter31
open MillerRabinExecution

#check trial
#check trial_spec
#check trial_count_le_size
#check run_reject
#check run_count_le
#check accepted_card
#check uniform_error_le

namespace MillerRabinExecutionTests

private theorem factor_two (m k : Nat) (hm : m ≠ 0)
    (hd : 2 ^ k ∣ m) (hn : ¬ 2 ^ (k + 1) ∣ m) : m.factorization 2 = k := by
  have hl : k ≤ m.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hm).mp hd
  apply Nat.le_antisymm _ hl
  by_contra h
  exact hn ((Nat.Prime.pow_dvd_iff_le_factorization (by decide : Nat.Prime 2) hm).mpr (by omega))

private theorem params9 : strongTestParams 9 = (3, 1) := by
  have h : (Nat.factorization 8) 2 = 3 := by apply factor_two <;> norm_num
  norm_num [strongTestParams, h]

-- The decision uses the same running residues whose squares are counted.
example : squareSearch 17 16 3 3 = (true, 3) := by decide
example : squareSearch 9 8 2 2 = (false, 2) := by decide
example : squareSearch 17 16 0 16 = (true, 0) := by decide
example : squareSearch 17 16 0 3 = (false, 0) := by decide
#guard trial 17 3 == (true, 5)
#guard trial 21 2 == (false, 6)
-- A real strong liar: a passing base is not a primality certificate.
example : ¬ Nat.Prime 2047 := by norm_num
#guard trial 2047 2 == (true, 20)

-- The first rejection prevents the remaining tests and their multiplication charges.
#guard run 21 [2, 3, 5] == (false, 6)
#guard run 17 [2, 3, 5] == (true, 14)
example (n a : Nat) (suffix : List Nat) (h : (trial n a).1 = false) :
    run n (a :: suffix) = (false, (trial n a).2) := run_reject n a suffix h
example (n : Nat) : run n [] = (true, 0) := rfl
example (n : Nat) : uniformError n 0 = 1 := uniformError_zero n

-- Exactly two of the eight nonzero bases for 9 are strong liars.
private theorem nine_liars : Nat.card (Liars 9) = 2 := by
  let e : Liars 9 ≃ {a : Fin 8 // a.val = 0 ∨ a.val = 7} :=
    Equiv.subtypeEquivRight (fun a => by
      unfold strongPseudoprime
      rw [params9]
      fin_cases a <;> norm_num [Nat.ModEq, Fin.exists_fin_succ])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

example : Nat.card (Samples 9 2) = 64 := by rw [samples_card]; norm_num
example : Nat.card (Accepted 9 2) = 4 := by rw [accepted_card, nine_liars]; norm_num
example : uniformError 9 2 = (1 / 16 : ℚ) := by
  rw [uniformError_eq, nine_liars]
  norm_num

example (rounds : Nat) : uniformError 9 rounds ≤ (1 / 4 : ℚ) ^ rounds :=
  uniform_error_le (by decide) (by decide) (by decide) rounds

-- The full product samples independent bases with replacement, not only distinct bases or units.
example : sampleBases (n := 9) (fun _ : Fin 2 => (0 : Fin 8)) = [1, 1] := by decide
#guard (run 9 (sampleBases (n := 9) (fun _ : Fin 2 => (0 : Fin 8)))).1

example (n : Nat) (bases : List Nat) : (run n bases).1 = (millerRabinLoop n bases).1 :=
  run_eq_legacy_value n bases

#assert_axioms trial_spec
#assert_axioms trial_prime
#assert_axioms squareSearch_reject_count
#assert_axioms run_spec
#assert_axioms run_count_le
#assert_axioms run_eq_legacy_value
#assert_axioms accepted_card
#assert_axioms uniform_error_le

end MillerRabinExecutionTests
