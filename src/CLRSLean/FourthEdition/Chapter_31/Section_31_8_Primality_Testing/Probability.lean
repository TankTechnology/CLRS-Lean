import CLRSLean.FourthEdition.Chapter_31.Section_31_8_Primality_Testing.Execution

/-!
# Independent uniform Miller–Rabin trials

The sample space is the full finite product of nonzero natural residues, with
replacement. Acceptance is defined by the counted execution, including its early
rejection behavior. A coordinatewise bijection counts accepting tuples exactly.
Uniform probability is the rational ratio of accepting samples to all samples;
the one-base strong-liar theorem then gives the repeated-trial error bound.
This is a finite probability model, not an implementation of random sampling.
-/

namespace CLRS.Chapter31.MillerRabinExecution

/-- The full product space: each coordinate is a uniform base in 1,...,n-1. -/
abbrev Samples (n rounds : Nat) := Fin rounds → Fin (n - 1)

def sampleBases (ω : Samples n rounds) : List Nat := List.ofFn (fun i => (ω i).val + 1)

/-- Acceptance is the Boolean returned by the counted, short-circuiting execution. -/
abbrev Accepted (n rounds : Nat) := {ω : Samples n rounds // (run n (sampleBases ω)).1 = true}

abbrev Liars (n : Nat) := {a : Fin (n - 1) // strongPseudoprime n (a.val + 1)}

theorem sample_accept_iff (ω : Samples n rounds) :
    (run n (sampleBases ω)).1 = true ↔ ∀ i, strongPseudoprime n ((ω i).val + 1) := by
  simp [run_spec, sampleBases]

/-- Coordinatewise restriction is a bijection, so no independence premise is supplied by callers. -/
def acceptedEquiv (n rounds : Nat) : Accepted n rounds ≃ (Fin rounds → Liars n) where
  toFun ω i := ⟨ω.val i, (sample_accept_iff ω.val).mp ω.property i⟩
  invFun f := ⟨fun i => (f i).val, (sample_accept_iff _).mpr (fun i => (f i).property)⟩
  left_inv ω := by rfl
  right_inv f := by rfl

theorem accepted_card (n rounds : Nat) :
    Nat.card (Accepted n rounds) = Nat.card (Liars n) ^ rounds := by
  rw [Nat.card_congr (acceptedEquiv n rounds), Nat.card_fun]
  simp

theorem samples_card (n rounds : Nat) : Nat.card (Samples n rounds) = (n - 1) ^ rounds := by
  simp [Samples]

/-- Uniform probability on the explicitly finite product space, expressed as a rational count ratio.
No random generator, entropy source, or sampling-operation runtime is asserted. -/
noncomputable def uniformError (n rounds : Nat) : ℚ :=
  (Nat.card (Accepted n rounds) : ℚ) / Nat.card (Samples n rounds)

theorem uniformError_eq (n rounds : Nat) :
    uniformError n rounds = ((Nat.card (Liars n) : ℚ) / (n - 1 : Nat)) ^ rounds := by
  rw [uniformError, accepted_card, samples_card]
  push_cast
  rw [div_pow]

/-- Actual executed false acceptance under independent uniform bases is at most 4^-rounds. -/
theorem uniform_error_le {n : Nat} (hn : 1 < n) (hodd : Odd n) (hcomp : ¬ Nat.Prime n)
    (rounds : Nat) : uniformError n rounds ≤ (1 / 4 : ℚ) ^ rounds := by
  letI : NeZero n := ⟨by omega⟩
  have hc := strongLiars_nat_card_le hn hodd hcomp
  have hprod : Nat.card (Liars n) * 4 ≤ n - 1 :=
    (Nat.mul_le_mul_right 4 hc).trans (Nat.div_mul_le_self (n - 1) 4)
  have hnpos : (0 : ℚ) < (n - 1 : Nat) := by exact_mod_cast (show 0 < n - 1 by omega)
  have hratio : (Nat.card (Liars n) : ℚ) / (n - 1 : Nat) ≤ 1 / 4 := by
    apply (div_le_div_iff₀ hnpos (by norm_num)).mpr
    simp only [one_mul]
    exact_mod_cast hprod
  rw [uniformError_eq]
  exact pow_le_pow_left₀ (by positivity) hratio rounds

@[simp] theorem uniformError_zero (n : Nat) : uniformError n 0 = 1 := by
  simp [uniformError_eq]

end CLRS.Chapter31.MillerRabinExecution
