import CLRSLean.FourthEdition.Chapter_31.Section_31_8_Primality_Testing

/-!
# Miller–Rabin with counted residue execution

The single-base decision inspects the residue returned by counted modular
exponentiation and the residues of subsequent counted modular squares. The
multi-base loop stops at the first rejection and never evaluates its suffix.
The counter measures modular multiplications, including the initial exponentiation;
it is not bit complexity or total runtime. Parameter decomposition, comparisons,
and supplied-base construction/sampling are outside this counter. In particular,
this module does not charge the implementation of {lit}`strongTestParams`.
The probability companion specifies independent uniform input samples separately.
The kernel preserves the existing strong-probable-prime predicate on all naturals;
its primality interpretation uses the existing admissible-input hypotheses.
-/

namespace CLRS.Chapter31.MillerRabinExecution

/-- Inspect the current residue, then at most {lit}`fuel` further modular squares. -/
def squareSearch (n target : Nat) : Nat → Nat → Bool × Nat
  | 0, x => (decide (x % n = target % n), 0)
  | k + 1, x =>
    if x % n = target % n then (true, 0)
    else
      let next := squareSearch n target k ((x * x) % n)
      (next.1, next.2 + 1)

private theorem square_pow (x n i : Nat) :
    (((x * x) % n) ^ (2 ^ i)) % n = (x ^ (2 ^ (i + 1))) % n := by
  rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod]
  rw [← pow_two, ← pow_mul]
  congr 2
  rw [pow_succ]
  omega

theorem squareSearch_spec (n target fuel x : Nat) :
    (squareSearch n target fuel x).1 = true ↔
      ∃ i ≤ fuel, x ^ (2 ^ i) % n = target % n := by
  induction fuel generalizing x with
  | zero => simp [squareSearch]
  | succ k ih =>
    by_cases hx : x % n = target % n
    · simp only [squareSearch, hx, if_true]
      exact ⟨fun _ => ⟨0, by omega, by simpa using hx⟩, fun _ => trivial⟩
    · simp only [squareSearch, hx, if_false, ih]
      constructor
      · rintro ⟨i, hi, he⟩
        exact ⟨i + 1, by omega, by simpa only [square_pow] using he⟩
      · rintro ⟨i, hi, he⟩
        cases i with
        | zero => simp [hx] at he
        | succ i => exact ⟨i, by omega, by simpa only [square_pow] using he⟩

theorem squareSearch_count_le (n target fuel x : Nat) :
    (squareSearch n target fuel x).2 ≤ fuel := by
  induction fuel generalizing x with
  | zero => simp [squareSearch]
  | succ k ih =>
    simp only [squareSearch]
    split
    · simp
    · exact Nat.add_le_add_right (ih _) 1

/-- Rejection exhausts exactly the allowed squarings; successful scans may stop earlier. -/
theorem squareSearch_reject_count (n target fuel x : Nat)
    (h : (squareSearch n target fuel x).1 = false) :
    (squareSearch n target fuel x).2 = fuel := by
  induction fuel generalizing x with
  | zero => rfl
  | succ k ih =>
    by_cases hx : x % n = target % n
    · simp [squareSearch, hx] at h
    · simp only [squareSearch, hx, if_false] at h ⊢
      rw [ih _ h]

/-- The result and count come from the same exponentiation and residue scan. -/
def trial (n a : Nat) : Bool × Nat :=
  let params := strongTestParams n
  let initial := modExpWithCount a n params.2
  if initial.1 = 1 % n then (true, initial.2)
  else
    match params.1 with
    | 0 => (false, initial.2)
    | s + 1 =>
      let scanned := squareSearch n (n - 1) s initial.1
      (scanned.1, initial.2 + scanned.2)

private theorem initial_pow (a n d i : Nat) :
    ((a ^ d % n) ^ (2 ^ i)) % n = a ^ (2 ^ i * d) % n := by
  rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← pow_mul, Nat.mul_comm d]

theorem trial_spec (n a : Nat) :
    (trial n a).1 = true ↔ strongPseudoprime n a := by
  unfold strongPseudoprime
  simp only [trial, modExpWithCount_spec]
  split
  · rename_i he
    constructor
    · intro _; exact Or.inl he
    · intro _; rfl
  · rename_i he
    cases hs : (strongTestParams n).1 with
    | zero => simp [Nat.ModEq, he]
    | succ s =>
      simp only [squareSearch_spec, initial_pow, Nat.ModEq]
      constructor
      · rintro ⟨i, hi, h⟩
        exact Or.inr ⟨⟨i, by omega⟩, h⟩
      · rintro (h | ⟨i, hi⟩)
        · exact (he h).elim
        · exact ⟨i.val, by omega, hi⟩

theorem trial_eq_millerRabin (n a : Nat) : (trial n a).1 = millerRabin n a := by
  apply Bool.eq_iff_iff.mpr
  simp [trial_spec, millerRabin]

theorem trial_prime {n a : Nat} (hn : Nat.Prime n) (hcop : Nat.Coprime a n) :
    (trial n a).1 = true := (trial_spec n a).mpr (strongPseudoprime_of_prime hn hcop)

theorem trial_count_le (n a : Nat) :
    (trial n a).2 ≤ 2 * Nat.size (strongTestParams n).2 + (strongTestParams n).1 := by
  have hc := modExpWithCount_count_le a n (strongTestParams n).2
  simp only [trial]
  split
  · omega
  · cases hs : (strongTestParams n).1 with
    | zero => simp only; omega
    | succ s =>
      have hsq := squareSearch_count_le n (n - 1) s (modExpWithCount a n (strongTestParams n).2).1
      simp only
      omega

theorem trial_count_le_size (n a : Nat) :
    (trial n a).2 ≤ 3 * Nat.size (n - 1) := by
  have hc := trial_count_le n a
  have hd : Nat.size (strongTestParams n).2 ≤ Nat.size (n - 1) :=
    Nat.size_le_size (Nat.div_le_self _ _)
  have hs : (strongTestParams n).1 ≤ Nat.size (n - 1) :=
    Nat.factorization_le_of_le_pow (Nat.size_le.mp (Nat.le_refl (Nat.size (n - 1)))).le
  omega

/-- Supplied bases are processed left to right, stopping before the suffix on rejection. -/
def run (n : Nat) : List Nat → Bool × Nat
  | [] => (true, 0)
  | a :: bases =>
    let tested := trial n a
    if tested.1 then
      let rest := run n bases
      (rest.1, tested.2 + rest.2)
    else (false, tested.2)

theorem run_spec (n : Nat) (bases : List Nat) :
    (run n bases).1 = true ↔ ∀ a ∈ bases, strongPseudoprime n a := by
  induction bases with
  | nil => simp [run]
  | cons a bases ih =>
    simp only [run]
    cases ht : (trial n a).1 with
    | false =>
      have hn : ¬ strongPseudoprime n a := by
        intro h; have := (trial_spec n a).mpr h; simp [ht] at this
      simp [hn]
    | true => simp [ih, (trial_spec n a).mp ht]

theorem run_reject (n a : Nat) (bases : List Nat) (h : (trial n a).1 = false) :
    run n (a :: bases) = (false, (trial n a).2) := by simp [run, h]

theorem run_count_le (n : Nat) (bases : List Nat) :
    (run n bases).2 ≤ bases.length * (3 * Nat.size (n - 1)) := by
  induction bases with
  | nil => simp [run]
  | cons a bases ih =>
    have ht := trial_count_le_size n a
    simp only [run]
    split
    · simp only [List.length_cons]; nlinarith
    · simp only [List.length_cons]; nlinarith

theorem run_eq_legacy_value (n : Nat) (bases : List Nat) :
    (run n bases).1 = (millerRabinLoop n bases).1 := by
  apply Bool.eq_iff_iff.mpr
  rw [run_spec, millerRabinLoop_fst_iff]
  simp [millerRabin]

end CLRS.Chapter31.MillerRabinExecution
