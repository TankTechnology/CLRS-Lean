import Mathlib
import CLRSLean.FourthEdition.Chapter_32.Section_32_3_Finite_Automata

set_option maxHeartbeats 1000000

/-! # Section 32.4 — The Knuth–Morris–Pratt Algorithm

The Knuth–Morris–Pratt algorithm (CLRS §32.4) finds all occurrences of a
pattern `P` in a text `T` in time `O(|P| + |T|)` by precomputing a *prefix
function* `π` on the pattern, then scanning the text once, falling back along
`π` whenever a match attempt fails.

## Key definitions

- {lit}`prefixLen P q` — the prefix function `π[q]`: the longest proper prefix
  of `P` that is a suffix of `P.take q`.
- {lit}`computePrefixFunction P` — the executable `COMPUTE-PREFIX-FUNCTION`
  (failure-link recurrence), returning the prefix array.
- {lit}`kmpMatcher T P` — the all-occurrences KMP scan.

## Main results

- `prefixLen_satisfies` / `prefixLen_maximal` — `P.take (π q)` is the longest
  proper prefix of `P` that is a suffix of `P.take q`.
- `prefixLen_chain_step` — the CLRS Lemma 32.5 induction step: a shorter
  prefix-suffix of `P.take q` is a prefix-suffix of `P.take (π q)`.
- `computePrefixFunction` — the executable failure-link `COMPUTE-PREFIX-FUNCTION`.

## Current gaps

The executable prefix function and its spec are in place, but the following are
not yet formalized here (tracked in issue #198):

- `computePrefixFunction_correct` — each entry of the executable array equals
  `prefixLen` (CLRS Lemma 32.6 recurrence).
- The all-occurrences KMP scan and its `naiveMatcher` refinement.
- The `O(m + n)` costed construction and scan.

Notation conventions used in this section:

- `P` : the pattern
- `T` : the text
- `π` : the prefix function (written `prefixLen P`)
-/
namespace CLRS
namespace Chapter32

variable {α : Type} [BEq α] [DecidableEq α] [LawfulBEq α] [Inhabited α]

/-- Search for the largest `k ≤ n` such that `P.take k` is a suffix of `x`. -/
def prefixLenAux (P x : Text α) : ℕ → ℕ
  | 0 => 0
  | n + 1 => if suffixTest (P.take (n + 1)) x then n + 1 else prefixLenAux P x n

/-- The prefix function `π(q)`: the longest *proper* prefix of `P` that is a
suffix of `P.take q` (CLRS §32.4).  Bounded by `q - 1` so it is always proper. -/
def prefixLen (P : Text α) (q : ℕ) : ℕ :=
  prefixLenAux P (P.take q) (q - 1)

/-- `prefixLenAux` never exceeds its bound. -/
lemma prefixLenAux_le (P x : Text α) (n : ℕ) : prefixLenAux P x n ≤ n := by
  induction n with
  | zero => simp [prefixLenAux]
  | succ n ih =>
      by_cases h : suffixTest (P.take (n + 1)) x
      · simp [prefixLenAux, h]
      · simp [prefixLenAux, h]; omega

/-- The prefix function never exceeds its index. -/
theorem prefixLen_le (P : Text α) (q : ℕ) : prefixLen P q ≤ q := by
  unfold prefixLen
  exact le_trans (prefixLenAux_le P (P.take q) (q - 1)) (by omega)

/-- The prefix function is proper when its index is positive. -/
theorem prefixLen_lt_of_pos (P : Text α) (q : ℕ) (hq : 0 < q) : prefixLen P q < q := by
  unfold prefixLen
  have hle := prefixLenAux_le P (P.take q) (q - 1)
  omega

/-- `P.take (π q)` is a suffix of `P.take q`. -/
theorem prefixLen_satisfies (P : Text α) (q : ℕ) :
    isSuffix (P.take (prefixLen P q)) (P.take q) := by
  unfold prefixLen
  have hgo : ∀ n, prefixLenAux P (P.take q) n = 0 ∨
      suffixTest (P.take (prefixLenAux P (P.take q) n)) (P.take q) = true := by
    intro n
    induction n with
    | zero => left; simp [prefixLenAux]
    | succ n ih =>
        by_cases h : suffixTest (P.take (n + 1)) (P.take q)
        · right; simpa [prefixLenAux, h] using h
        · simpa [prefixLenAux, h] using ih
  rcases hgo (q - 1) with hzero | hsuf
  · rw [hzero]; exact isSuffix_empty _
  · exact (suffixTest_eq_isSuffix _ _).mp hsuf

/-- `π(q)` is maximal among proper prefixes of `P` that are suffixes of
`P.take q`. -/
theorem prefixLen_maximal (P : Text α) (q k : ℕ) (hk : k < q)
    (hsuf : isSuffix (P.take k) (P.take q)) : k ≤ prefixLen P q := by
  unfold prefixLen
  have ht : suffixTest (P.take k) (P.take q) = true := (suffixTest_eq_isSuffix _ _).mpr hsuf
  have hgo : ∀ n, k ≤ n → k ≤ prefixLenAux P (P.take q) n := by
    intro n hkn
    induction n with
    | zero => omega
    | succ n ih =>
        by_cases hts : suffixTest (P.take (n + 1)) (P.take q)
        · simp [prefixLenAux, hts]; omega
        · have hklt : k < n + 1 := by
            by_cases hk_eq : k = n + 1
            · subst k; simpa [hts] using ht
            · omega
          have := ih (by omega)
          simpa [prefixLenAux, hts] using this
  have hle : k ≤ q - 1 := by omega
  exact hgo (q - 1) hle

/-- Follow failure links from `k`: repeatedly replace `k` by `π[k-1]` while
`k > 0` and `P[k] ≠ c`, returning the first `k` (along the chain) with
`P[k] = c`, or `0`.  `hinv` guarantees every `π[i] < i + 1`, so the chain
strictly decreases. -/
def failureFollow (P : Text α) (π : List ℕ) (c : α) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) : ℕ :=
  if hk : k = 0 then 0
  else if (P.getD k default) = c then k
  else failureFollow P π c (π.getD (k - 1) 0) hinv
termination_by k
decreasing_by
  simp_wf
  have hpos : 0 < k := Nat.pos_of_ne_zero hk
  have hk' : (k - 1) + 1 = k := by omega
  simpa [hk'] using hinv (k - 1)

/-- `failureFollow` never increases its argument. -/
lemma failureFollow_le (P : Text α) (π : List ℕ) (c : α) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) : failureFollow P π c k hinv ≤ k := by
  rw [failureFollow.eq_1]
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]
    by_cases hc : P[k]?.getD default = c
    · simp [hc]
    · simp [hc]
      have ih := failureFollow_le P π c (π.getD (k - 1) 0) hinv
      have hlt : π.getD (k - 1) 0 < k := by
        have hpos : 0 < k := Nat.pos_of_ne_zero hk
        have h := hinv (k - 1)
        omega
      exact le_of_lt (lt_of_le_of_lt ih hlt)
termination_by k
decreasing_by
  simp_wf
  have hpos : 0 < k := Nat.pos_of_ne_zero hk
  have hk' : (k - 1) + 1 = k := by omega
  simpa [hk'] using hinv (k - 1)

/-- The executable `COMPUTE-PREFIX-FUNCTION` (CLRS §32.4).  `π` is the prefix
array computed so far (length `q`), `k = π[q-1]`, and `hinv` records that every
`π[i] < i + 1`; `hk_lt` records `k < π.length`. -/
def computePrefixGo (P : Text α) (π : List ℕ) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hk_lt : k < π.length) : Text α → List ℕ
  | [] => π
  | c :: rest =>
      let k' := failureFollow P π c k hinv
      let k'' := if (P.getD k' default) = c then k' + 1 else 0
      have hk'le : k' ≤ k := failureFollow_le P π c k hinv
      have hk'lt : k' < π.length := lt_of_le_of_lt hk'le hk_lt
      have hk''le : k'' ≤ π.length := by
        unfold k''
        split <;> omega
      have hinv' : ∀ i, (π ++ [k'']).getD i 0 < i + 1 := by
        intro i
        by_cases hi : i < π.length
        · rw [List.getD_append π [k''] 0 i hi]
          exact hinv i
        · have hge : π.length ≤ i := by omega
          rw [List.getD_append_right π [k''] 0 i hge]
          have hle : [k''].getD (i - π.length) 0 ≤ k'' := by
            by_cases h : i - π.length = 0 <;> simp [List.getD, h]
          omega
      have hk''lt : k'' < (π ++ [k'']).length := by
        simp [hk''le]
      computePrefixGo P (π ++ [k'']) k'' hinv' hk''lt rest

/-- The executable prefix-function array: `(computePrefixFunction P)[q]` is the
prefix function `π(q)` (CLRS §32.4). -/
def computePrefixFunction (P : Text α) : List ℕ :=
  match P with
  | [] => []
  | a :: as => computePrefixGo P [0] 0 (by intro i; simp) (by simp) as

/-- If `k < π(q)` and `P.take k` is a suffix of `P.take q`, then `P.take k` is
also a suffix of `P.take (π q)` (CLRS Lemma 32.5, induction step). -/
lemma prefixLen_chain_step (P : Text α) (q k : ℕ)
    (hk : isSuffix (P.take k) (P.take q)) (hklt : k < prefixLen P q) :
    isSuffix (P.take k) (P.take (prefixLen P q)) := by
  have hpfx : isSuffix (P.take (prefixLen P q)) (P.take q) := prefixLen_satisfies P q
  have hlen : (P.take k).length ≤ (P.take (prefixLen P q)).length := by
    simp [List.length_take]
    omega
  exact isSuffix_of_suffix_of_suffix hpfx hk hlen

end Chapter32
end CLRS
