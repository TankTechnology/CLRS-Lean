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

/-- Search for the largest `k ≤ n` such that `P.take k` is a suffix of `P.take q`
and `P[k] = c`. -/
def prefixMatchAux (P : Text α) (q : ℕ) (c : α) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      if suffixTest (P.take (n + 1)) (P.take q) && (P.getD (n + 1) default == c) then n + 1
      else prefixMatchAux P q c n

/-- One plus the largest `k < q` such that `P.take k` is a suffix of `P.take q`
and `P[k] = c`, or `0` when no such `k` exists. -/
def prefixMatch (P : Text α) (q : ℕ) (c : α) : ℕ :=
  let k := prefixMatchAux P q c (q - 1)
  if suffixTest (P.take k) (P.take q) && (P.getD k default == c) then k + 1 else 0

/-- `prefixMatchAux` never exceeds its bound. -/
lemma prefixMatchAux_le (P : Text α) (q : ℕ) (c : α) (n : ℕ) : prefixMatchAux P q c n ≤ n := by
  induction n with
  | zero => simp [prefixMatchAux]
  | succ n ih =>
      by_cases h : suffixTest (P.take (n + 1)) (P.take q) && (P.getD (n + 1) default == c)
      · simp [prefixMatchAux, h]
      · simp [prefixMatchAux, h]; omega

/-- If `P.take r` is a suffix of `P.take q ++ [a]` with `0 < r ≤ P.length`, then
the character `P[r-1]` equals `a`. -/
lemma suffix_snoc_char_eq (P : Text α) (q r : ℕ) (a : α) (hrpos : 0 < r) (hrle : r ≤ P.length)
    (hsuf : isSuffix (P.take r) (P.take q ++ [a])) : P.getD (r - 1) default = a := by
  have hchar : (P.take r).getLast? = some a := suffix_last_char_of_snoc P (P.take q) r a hsuf hrpos hrle
  have htake : P.take r = P.take (r - 1) ++ [a] := take_eq_take_pred_append P r a hrpos hrle hchar
  have hlenr : (P.take r).length = r := by rw [List.length_take]; exact Nat.min_eq_left hrle
  have hlt : r - 1 < (P.take r).length := by rw [hlenr]; omega
  have hltP : r - 1 < P.length := by omega
  have h1 : (P.take r).getD (r - 1) default = P.getD (r - 1) default := by
    rw [List.getD_eq_getElem (P.take r) default hlt]
    rw [List.getElem_take]
    rw [← List.getD_eq_getElem P default hltP]
  have h2 : (P.take (r - 1) ++ [a]).getD (r - 1) default = a := by
    rw [List.getD_append_right (P.take (r - 1)) [a] default (r - 1) (by simp)]
    simp
  calc
    P.getD (r - 1) default = (P.take r).getD (r - 1) default := h1.symm
    _ = (P.take (r - 1) ++ [a]).getD (r - 1) default := by rw [htake]
    _ = a := h2

/-- The recurrence (CLRS Lemma 32.6): `π(q + 1)` extends the longest proper
prefix-suffix of `P.take q` whose next character matches `P[q]`. -/
theorem prefixLen_snoc_eq (P : Text α) (q : ℕ) (hq : q < P.length) :
    prefixLen P (q + 1) = prefixMatch P q (P.getD q default) := by
  have hqlen : q + 1 ≤ P.length := Nat.succ_le_of_lt hq
  -- `P.take (q + 1) = P.take q ++ [P[q]]`
  have htake : P.take (q + 1) = P.take q ++ [P.getD q default] := by
    rw [List.take_succ]
    congr 1
    rw [List.getD_eq_getElem P default (by omega : q < P.length)]
    simp
  -- direction ≤ : π(q+1) ≤ prefixMatch
  have hle : prefixLen P (q + 1) ≤ prefixMatch P q (P.getD q default) := by
    unfold prefixMatch
    have hsat := prefixLen_satisfies P (q + 1)
    rw [htake] at hsat
    let r := prefixLen P (q + 1)
    by_cases hr : r = 0
    · simp [hr]
    · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
      have hrle : r ≤ P.length := le_trans (prefixLen_le P (q + 1)) hqlen
      have hpre : isSuffix (P.take (r - 1)) (P.take q) :=
        suffix_dropLast_of_snoc P (P.take q) r (P.getD q default) hrpos hrle hsat
      have hlastchar : P.getD (r - 1) default = P.getD q default :=
        suffix_snoc_char_eq P q r (P.getD q default) hrpos hrle hsat
      have hprop : suffixTest (P.take (r - 1)) (P.take q) && (P.getD (r - 1) default == P.getD q default) = true := by
        have hsuf : suffixTest (P.take (r - 1)) (P.take q) = true := (suffixTest_eq_isSuffix _ _).mpr hpre
        have hch : (P.getD (r - 1) default == P.getD q default) = true := beq_iff_eq.mpr hlastchar
        simp [hsuf, hch]
      have hmax : r - 1 ≤ prefixMatchAux P q (P.getD q default) (q - 1) := by
        have hgo : ∀ n, r - 1 ≤ n → r - 1 ≤ prefixMatchAux P q (P.getD q default) n := by
          intro n hrn
          induction n with
          | zero => omega
          | succ n ih =>
              by_cases ht : suffixTest (P.take (n + 1)) (P.take q) && (P.getD (n + 1) default == P.getD q default)
              · simp [prefixMatchAux, ht]; omega
              · have hrlt : r - 1 < n + 1 := by
                  by_cases heq : r - 1 = n + 1
                  · have hcontra : suffixTest (P.take (n + 1)) (P.take q) && (P.getD (n + 1) default == P.getD q default) = true := by
                      simpa [heq] using hprop
                    exact (ht hcontra).elim
                  · omega
                have := ih (by omega)
                simpa [prefixMatchAux, ht] using this
        exact hgo (q - 1) (by omega)
      have hbase : suffixTest (P.take (prefixMatchAux P q (P.getD q default) (q - 1))) (P.take q)
          && (P.getD (prefixMatchAux P q (P.getD q default) (q - 1)) default == P.getD q default) = true := by
        have hgo : ∀ n, (∃ k, k ≤ n ∧ suffixTest (P.take k) (P.take q) && (P.getD k default == P.getD q default) = true) →
            (suffixTest (P.take (prefixMatchAux P q (P.getD q default) n)) (P.take q)
              && (P.getD (prefixMatchAux P q (P.getD q default) n) default == P.getD q default)) = true := by
          intro n hex
          induction n with
          | zero =>
              rcases hex with ⟨k, hk, hkprop⟩
              have hk0 : k = 0 := by omega
              simpa [prefixMatchAux, hk0] using hkprop
          | succ n ih =>
              by_cases ht : suffixTest (P.take (n + 1)) (P.take q) && (P.getD (n + 1) default == P.getD q default)
              · simpa [prefixMatchAux, ht] using ht
              · rcases hex with ⟨k, hk, hkprop⟩
                have hkne : k ≠ n + 1 := by intro hkk; rw [hkk] at hkprop; exact (ht hkprop).elim
                have hklt : k ≤ n := by omega
                simpa [prefixMatchAux, ht] using ih ⟨k, hklt, hkprop⟩
        exact hgo (q - 1) ⟨r - 1, by omega, hprop⟩
      simp [prefixMatch, hbase]
      omega
  -- direction ≥ : prefixMatch ≤ π(q+1)
  have hge : prefixMatch P q (P.getD q default) ≤ prefixLen P (q + 1) := by
    unfold prefixMatch
    by_cases hb : suffixTest (P.take (prefixMatchAux P q (P.getD q default) (q - 1))) (P.take q)
        && (P.getD (prefixMatchAux P q (P.getD q default) (q - 1)) default == P.getD q default)
    · simp [hb]
      let k := prefixMatchAux P q (P.getD q default) (q - 1)
      have hksuf : isSuffix (P.take k) (P.take q) := (suffixTest_eq_isSuffix _ _).mp (Bool.and_eq_true_iff.mp hb).1
      have hkchar : P.getD k default = P.getD q default := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hb).2
      have hklt : k < q := by
        have hle := prefixMatchAux_le P q (P.getD q default) (q - 1)
        omega
      have htakek : P.take (k + 1) = P.take k ++ [P.getD k default] := by
        rw [List.take_succ]
        congr 1
        rw [List.getD_eq_getElem P default (by omega : k < P.length)]
        simp
      have hsufk1 : isSuffix (P.take k ++ [P.getD k default]) (P.take q ++ [P.getD q default]) := by
        have hsuf0 : isSuffix (P.take k ++ [P.getD k default]) (P.take q ++ [P.getD k default]) :=
          suffix_append_right hksuf
        simpa [hkchar] using hsuf0
      have hsufk1' : isSuffix (P.take (k + 1)) (P.take (q + 1)) := by
        simpa [htakek, htake] using hsufk1
      have hk1 : k + 1 ≤ prefixLen P (q + 1) :=
        prefixLen_maximal P (q + 1) (k + 1) (by omega) hsufk1'
      omega
    · simp [hb]
  exact le_antisymm hle hge

/-- The empty prefix `P.take 0 = []` is always a suffix of `P.take q`. -/
lemma suffixTest_take_zero (P : Text α) (q : ℕ) :
    suffixTest (P.take 0) (P.take q) = true := by
  exact (suffixTest_eq_isSuffix (P.take 0) (P.take q)).mpr (isSuffix_empty _)

/-- `prefixMatchAux` always returns a value whose prefix is a suffix of `P.take q`. -/
lemma prefixMatchAux_satisfies (P : Text α) (q : ℕ) (c : α) (n : ℕ) :
    suffixTest (P.take (prefixMatchAux P q c n)) (P.take q) = true := by
  induction n with
  | zero => simp [prefixMatchAux]; exact suffixTest_take_zero P q
  | succ n ih =>
      by_cases h : suffixTest (P.take (n + 1)) (P.take q) && (P.getD (n + 1) default == c)
      · simp [prefixMatchAux, h]
        exact (Bool.and_eq_true_iff.mp h).1
      · simp [prefixMatchAux, h]
        exact ih

/-- When `P.take (n+1)` is not a suffix of `P.take q`, `prefixMatchAux` at `n+1`
falls through to `n`. -/
lemma prefixMatchAux_succ_of_not_suffix (P : Text α) (q : ℕ) (c : α) (n : ℕ)
    (h : suffixTest (P.take (n + 1)) (P.take q) = false) :
    prefixMatchAux P q c (n + 1) = prefixMatchAux P q c n := by
  simp [prefixMatchAux, h]

/-- If no value in `(n', n]` is a suffix of `P.take q`, the search from `n`
agrees with the search from `n'`. -/
lemma prefixMatchAux_drop (P : Text α) (q : ℕ) (c : α) (n n' : ℕ) (hle : n' ≤ n)
    (h : ∀ j, n' < j → j ≤ n → suffixTest (P.take j) (P.take q) = false) :
    prefixMatchAux P q c n = prefixMatchAux P q c n' := by
  induction n generalizing n' with
  | zero =>
      have hn' : n' = 0 := by omega
      subst n'
      rfl
  | succ n ih =>
      by_cases hn' : n' = n + 1
      · subst n'; rfl
      · have hn'le : n' ≤ n := by omega
        have hsuf : suffixTest (P.take (n + 1)) (P.take q) = false :=
          h (n + 1) (by omega) (by omega)
        rw [prefixMatchAux_succ_of_not_suffix P q c n hsuf]
        exact ih hn'le (fun j hj1 hj2 => h j hj1 (by omega))

/-- `prefixMatchAux` is insensitive to the suffix target `q`, provided the
suffix tests agree on every position up to the bound. -/
lemma prefixMatchAux_congr (P : Text α) (q q' : ℕ) (c : α) (n : ℕ)
    (h : ∀ j, j ≤ n → (suffixTest (P.take j) (P.take q) = true ↔ suffixTest (P.take j) (P.take q') = true)) :
    prefixMatchAux P q c n = prefixMatchAux P q' c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hsuf : suffixTest (P.take (n + 1)) (P.take q) = suffixTest (P.take (n + 1)) (P.take q') := by
        have hiff := h (n + 1) (by omega)
        cases hq : suffixTest (P.take (n + 1)) (P.take q) with
        | false =>
            have hq' : suffixTest (P.take (n + 1)) (P.take q') = false := by
              cases hh : suffixTest (P.take (n + 1)) (P.take q') with
              | false => rfl
              | true =>
                  have hqtrue : suffixTest (P.take (n + 1)) (P.take q) = true := hiff.mpr hh
                  rw [hq] at hqtrue
                  cases hqtrue
            rw [hq, hq']
        | true =>
            have hq' : suffixTest (P.take (n + 1)) (P.take q') = true := hiff.mp hq
            rw [hq, hq']
      simp [prefixMatchAux, hsuf, ih]

end Chapter32
end CLRS
