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
- {lit}`kmpMatcher P T` — the executable all-occurrences `KMP-MATCHER` scan.

## Main results

- `prefixLen_satisfies` / `prefixLen_maximal` — `P.take (π q)` is the longest
  proper prefix of `P` that is a suffix of `P.take q`.
- `prefixLen_chain_step` — the CLRS Lemma 32.5 induction step: a shorter
  prefix-suffix of `P.take q` is a prefix-suffix of `P.take (π q)`.
- `prefixLen_snoc_eq` — the CLRS Lemma 32.6 recurrence: `π(q + 1)` extends the
  longest prefix-suffix of `P.take q` whose next character matches `P[q]`.
- `failureFollow_eq_prefixMatchAux` — following failure links from `π(q)` agrees
  with the from-scratch search.
- `computePrefixFunction_correct` — each entry of the executable array equals
  `prefixLen` (CLRS Lemma 32.6).
- `kmpStep_eq_delta` — one executable scan step computes the automaton
  transition `δ(q, a)`.
- `kmpMatcher_correct` — `kmpMatcher P T` agrees with `naiveMatcher T P`
  (all and only matches), with `kmpMatcher_sound`/`kmpMatcher_complete`.
- `kmpTotalCost_le` — the costed prefix construction plus costed scan runs in
  linear time `O(|P| + |T|)`.

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
      unfold prefixMatchAux
      split <;> omega

/-- If `prefixMatchAux` returns a nonzero value, that value's character matches `c`. -/
lemma prefixMatchAux_char (P : Text α) (q : ℕ) (c : α) (n : ℕ) :
    prefixMatchAux P q c n = 0 ∨ (P.getD (prefixMatchAux P q c n) default == c) = true := by
  induction n with
  | zero => simp [prefixMatchAux]
  | succ n ih =>
      unfold prefixMatchAux
      split
      · next h => right; exact (Bool.and_eq_true_iff.mp h).2
      · next _ => exact ih

/-- `prefixMatchAux` is maximal: any candidate below the bound is at most its result. -/
lemma prefixMatchAux_maximal (P : Text α) (q : ℕ) (c : α) (n k : ℕ) (hk : k ≤ n)
    (hsuf : suffixTest (P.take k) (P.take q) = true) (hchar : (P.getD k default == c) = true) :
    k ≤ prefixMatchAux P q c n := by
  induction n with
  | zero => omega
  | succ n ih =>
      unfold prefixMatchAux
      split
      · next _ => omega
      · next hnot =>
          have hkne : k ≠ n + 1 := by
            intro hkk
            apply hnot
            subst k
            rw [hsuf, hchar]
            rfl
          have hklt : k ≤ n := by omega
          exact ih hklt

/-- If a candidate exists below the bound, the result of `prefixMatchAux` is itself a
candidate (its character matches `c`). -/
lemma prefixMatchAux_found (P : Text α) (q : ℕ) (c : α) (n : ℕ)
    (hex : ∃ j, j ≤ n ∧ (suffixTest (P.take j) (P.take q) && (P.getD j default == c)) = true) :
    (P.getD (prefixMatchAux P q c n) default == c) = true := by
  induction n with
  | zero =>
      rcases hex with ⟨j, hj, hjprop⟩
      have hj0 : j = 0 := by omega
      change (P.getD 0 default == c) = true
      rw [hj0] at hjprop
      exact (Bool.and_eq_true_iff.mp hjprop).2
  | succ n ih =>
      unfold prefixMatchAux
      by_cases ht : (suffixTest (P.take (n+1)) (P.take q) && (P.getD (n+1) default == c)) = true
      · rw [ht]
        exact (Bool.and_eq_true_iff.mp ht).2
      · have htf : (suffixTest (P.take (n+1)) (P.take q) && (P.getD (n+1) default == c)) = false := by
          cases hh : (suffixTest (P.take (n+1)) (P.take q) && (P.getD (n+1) default == c))
          · rfl
          · exact (ht hh).elim
        rw [htf]
        rcases hex with ⟨j, hj, hjprop⟩
        have hjne : j ≠ n + 1 := by
          intro hjj
          rw [hjj] at hjprop
          exact (ht hjprop).elim
        have hjle : j ≤ n := by omega
        exact ih ⟨j, hjle, hjprop⟩

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
      unfold prefixMatchAux
      split
      · next h => exact (Bool.and_eq_true_iff.mp h).1
      · next _ => exact ih

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
    have hlen : (P.take (r - 1)).length = r - 1 := by
      rw [List.length_take]
      exact Nat.min_eq_left (by omega)
    rw [List.getD_append_right (P.take (r - 1)) [a] default (r - 1) (by omega)]
    simp [hlen]
  calc
    P.getD (r - 1) default = (P.take r).getD (r - 1) default := h1.symm
    _ = (P.take (r - 1) ++ [a]).getD (r - 1) default := by rw [htake]
    _ = a := h2

/-- `prefixMatch P q c` equals `k + 1` when the search result's character matches
`c`, and `0` otherwise. -/
lemma prefixMatch_eq (P : Text α) (q : ℕ) (c : α) :
    prefixMatch P q c =
      if (P.getD (prefixMatchAux P q c (q - 1)) default == c)
      then prefixMatchAux P q c (q - 1) + 1 else 0 := by
  unfold prefixMatch
  dsimp
  rw [prefixMatchAux_satisfies P q c (q - 1)]
  rfl

/-- The recurrence (CLRS Lemma 32.6): `π(q + 1)` extends the longest proper
prefix-suffix of `P.take q` whose next character matches `P[q]`. -/
theorem prefixLen_snoc_eq (P : Text α) (q : ℕ) (hqpos : 0 < q) (hq : q < P.length) :
    prefixLen P (q + 1) = prefixMatch P q (P.getD q default) := by
  have hqlen : q + 1 ≤ P.length := Nat.succ_le_of_lt hq
  have htake : P.take (q + 1) = P.take q ++ [P.getD q default] := by
    rw [List.take_succ]
    congr 1
    rw [List.getD_eq_getElem P default (by omega : q < P.length)]
    simp
  let c := P.getD q default
  let k := prefixMatchAux P q c (q - 1)
  have hksuf : suffixTest (P.take k) (P.take q) = true := by
    dsimp [k]
    exact prefixMatchAux_satisfies P q c (q - 1)
  have hkle : k ≤ q - 1 := by
    dsimp [k]
    exact prefixMatchAux_le P q c (q - 1)
  have hklt : k < q := by omega
  have hkltP : k < P.length := by omega
  -- direction ≤ : π(q+1) ≤ prefixMatch P q c
  have hle : prefixLen P (q + 1) ≤ prefixMatch P q c := by
    by_cases h0 : prefixLen P (q + 1) = 0
    · rw [h0]
      exact Nat.zero_le _
    · let r := prefixLen P (q + 1)
      have hrpos : 0 < r := Nat.pos_of_ne_zero h0
      have hrle : r ≤ P.length := le_trans (prefixLen_le P (q + 1)) hqlen
      have hrle' : r ≤ q := by
        have hlt := prefixLen_lt_of_pos P (q + 1) (by omega)
        dsimp [r]
        omega
      have hsat := prefixLen_satisfies P (q + 1)
      rw [htake] at hsat
      have hpre : isSuffix (P.take (r - 1)) (P.take q) :=
        suffix_dropLast_of_snoc P (P.take q) r c hrpos hrle hsat
      have hlastchar : P.getD (r - 1) default = c :=
        suffix_snoc_char_eq P q r c hrpos hrle hsat
      have hsuf' : suffixTest (P.take (r - 1)) (P.take q) = true :=
        (suffixTest_eq_isSuffix _ _).mpr hpre
      have hchar' : (P.getD (r - 1) default == c) = true := beq_iff_eq.mpr hlastchar
      have hcand : (suffixTest (P.take (r - 1)) (P.take q) && (P.getD (r - 1) default == c)) = true := by
        rw [hsuf', hchar']
        rfl
      have hmax : r - 1 ≤ k :=
        prefixMatchAux_maximal P q c (q - 1) (r - 1) (by omega) hsuf' hchar'
      have hchar_k : (P.getD k default == c) = true :=
        prefixMatchAux_found P q c (q - 1) ⟨r - 1, by omega, hcand⟩
      have hpm : prefixMatch P q c = k + 1 := by
        rw [prefixMatch_eq]
        dsimp [k] at hchar_k
        rw [hchar_k]
        rfl
      rw [hpm]
      omega
  -- direction ≥ : prefixMatch P q c ≤ π(q+1)
  have hge : prefixMatch P q c ≤ prefixLen P (q + 1) := by
    by_cases hck : (P.getD k default == c) = true
    · have hchar : P.getD k default = c := beq_iff_eq.mp hck
      have hksuf' : isSuffix (P.take k) (P.take q) := (suffixTest_eq_isSuffix _ _).mp hksuf
      have htakek : P.take (k + 1) = P.take k ++ [P.getD k default] := by
        rw [List.take_succ]
        congr 1
        rw [List.getD_eq_getElem P default (by omega : k < P.length)]
        simp
      have hsufk1 : isSuffix (P.take (k + 1)) (P.take (q + 1)) := by
        rw [htakek, htake]
        have hchar' : P.getD k default = P.getD q default := by
          dsimp [c] at hchar
          exact hchar
        have hsuf0 : isSuffix (P.take k ++ [P.getD k default]) (P.take q ++ [P.getD k default]) :=
          suffix_append_right hksuf'
        rw [← hchar']
        exact hsuf0
      have hklt1 : k + 1 < q + 1 := by omega
      have hk1 : k + 1 ≤ prefixLen P (q + 1) :=
        prefixLen_maximal P (q + 1) (k + 1) hklt1 hsufk1
      have hpm : prefixMatch P q c = k + 1 := by
        rw [prefixMatch_eq]
        dsimp [k] at hck
        rw [hck]
        rfl
      rw [hpm]
      exact hk1
    · have hpm : prefixMatch P q c = 0 := by
        rw [prefixMatch_eq]
        have hf : (P.getD (prefixMatchAux P q c (q - 1)) default == c) = false := by
          dsimp [k] at hck
          cases hh : (P.getD (prefixMatchAux P q c (q - 1)) default == c)
          · rfl
          · exact (hck hh).elim
        rw [hf]
        rfl
      rw [hpm]
      exact Nat.zero_le _
  exact le_antisymm hle hge

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
        exact ih n' hn'le (fun j hj1 hj2 => h j hj1 (by omega))

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
        revert hiff
        generalize hq : suffixTest (P.take (n + 1)) (P.take q) = b1
        generalize hq' : suffixTest (P.take (n + 1)) (P.take q') = b2
        intro hiff
        cases b1 <;> cases b2 <;> simp_all
      have ih' : prefixMatchAux P q c n = prefixMatchAux P q' c n :=
        ih (fun j hj => h j (by omega))
      rw [prefixMatchAux, prefixMatchAux]
      rw [hsuf]
      rw [ih']

/-- The from-scratch search from `k - 1` over `P.take q` agrees with the search from
`prefixLen P k` over `P.take k`, when `k = prefixLen P q` (the failure-link jump). -/
lemma prefixMatchAux_chain_jump (P : Text α) (q k : ℕ) (c : α) (hk : k = prefixLen P q) (hkpos : 0 < k) :
    prefixMatchAux P q c (k - 1) = prefixMatchAux P k c (prefixLen P k) := by
  have hplt : prefixLen P k < k := prefixLen_lt_of_pos P k hkpos
  have hdrop : prefixMatchAux P q c (k - 1) = prefixMatchAux P q c (prefixLen P k) := by
    refine prefixMatchAux_drop P q c (k - 1) (prefixLen P k) (by omega) ?_
    intro j hj1 hj2
    by_contra hsj
    have hsjt : suffixTest (P.take j) (P.take q) = true := by
      cases h : suffixTest (P.take j) (P.take q) with
      | false => exact (hsj h).elim
      | true => rfl
    have hjsuf : isSuffix (P.take j) (P.take q) := (suffixTest_eq_isSuffix _ _).mp hsjt
    have hjltpl : j < prefixLen P q := by rw [← hk]; omega
    have hchain : isSuffix (P.take j) (P.take k) := by
      simpa [hk] using (prefixLen_chain_step P q j hjsuf hjltpl)
    have hjltk : j < k := by omega
    have hmax : j ≤ prefixLen P k := prefixLen_maximal P k j hjltk hchain
    omega
  have hcongr : prefixMatchAux P q c (prefixLen P k) = prefixMatchAux P k c (prefixLen P k) := by
    refine prefixMatchAux_congr P q k c (prefixLen P k) ?_
    intro j hj
    constructor
    · intro hsjt
      have hjsuf : isSuffix (P.take j) (P.take q) := (suffixTest_eq_isSuffix _ _).mp hsjt
      have hjltpl : j < prefixLen P q := by
        rw [← hk]
        omega
      have hchain : isSuffix (P.take j) (P.take k) := by
        simpa [hk] using (prefixLen_chain_step P q j hjsuf hjltpl)
      exact (suffixTest_eq_isSuffix _ _).mpr hchain
    · intro hsjt
      have hjsuf : isSuffix (P.take j) (P.take k) := (suffixTest_eq_isSuffix _ _).mp hsjt
      have hksuf : isSuffix (P.take k) (P.take q) := by
        simpa [hk] using prefixLen_satisfies P q
      have hjsuf' : isSuffix (P.take j) (P.take q) := suffix_trans hjsuf hksuf
      exact (suffixTest_eq_isSuffix _ _).mpr hjsuf'
  exact hdrop.trans hcongr

/-- Following failure links from `k = π(q)` agrees with the from-scratch search
`prefixMatchAux P q c k`, when `π` is the correct prefix-function array. -/
lemma failureFollow_eq_prefixMatchAux (P : Text α) (π : List ℕ) (c : α) (q k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1)
    (hπ : ∀ i, i < q → π.getD i 0 = prefixLen P (i + 1))
    (hk : k = prefixLen P q) :
    failureFollow P π c k hinv = prefixMatchAux P q c k := by
  revert q
  refine Nat.strong_induction_on k ?_
  intro k ih q hπ hk
  by_cases hk0 : k = 0
  · subst hk0
    rw [failureFollow.eq_1, prefixMatchAux]
    rfl
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    have hsuf : suffixTest (P.take k) (P.take q) = true := by
      simpa [hk] using (suffixTest_eq_isSuffix _ _).mpr (prefixLen_satisfies P q)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hqpos : 0 < q := by
      have hle := prefixLen_le P q
      rw [← hk] at hle
      omega
    have hnltq : n < q := by
      have hlt := prefixLen_lt_of_pos P q hqpos
      rw [← hk] at hlt
      omega
    rw [failureFollow.eq_1]
    simp only [Nat.succ_ne_zero, if_false]
    rw [prefixMatchAux]
    rw [hsuf]
    change (if P.getD (n + 1) default = c then n + 1 else failureFollow P π c (π.getD n 0) hinv)
      = (if (P.getD (n + 1) default == c) = true then n + 1 else prefixMatchAux P q c n)
    by_cases hc : P.getD (n + 1) default = c
    · rw [if_pos hc, if_pos (beq_iff_eq.mpr hc)]
    · have hcneg : ¬ (P.getD (n + 1) default == c) = true := by
        intro hh
        exact hc (beq_iff_eq.mp hh)
      rw [if_neg hc, if_neg hcneg]
      have hπn : π.getD n 0 = prefixLen P (n + 1) := hπ n hnltq
      rw [hπn]
      have hih := ih (prefixLen P (n + 1)) (prefixLen_lt_of_pos P (n + 1) (by omega))
        (n + 1) (fun i hi => hπ i (by omega)) rfl
      rw [hih]
      exact (prefixMatchAux_chain_jump P q (n + 1) c (by simpa [hk]) (by omega)).symm

/-- `prefixMatchAux` from `prefixLen P q` agrees with the full search from `q - 1`. -/
lemma prefixMatchAux_top_drop (P : Text α) (q : ℕ) (c : α) (hqpos : 0 < q) :
    prefixMatchAux P q c (prefixLen P q) = prefixMatchAux P q c (q - 1) := by
  have hle : prefixLen P q ≤ q - 1 := by
    have hlt := prefixLen_lt_of_pos P q hqpos
    omega
  refine (prefixMatchAux_drop P q c (q - 1) (prefixLen P q) hle ?_).symm
  intro j hj1 hj2
  by_contra hsj
  have hsjt : suffixTest (P.take j) (P.take q) = true := by
    cases h : suffixTest (P.take j) (P.take q) with
    | false => exact (hsj h).elim
    | true => rfl
  have hjsuf : isSuffix (P.take j) (P.take q) := (suffixTest_eq_isSuffix _ _).mp hsjt
  have hjltq : j < q := by omega
  have hmax : j ≤ prefixLen P q := prefixLen_maximal P q j hjltq hjsuf
  omega

/-- One step of `computePrefixGo` computes `prefixLen P (π.length + 1)` (the
failure-link recurrence, CLRS Lemma 32.6). -/
lemma computePrefixGo_step (P : Text α) (π : List ℕ) (k : ℕ) (c : α)
    (hinv : ∀ i, π.getD i 0 < i + 1)
    (hπ : ∀ i, i < π.length → π.getD i 0 = prefixLen P (i + 1))
    (hk : k = prefixLen P π.length)
    (hc : c = P.getD π.length default)
    (hqpos : 0 < π.length) (hqlt : π.length < P.length) :
    (if (P.getD (failureFollow P π c k hinv) default) = c then failureFollow P π c k hinv + 1 else 0)
      = prefixLen P (π.length + 1) := by
  have hk' : failureFollow P π c k hinv = prefixMatchAux P π.length c (π.length - 1) := by
    rw [failureFollow_eq_prefixMatchAux P π c π.length k hinv hπ hk]
    rw [hk]
    exact prefixMatchAux_top_drop P π.length c hqpos
  have hsnoc : prefixLen P (π.length + 1) = prefixMatch P π.length c := by
    simpa [hc] using (prefixLen_snoc_eq P π.length hqpos hqlt)
  have hpm : prefixMatch P π.length c =
      (if (P.getD (prefixMatchAux P π.length c (π.length - 1)) default == c)
        then prefixMatchAux P π.length c (π.length - 1) + 1 else 0) :=
    prefixMatch_eq P π.length c
  rw [hsnoc]
  rw [hpm, hk']
  by_cases hc' : P.getD (prefixMatchAux P π.length c (π.length - 1)) default = c
  · rw [if_pos hc', if_pos (beq_iff_eq.mpr hc')]
  · have hneg : ¬ (P.getD (prefixMatchAux P π.length c (π.length - 1)) default == c) = true := by
      intro hh
      exact hc' (beq_iff_eq.mp hh)
    rw [if_neg hc', if_neg hneg]

/-- `failureFollow`'s result is independent of its `hinv` proof argument. -/
lemma failureFollow_irrelevant (P : Text α) (π : List ℕ) (c : α) (k : ℕ)
    (hinv hinv' : ∀ i, π.getD i 0 < i + 1) :
    failureFollow P π c k hinv = failureFollow P π c k hinv' := by
  unfold failureFollow
  by_cases hk : k = 0 <;> simp [hk]

/-- `computePrefixGo`'s result is independent of its `hinv`/`hk_lt` proof arguments. -/
lemma computePrefixGo_irrelevant (P : Text α) (π : List ℕ) (k : ℕ) (rest : Text α)
    (hinv hinv' : ∀ i, π.getD i 0 < i + 1) (hk_lt hk_lt' : k < π.length) :
    computePrefixGo P π k hinv hk_lt rest = computePrefixGo P π k hinv' hk_lt' rest := by
  induction rest generalizing π k hinv hinv' hk_lt hk_lt' with
  | nil => rfl
  | cons c rest' ih =>
      unfold computePrefixGo
      simp [failureFollow_irrelevant, ih]

/-- Extract the head/tail of `P.drop n = c :: rest`. -/
lemma drop_cons (P : Text α) (n : ℕ) (c : α) (rest : Text α) (h : P.drop n = c :: rest) :
    n < P.length ∧ c = P.getD n default ∧ rest = P.drop (n + 1) := by
  have hlen : n < P.length := by
    by_contra hge
    have hnil : P.drop n = [] := List.drop_eq_nil_of_le (by omega)
    rw [h] at hnil
    cases hnil
  refine ⟨hlen, ?_, ?_⟩
  · have hhead : (P.drop n).head? = (c :: rest).head? := by rw [h]
    simp at hhead
    have : P.getD n default = c := by
      change P[n]?.getD default = c
      rw [hhead]
      rfl
    exact this.symm
  · have htail : (P.drop n).drop 1 = (c :: rest).drop 1 := by rw [h]
    simp at htail
    exact htail.symm

/-- The invariant of `computePrefixGo`: it extends a correct prefix array. -/
lemma computePrefixGo_correct (P : Text α) (π : List ℕ) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hk_lt : k < π.length)
    (hπ : ∀ i, i < π.length → π.getD i 0 = prefixLen P (i + 1))
    (hk : k = prefixLen P π.length) :
    ∀ rest, rest = P.drop π.length →
      ∀ i, i < (computePrefixGo P π k hinv hk_lt rest).length →
        (computePrefixGo P π k hinv hk_lt rest).getD i 0 = prefixLen P (i + 1) := by
  intro rest hrest
  induction rest generalizing π k hinv hk_lt hπ hk with
  | nil =>
      intro i hi
      simpa [computePrefixGo] using hπ i (by simpa [computePrefixGo] using hi)
  | cons c rest' ih =>
      intro i hi
      have hd := drop_cons P π.length c rest' hrest.symm
      have hqlt : π.length < P.length := hd.1
      have hc : c = P.getD π.length default := hd.2.1
      have hrest' : rest' = P.drop (π.length + 1) := hd.2.2
      have hqpos : 0 < π.length := by omega
      let k' := failureFollow P π c k hinv
      let k'' := if (P.getD k' default) = c then k' + 1 else 0
      have hk'le : k' ≤ k := failureFollow_le P π c k hinv
      have hk''le : k'' ≤ π.length := by
        dsimp [k'']
        have hk'lt : k' < π.length := lt_of_le_of_lt hk'le hk_lt
        split <;> omega
      have hstep : k'' = prefixLen P (π.length + 1) := by
        dsimp [k'', k']
        exact computePrefixGo_step P π k c hinv hπ hk hc hqpos hqlt
      have hπ' : ∀ j, j < (π ++ [k'']).length → (π ++ [k'']).getD j 0 = prefixLen P (j + 1) := by
        intro j hj
        by_cases hjπ : j < π.length
        · rw [List.getD_append π [k''] 0 j hjπ]
          exact hπ j hjπ
        · have hge : π.length ≤ j := by omega
          rw [List.getD_append_right π [k''] 0 j hge]
          have hj_eq : j = π.length := by
            have hj' : j < π.length + 1 := by simpa [List.length_append] using hj
            omega
          subst j
          simpa using hstep
      have hk' : k'' = prefixLen P (π ++ [k'']).length := by
        simpa [List.length_append] using hstep
      have hinv'' : ∀ j, (π ++ [k'']).getD j 0 < j + 1 := by
        intro j
        by_cases hjπ : j < π.length
        · rw [List.getD_append π [k''] 0 j hjπ]
          exact hinv j
        · have hge : π.length ≤ j := by omega
          rw [List.getD_append_right π [k''] 0 j hge]
          have hle : [k''].getD (j - π.length) 0 ≤ k'' := by
            by_cases h : j - π.length = 0 <;> simp [List.getD, h]
          omega
      have hk''lt : k'' < (π ++ [k'']).length := by
        simp [hk''le]
      have heq : computePrefixGo P π k hinv hk_lt (c :: rest') =
          computePrefixGo P (π ++ [k'']) k'' hinv'' hk''lt rest' := by
        rw [computePrefixGo]
      rw [heq] at hi ⊢
      exact (ih (π ++ [k'']) k'' hinv'' hk''lt hπ' hk' (by simpa [List.length_append] using hrest')) i hi

/-- `computePrefixGo`'s result has length `π.length + rest.length`. -/
lemma computePrefixGo_length (P : Text α) (π : List ℕ) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hk_lt : k < π.length) (rest : Text α) :
    (computePrefixGo P π k hinv hk_lt rest).length = π.length + rest.length := by
  induction rest generalizing π k hinv hk_lt with
  | nil => rfl
  | cons c rest' ih =>
      rw [computePrefixGo]
      rw [ih]
      simp
      omega

/-- The executable `COMPUTE-PREFIX-FUNCTION` array equals the prefix function
`prefixLen` (CLRS Lemma 32.6). -/
theorem computePrefixFunction_correct (P : Text α) (i : ℕ) (hi : i < P.length) :
    (computePrefixFunction P).getD i 0 = prefixLen P (i + 1) := by
  cases P with
  | nil => simp at hi
  | cons a as =>
      have hπ : ∀ j, j < 1 → [0].getD j 0 = prefixLen (a :: as) (j + 1) := by
        intro j hj
        have hj0 : j = 0 := by omega
        subst j
        simp [prefixLen, prefixLenAux]
      have hk : 0 = prefixLen (a :: as) 1 := by
        simp [prefixLen, prefixLenAux]
      have hres := computePrefixGo_correct (a :: as) [0] 0
        (by intro j; simp) (by simp) hπ hk
        as (by simp)
      have hlen : (computePrefixGo (a :: as) [0] 0 (by intro j; simp) (by simp) as).length
          = (a :: as).length := by
        rw [computePrefixGo_length]
        simp
        omega
      simpa [computePrefixFunction] using
        (hres i (by simpa [hlen] using hi))

/-- The executable prefix array has exactly `|P|` entries. -/
lemma computePrefixFunction_length (P : Text α) : (computePrefixFunction P).length = P.length := by
  cases P with
  | nil => simp [computePrefixFunction]
  | cons a as =>
      simp [computePrefixFunction]
      rw [computePrefixGo_length]
      simp [Nat.add_comm]

/-- Every entry of the executable prefix array is strictly below its successor
index, so it can serve as the `hinv` termination argument of `failureFollow`. -/
lemma computePrefixFunction_inv (P : Text α) :
    ∀ i, (computePrefixFunction P).getD i 0 < i + 1 := by
  intro i
  by_cases hi : i < P.length
  · rw [computePrefixFunction_correct P i hi]
    exact prefixLen_lt_of_pos P (i + 1) (by omega)
  · rw [List.getD_eq_default (hn := by rw [computePrefixFunction_length P]; omega)]
    omega

/-! ## The KMP scan -/

/-- The advance step of the KMP scan: if the current fallback position's
character matches `a`, extend the match by one; otherwise restart at `0`.
`failureFollow` guarantees its result is `0` whenever its character does not
match `a`, so the `else 0` branch is exactly the textbook `q ← q` state. -/
def kmpAdvance (P : Text α) (q' : ℕ) (a : α) : ℕ :=
  if P.getD q' default = a then q' + 1 else 0

/-- One KMP scan step (CLRS `KMP-MATCHER` lines 6-9): given the current state
`q` (the number of matched characters, `q ≤ |P|`) and the next text character
`a`, follow failure links until the next character matches, then advance.  When
`q = |P|` the step first falls back to `π[|P|-1]`, which is the textbook reset
`q ← π[q]` performed before the next character is read. -/
def kmpStep (P : Text α) (π : List ℕ) (q : ℕ) (a : α)
    (hinv : ∀ i, π.getD i 0 < i + 1) : ℕ :=
  if q = P.length then
    kmpAdvance P (failureFollow P π a (π.getD (P.length - 1) 0) hinv) a
  else
    kmpAdvance P (failureFollow P π a q hinv) a

/-- The Knuth–Morris–Pratt scan: scan `T` left-to-right maintaining the
automaton state `q = δ*(0, scanned)`, recording every shift where the state
reaches `|P|`.  `scanned` is the text already scanned and `m = |P|`. -/
def kmpScan (P : Text α) (π : List ℕ) (m : ℕ) (scanned : Text α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) : Text α → List ℕ
  | [] => if q == m then [scanned.length - m] else []
  | c :: rest =>
      let q' := kmpStep P π q c hinv
      let tail := kmpScan P π m (scanned ++ [c]) q' hinv rest
      if q == m then (scanned.length - m) :: tail else tail

/-- The Knuth–Morris–Pratt matcher: the list of all shifts where `P` occurs in
`T`, computed by the prefix function plus a single left-to-right scan
(CLRS §32.4). -/
def kmpMatcher (P T : Text α) : List ℕ :=
  if P.length = 0 then List.range (T.length + 1)
  else kmpScan P (computePrefixFunction P) P.length [] 0 (computePrefixFunction_inv P) T

/-- The specification transition: `δ(q, a)` written as "extend by one if the
character matches `P[q]`, otherwise the longest proper prefix-suffix extension
`prefixMatch`".  This is the semantic content of one KMP scan step. -/
def kmpNextSpec (P : Text α) (q : ℕ) (a : α) : ℕ :=
  if q < P.length ∧ P.getD q default = a then q + 1 else prefixMatch P q a

/-- `kmpAdvance` over the from-scratch search result is exactly `prefixMatch`. -/
lemma kmpAdvance_eq_prefixMatch (P : Text α) (q : ℕ) (a : α) :
    kmpAdvance P (prefixMatchAux P q a (q - 1)) a = prefixMatch P q a := by
  unfold kmpAdvance
  rw [prefixMatch_eq P q a]
  change (if P.getD (prefixMatchAux P q a (q - 1)) default = a then prefixMatchAux P q a (q - 1) + 1 else 0)
    = (if (P.getD (prefixMatchAux P q a (q - 1)) default == a) = true then prefixMatchAux P q a (q - 1) + 1 else 0)
  by_cases h : P.getD (prefixMatchAux P q a (q - 1)) default = a
  · rw [if_pos h, if_pos (beq_iff_eq.mpr h)]
  · rw [if_neg h]
    have hneg : ¬ (P.getD (prefixMatchAux P q a (q - 1)) default == a) = true := by
      intro hh
      exact h (beq_iff_eq.mp hh)
    rw [if_neg hneg]

/-- If `P[q] = a`, the failure-link search starting at `q` stays at `q`. -/
lemma failureFollow_eq_self_of_char (P : Text α) (π : List ℕ) (a : α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hchar : P.getD q default = a) :
    failureFollow P π a q hinv = q := by
  rw [failureFollow.eq_1]
  by_cases hq0 : q = 0
  · simp [hq0]
  · simp only [hq0, if_false]
    by_cases hc : P[q]?.getD default = a
    · simp [hc]
    · have hc' : P[q]?.getD default = a := by simpa using hchar
      exact (hc hc').elim

/-- One fallback step: when `P[q] ≠ a` and `q > 0`, the search moves to
`π[q-1]`. -/
lemma failureFollow_step_eq (P : Text α) (π : List ℕ) (a : α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hqpos : 0 < q) (hne : P.getD q default ≠ a) :
    failureFollow P π a q hinv = failureFollow P π a (π.getD (q - 1) 0) hinv := by
  rw [failureFollow.eq_1]
  by_cases hq0 : q = 0
  · omega
  · simp only [hq0, if_false]
    by_cases hc : P[q]?.getD default = a
    · have hc' : P[q]?.getD default = a := by simpa using hc
      have hne' : P[q]?.getD default ≠ a := by simpa using hne
      exact (hne' hc').elim
    · simp [hc]

/-- The failure-link search from `prefixLen P q` agrees with the from-scratch
search `prefixMatchAux P q a (q - 1)`. -/
lemma failureFollow_from_prefixLen_eq (P : Text α) (π : List ℕ) (a : α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1)
    (hπ : ∀ i, i < q → π.getD i 0 = prefixLen P (i + 1))
    (hqpos : 0 < q) :
    failureFollow P π a (prefixLen P q) hinv = prefixMatchAux P q a (q - 1) := by
  rw [failureFollow_eq_prefixMatchAux P π a q (prefixLen P q) hinv hπ rfl]
  exact prefixMatchAux_top_drop P q a hqpos

/-- When `P[q] ≠ a`, the failure-link search from `q` agrees with the
from-scratch search `prefixMatchAux P q a (q - 1)` (for `q = 0` both are `0`). -/
lemma failureFollow_eq_prefixMatchAux_top_of_ne (P : Text α) (π : List ℕ) (a : α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1)
    (hπ : ∀ i, i < q → π.getD i 0 = prefixLen P (i + 1))
    (hne : P.getD q default ≠ a) :
    failureFollow P π a q hinv = prefixMatchAux P q a (q - 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp [failureFollow, prefixMatchAux]
  · have hqpos : 0 < q := by omega
    rw [failureFollow_step_eq P π a q hinv hqpos hne]
    have hπq1 : π.getD (q - 1) 0 = prefixLen P q := by
      have h := hπ (q - 1) (by omega)
      rwa [Nat.sub_add_cancel hqpos] at h
    rw [hπq1]
    exact failureFollow_from_prefixLen_eq P π a q hinv hπ hqpos

/-- `suffixLen P (P.take q ++ [a]) ≤ kmpNextSpec P q a`: the suffix function of
a one-step extension never exceeds the specification transition. -/
lemma suffixLen_snoc_le_spec (P : Text α) (q : ℕ) (a : α) (hq : q ≤ P.length) :
    suffixLen P (P.take q ++ [a]) ≤ kmpNextSpec P q a := by
  unfold kmpNextSpec
  by_cases hcond : q < P.length ∧ P.getD q default = a
  · rw [if_pos hcond]
    have hle := suffixLen_le_length P (P.take q ++ [a])
    have hlen : (P.take q ++ [a]).length ≤ q + 1 := by
      rw [List.length_append, List.length_singleton, List.length_take]
      exact Nat.add_le_add_right (Nat.min_le_left q P.length) 1
    omega
  · rw [if_neg hcond]
    have hr : suffixLen P (P.take q ++ [a]) ≤ P.length := suffixLen_le P (P.take q ++ [a])
    have hrle : suffixLen P (P.take q ++ [a]) ≤ q + 1 := by
      have hle := suffixLen_le_length P (P.take q ++ [a])
      have hlen : (P.take q ++ [a]).length ≤ q + 1 := by
        rw [List.length_append, List.length_singleton, List.length_take]
        exact Nat.add_le_add_right (Nat.min_le_left q P.length) 1
      omega
    have hsuf : isSuffix (P.take (suffixLen P (P.take q ++ [a]))) (P.take q ++ [a]) :=
      suffixLen_satisfies P (P.take q ++ [a])
    set r := suffixLen P (P.take q ++ [a]) with hr_def
    have hr' : r ≤ P.length := by simpa [hr_def] using hr
    have hrle' : r ≤ q + 1 := by simpa [hr_def] using hrle
    have hsuf' : isSuffix (P.take r) (P.take q ++ [a]) := by simpa [hr_def] using hsuf
    by_cases hrq : r = q + 1
    · exfalso
      have hqlt : q < P.length := by
        have : q + 1 ≤ P.length := by simpa [hrq] using hr'
        omega
      have hchar : P.getD q default = a := by
        have hsuf'' : isSuffix (P.take (q + 1)) (P.take q ++ [a]) := by simpa [hrq] using hsuf'
        have hk' : q + 1 ≤ P.length := by omega
        have hlast : (P.take (q + 1)).getLast? = some a :=
          suffix_last_char_of_snoc P (P.take q) (q + 1) a hsuf'' (by omega) hk'
        have htake1 : P.take (q + 1) = P.take q ++ [a] :=
          take_eq_take_pred_append P (q + 1) a (by omega) hk' hlast
        have htake2 : P.take (q + 1) = P.take q ++ [P.getD q default] := by
          rw [List.take_succ]
          congr 1
          rw [List.getD_eq_getElem P default (by omega : q < P.length)]
          simp
        have hconcat : P.take q ++ [a] = P.take q ++ [P.getD q default] := by
          rw [← htake1, ← htake2]
        have hsing : [a] = [P.getD q default] := by
          simpa [List.drop_left] using (congrArg (fun t => t.drop (P.take q).length) hconcat)
        exact (List.cons.inj hsing).1.symm
      exact hcond ⟨hqlt, hchar⟩
    · have hrq' : r ≤ q := by omega
      by_cases hr0 : r = 0
      · rw [hr0]
        exact Nat.zero_le _
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
        have hpre : isSuffix (P.take (r - 1)) (P.take q) :=
          suffix_dropLast_of_snoc P (P.take q) r a hrpos hr' hsuf'
        have hchar : P.getD (r - 1) default = a :=
          suffix_snoc_char_eq P q r a hrpos hr' hsuf'
        have hsuf_t : suffixTest (P.take (r - 1)) (P.take q) = true :=
          (suffixTest_eq_isSuffix _ _).mpr hpre
        have hchar_t : (P.getD (r - 1) default == a) = true := beq_iff_eq.mpr hchar
        have hcand : (suffixTest (P.take (r - 1)) (P.take q) && (P.getD (r - 1) default == a)) = true := by
          rw [hsuf_t, hchar_t]
          rfl
        have hmax : r - 1 ≤ prefixMatchAux P q a (q - 1) :=
          prefixMatchAux_maximal P q a (q - 1) (r - 1) (by omega) hsuf_t hchar_t
        have hchar_k : (P.getD (prefixMatchAux P q a (q - 1)) default == a) = true :=
          prefixMatchAux_found P q a (q - 1) ⟨r - 1, by omega, hcand⟩
        have hpm : prefixMatch P q a = prefixMatchAux P q a (q - 1) + 1 := by
          rw [prefixMatch_eq]
          rw [hchar_k]
          rfl
        rw [hpm]
        omega

/-- `kmpNextSpec P q a ≤ suffixLen P (P.take q ++ [a])`: the specification
transition never exceeds the suffix function. -/
lemma spec_le_suffixLen_snoc (P : Text α) (q : ℕ) (a : α) (hP : 0 < P.length) (hq : q ≤ P.length) :
    kmpNextSpec P q a ≤ suffixLen P (P.take q ++ [a]) := by
  unfold kmpNextSpec
  by_cases hcond : q < P.length ∧ P.getD q default = a
  · rw [if_pos hcond]
    rcases hcond with ⟨hqlt, hchar⟩
    have htake0 : P.take (q + 1) = P.take q ++ [P.getD q default] := by
      rw [List.take_succ]
      congr 1
      rw [List.getD_eq_getElem P default (by omega : q < P.length)]
      simp
    have htake : P.take (q + 1) = P.take q ++ [a] := by
      rw [htake0, hchar]
    have hsuf : isSuffix (P.take (q + 1)) (P.take q ++ [a]) := by
      rw [htake]
      exact isSuffix_self _
    have hk : q + 1 ≤ P.length := by omega
    exact suffixLen_maximal P (P.take q ++ [a]) (q + 1) hk hsuf
  · rw [if_neg hcond]
    by_cases h0 : prefixMatch P q a = 0
    · rw [h0]
      exact Nat.zero_le _
    · have hkchar : (P.getD (prefixMatchAux P q a (q - 1)) default == a) = true := by
        by_contra hneg
        have hf : (P.getD (prefixMatchAux P q a (q - 1)) default == a) = false := by
          cases hh : (P.getD (prefixMatchAux P q a (q - 1)) default == a)
          · rfl
          · exact (hneg hh).elim
        have : prefixMatch P q a = 0 := by
          rw [prefixMatch_eq]
          rw [hf]
          rfl
        exact h0 this
      have hkchar' : P.getD (prefixMatchAux P q a (q - 1)) default = a := beq_iff_eq.mp hkchar
      have hksuf : isSuffix (P.take (prefixMatchAux P q a (q - 1))) (P.take q) :=
        (suffixTest_eq_isSuffix _ _).mp (prefixMatchAux_satisfies P q a (q - 1))
      have hkle : prefixMatchAux P q a (q - 1) ≤ q - 1 := prefixMatchAux_le P q a (q - 1)
      have hkltP : prefixMatchAux P q a (q - 1) < P.length := by omega
      have htake0 : P.take (prefixMatchAux P q a (q - 1) + 1) = P.take (prefixMatchAux P q a (q - 1)) ++ [P.getD (prefixMatchAux P q a (q - 1)) default] := by
        rw [List.take_succ]
        congr 1
        rw [List.getD_eq_getElem P default (by omega : prefixMatchAux P q a (q - 1) < P.length)]
        simp
      have htake : P.take (prefixMatchAux P q a (q - 1) + 1) = P.take (prefixMatchAux P q a (q - 1)) ++ [a] := by
        rw [htake0, hkchar']
      have hsuf1 : isSuffix (P.take (prefixMatchAux P q a (q - 1) + 1)) (P.take q ++ [a]) := by
        rw [htake]
        exact suffix_append_right hksuf
      have hk1 : prefixMatchAux P q a (q - 1) + 1 ≤ P.length := by omega
      have hle : prefixMatchAux P q a (q - 1) + 1 ≤ suffixLen P (P.take q ++ [a]) :=
        suffixLen_maximal P (P.take q ++ [a]) (prefixMatchAux P q a (q - 1) + 1) hk1 hsuf1
      have hpm : prefixMatch P q a = prefixMatchAux P q a (q - 1) + 1 := by
        rw [prefixMatch_eq]
        rw [hkchar]
        rfl
      rw [hpm]
      exact hle

/-- The transition `δ(q, a)` equals the specification transition: `q + 1` when
`q < |P|` and `P[q] = a`, and `prefixMatch P q a` otherwise. -/
lemma delta_spec (P : Text α) (q : ℕ) (a : α) (hP : 0 < P.length) (hq : q ≤ P.length) :
    delta P q a = kmpNextSpec P q a := by
  unfold delta
  exact le_antisymm (suffixLen_snoc_le_spec P q a hq) (spec_le_suffixLen_snoc P q a hP hq)

/-- The executable KMP step computes exactly the automaton transition `δ`. -/
lemma kmpStep_eq_delta (P : Text α) (π : List ℕ) (q : ℕ) (a : α)
    (hP : 0 < P.length)
    (hinv : ∀ i, π.getD i 0 < i + 1)
    (hπ : ∀ i, i < P.length → π.getD i 0 = prefixLen P (i + 1))
    (hq : q ≤ P.length) :
    kmpStep P π q a hinv = delta P q a := by
  rw [delta_spec P q a hP hq]
  by_cases hqlt : q < P.length
  · have hqne : q ≠ P.length := by omega
    unfold kmpStep kmpNextSpec
    rw [if_neg hqne]
    by_cases hchar : P.getD q default = a
    · rw [if_pos ⟨hqlt, hchar⟩]
      have hff : failureFollow P π a q hinv = q := failureFollow_eq_self_of_char P π a q hinv hchar
      rw [hff]
      unfold kmpAdvance
      rw [if_pos hchar]
    · rw [if_neg (by intro h; exact hchar h.2)]
      have hπq : ∀ i, i < q → π.getD i 0 = prefixLen P (i + 1) := by
        intro i hi
        exact hπ i (by omega)
      have hff : failureFollow P π a q hinv = prefixMatchAux P q a (q - 1) :=
        failureFollow_eq_prefixMatchAux_top_of_ne P π a q hinv hπq hchar
      rw [hff]
      exact kmpAdvance_eq_prefixMatch P q a
  · have hqe : q = P.length := by omega
    subst q
    unfold kmpStep kmpNextSpec
    rw [if_pos rfl]
    rw [if_neg (by intro h; omega)]
    have hπm : π.getD (P.length - 1) 0 = prefixLen P P.length := by
      have h := hπ (P.length - 1) (by omega)
      rwa [Nat.sub_add_cancel hP] at h
    have hff : failureFollow P π a (prefixLen P P.length) hinv = prefixMatchAux P P.length a (P.length - 1) :=
      failureFollow_from_prefixLen_eq P π a P.length hinv hπ hP
    rw [hπm, hff]
    exact kmpAdvance_eq_prefixMatch P P.length a

/-- The KMP scan equation across one consumed character. -/
lemma kmpScan_cons (P : Text α) (π : List ℕ) (m : ℕ) (scanned : Text α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (c : α) (T : Text α) :
    kmpScan P π m scanned q hinv (c :: T)
      = (if q == m then [scanned.length - m] else [])
          ++ kmpScan P π m (scanned ++ [c]) (kmpStep P π q c hinv) hinv T := by
  by_cases h : q == m <;> simp [kmpScan, h]

/-- The KMP scan agrees with the finite-automaton scan when `π` is the correct
prefix-function array. -/
lemma kmpScan_eq_dfaScan (P : Text α) (π : List ℕ) (hP : 0 < P.length)
    (hπ : ∀ i, i < P.length → π.getD i 0 = prefixLen P (i + 1))
    (hinv : ∀ i, π.getD i 0 < i + 1) :
    ∀ (T scanned : Text α) (q : ℕ), q ≤ P.length →
      kmpScan P π P.length scanned q hinv T = dfaScan P P.length scanned q T := by
  intro T scanned q hq
  induction T generalizing scanned q with
  | nil =>
      rfl
  | cons c T ih =>
      have hstep : kmpStep P π q c hinv = delta P q c := kmpStep_eq_delta P π q c hP hinv hπ hq
      have hq' : kmpStep P π q c hinv ≤ P.length := by
        rw [hstep]
        unfold delta
        exact suffixLen_le P (P.take q ++ [c])
      rw [kmpScan_cons P π P.length scanned q hinv c T]
      rw [dfaScan_cons P P.length scanned q c T]
      rw [ih (scanned ++ [c]) (kmpStep P π q c hinv) hq']
      rw [hstep]

/--
**Correctness of the Knuth–Morris–Pratt matcher.**  `kmpMatcher P T` returns
exactly the shifts that `naiveMatcher T P` returns, for every pattern and text
(CLRS §32.4).
-/
theorem kmpMatcher_correct (P T : Text α) : kmpMatcher P T = naiveMatcher T P := by
  unfold kmpMatcher
  by_cases hP0 : P.length = 0
  · have hnil : P = [] := List.eq_nil_of_length_eq_zero hP0
    subst P
    simp [naiveMatcher_empty]
  · have hP : 0 < P.length := Nat.pos_of_ne_zero hP0
    have hscan := kmpScan_eq_dfaScan P (computePrefixFunction P) hP
      (by intro i hi; exact computePrefixFunction_correct P i hi)
      (computePrefixFunction_inv P)
    have hsc : kmpScan P (computePrefixFunction P) P.length [] 0 (computePrefixFunction_inv P) T
        = dfaScan P P.length [] 0 T := hscan T [] 0 (by omega)
    rw [hsc]
    simp [hP0]
    simpa [dfaMatcher] using dfaMatcher_correct P T

/-- Every shift returned by the KMP matcher is a valid match. -/
theorem kmpMatcher_sound (P T : Text α) (s : ℕ) (h : s ∈ kmpMatcher P T) : matchesAt T P s := by
  rw [kmpMatcher_correct] at h
  exact naiveMatcher_sound T P s h

/-- Every valid match is returned by the KMP matcher. -/
theorem kmpMatcher_complete (P T : Text α) (s : ℕ) (h : matchesAt T P s) : s ∈ kmpMatcher P T := by
  rw [kmpMatcher_correct]
  exact naiveMatcher_complete T P s h

/-! ## Costed KMP

The functions below instrument the executable KMP operations with an abstract
unit control-step count: one unit per failure-link traversal plus one unit per
character processed.  The metric charges the potentially super-constant part of
the algorithm — the `while q > 0 ∧ P[q] ≠ c` fallback loop — so that a linear
bound on this metric is a real statement about the executable scan.  Erasure
theorems (`*_result`) show the costed functions project to the plain
executables above.
-/

/-- `failureFollow` paired with the number of failure-link traversals. -/
def failureFollowWithCost (P : Text α) (π : List ℕ) (c : α) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) : ℕ × ℕ :=
  if hk : k = 0 then (0, 0)
  else if (P.getD k default) = c then (k, 0)
  else
    let r := failureFollowWithCost P π c (π.getD (k - 1) 0) hinv
    (r.1, r.2 + 1)
termination_by k
decreasing_by
  simp_wf
  have hpos : 0 < k := Nat.pos_of_ne_zero hk
  have hk' : (k - 1) + 1 = k := by omega
  simpa [hk'] using hinv (k - 1)

/-- Erasing the cost recovers `failureFollow`. -/
lemma failureFollowWithCost_result (P : Text α) (π : List ℕ) (c : α) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) :
    (failureFollowWithCost P π c k hinv).1 = failureFollow P π c k hinv := by
  refine Nat.strong_induction_on k ?_
  intro k ih
  rw [failureFollowWithCost, failureFollow.eq_1]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    by_cases hc : P[k]?.getD default = c
    · simp [hc]
    · simp [hc]
      exact ih (π[k - 1]?.getD 0) (by
        have hpos : 0 < k := Nat.pos_of_ne_zero hk
        have h := hinv (k - 1)
        have hk' : (k - 1) + 1 = k := by omega
        simpa [hk'] using h)

/-- The fallback cost plus the final state never exceeds the initial state. -/
lemma failureFollowWithCost_cost_add_le (P : Text α) (π : List ℕ) (c : α) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) :
    (failureFollowWithCost P π c k hinv).2 + (failureFollowWithCost P π c k hinv).1 ≤ k := by
  refine Nat.strong_induction_on k ?_
  intro k ih
  rw [failureFollowWithCost]
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, if_false]
    by_cases hc : P[k]?.getD default = c
    · simp [hc]
    · simp [hc]
      have hlt : π[k - 1]?.getD 0 < k := by
        have hpos : 0 < k := Nat.pos_of_ne_zero hk
        have h := hinv (k - 1)
        have hk' : (k - 1) + 1 = k := by omega
        simpa [hk'] using h
      have hih := ih (π[k - 1]?.getD 0) hlt
      omega

/-- `computePrefixGo` paired with its unit cost and the final failure state. -/
def computePrefixGoWithCost (P : Text α) (π : List ℕ) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hk_lt : k < π.length) : Text α → List ℕ × ℕ × ℕ
  | [] => (π, 0, k)
  | c :: rest =>
      let k' := (failureFollowWithCost P π c k hinv).1
      let cf := (failureFollowWithCost P π c k hinv).2
      let k'' := if (P.getD k' default) = c then k' + 1 else 0
      have hk'le : k' ≤ k := by
        have hcost := failureFollowWithCost_cost_add_le P π c k hinv
        omega
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
      let r := computePrefixGoWithCost P (π ++ [k'']) k'' hinv' hk''lt rest
      (r.1, cf + 1 + r.2.1, r.2.2)

/-- Erasing the cost recovers `computePrefixGo`. -/
lemma computePrefixGoWithCost_result (P : Text α) (π : List ℕ) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hk_lt : k < π.length) (rest : Text α) :
    (computePrefixGoWithCost P π k hinv hk_lt rest).1 = computePrefixGo P π k hinv hk_lt rest := by
  induction rest generalizing π k hinv hk_lt with
  | nil => simp [computePrefixGoWithCost, computePrefixGo]
  | cons c rest ih =>
      simp [computePrefixGoWithCost, computePrefixGo, failureFollowWithCost_result, ih]

/-- The amortized potential invariant: `cost + final_k ≤ 2 · rest.length + k`. -/
lemma computePrefixGoWithCost_potential (P : Text α) (π : List ℕ) (k : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (hk_lt : k < π.length) (rest : Text α) :
    (computePrefixGoWithCost P π k hinv hk_lt rest).2.1
        + (computePrefixGoWithCost P π k hinv hk_lt rest).2.2 ≤ 2 * rest.length + k := by
  induction rest generalizing π k hinv hk_lt with
  | nil => simp [computePrefixGoWithCost]
  | cons c rest ih =>
      rw [computePrefixGoWithCost]
      let k' := (failureFollowWithCost P π c k hinv).1
      let cf := (failureFollowWithCost P π c k hinv).2
      let k'' := if (P.getD k' default) = c then k' + 1 else 0
      have hk'le : k' ≤ k := by
        have hcost := failureFollowWithCost_cost_add_le P π c k hinv
        omega
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
      have hcost := failureFollowWithCost_cost_add_le P π c k hinv
      have hih := ih (π ++ [k'']) k'' hinv' hk''lt
      have hk''le' : k'' ≤ k' + 1 := by
        unfold k''
        split <;> omega
      change cf + 1 + (computePrefixGoWithCost P (π ++ [k'']) k'' hinv' hk''lt rest).2.1
          + (computePrefixGoWithCost P (π ++ [k'']) k'' hinv' hk''lt rest).2.2 ≤ 2 * (rest.length + 1) + k
      omega

/-- `computePrefixFunction` paired with its preprocessing cost. -/
def computePrefixFunctionWithCost (P : Text α) : List ℕ × ℕ :=
  match P with
  | [] => ([], 0)
  | a :: as =>
      let r := computePrefixGoWithCost P [0] 0 (by intro i; simp) (by simp) as
      (r.1, r.2.1)

/-- Erasing the cost recovers `computePrefixFunction`. -/
lemma computePrefixFunctionWithCost_result (P : Text α) :
    (computePrefixFunctionWithCost P).1 = computePrefixFunction P := by
  cases P with
  | nil => simp [computePrefixFunctionWithCost, computePrefixFunction]
  | cons a as =>
      simp [computePrefixFunctionWithCost, computePrefixFunction]
      exact computePrefixGoWithCost_result (a :: as) [0] 0 (by intro i; simp) (by simp) as

/-- The prefix-function construction costs at most `2 · |P|` steps. -/
theorem computePrefixFunctionWithCost_cost_le (P : Text α) :
    (computePrefixFunctionWithCost P).2 ≤ 2 * P.length := by
  cases P with
  | nil => simp [computePrefixFunctionWithCost]
  | cons a as =>
      simp [computePrefixFunctionWithCost]
      have h := computePrefixGoWithCost_potential (a :: as) [0] 0 (by intro i; simp) (by simp) as
      omega

/-- One KMP scan step paired with its unit cost (one fallback traversal plus
one character). -/
def kmpStepWithCost (P : Text α) (π : List ℕ) (q : ℕ) (a : α)
    (hinv : ∀ i, π.getD i 0 < i + 1) : ℕ × ℕ :=
  if q = P.length then
    let r := failureFollowWithCost P π a (π.getD (P.length - 1) 0) hinv
    (if P.getD r.1 default = a then r.1 + 1 else 0, r.2 + 1)
  else
    let r := failureFollowWithCost P π a q hinv
    (if P.getD r.1 default = a then r.1 + 1 else 0, r.2 + 1)

/-- Erasing the cost recovers `kmpStep`. -/
lemma kmpStepWithCost_result (P : Text α) (π : List ℕ) (q : ℕ) (a : α)
    (hinv : ∀ i, π.getD i 0 < i + 1) :
    (kmpStepWithCost P π q a hinv).1 = kmpStep P π q a hinv := by
  unfold kmpStepWithCost kmpStep kmpAdvance
  by_cases hq : q = P.length <;> simp [hq, failureFollowWithCost_result]

/-- The scan-step cost plus the next state never exceeds `q + 2`. -/
lemma kmpStepWithCost_cost_add_le (P : Text α) (π : List ℕ) (q : ℕ) (a : α)
    (hinv : ∀ i, π.getD i 0 < i + 1) :
    (kmpStepWithCost P π q a hinv).2 + (kmpStepWithCost P π q a hinv).1 ≤ q + 2 := by
  unfold kmpStepWithCost
  by_cases hq : q = P.length
  · simp only [hq, if_true]
    have hcost := failureFollowWithCost_cost_add_le P π a (π.getD (P.length - 1) 0) hinv
    have hle : π.getD (P.length - 1) 0 ≤ q := by
      subst q
      have h := hinv (P.length - 1)
      omega
    split <;> omega
  · simp only [hq, if_false]
    have hcost := failureFollowWithCost_cost_add_le P π a q hinv
    split <;> omega

/-- The KMP scan paired with its unit cost and the final failure state. -/
def kmpScanWithCost (P : Text α) (π : List ℕ) (m : ℕ) (scanned : Text α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) : Text α → List ℕ × ℕ × ℕ
  | [] => (if q == m then [scanned.length - m] else [], 0, q)
  | c :: rest =>
      let q' := (kmpStepWithCost P π q c hinv).1
      let cstep := (kmpStepWithCost P π q c hinv).2
      let r := kmpScanWithCost P π m (scanned ++ [c]) q' hinv rest
      (if q == m then (scanned.length - m) :: r.1 else r.1, cstep + r.2.1, r.2.2)

/-- Erasing the cost recovers `kmpScan`. -/
lemma kmpScanWithCost_result (P : Text α) (π : List ℕ) (m : ℕ) (scanned : Text α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (T : Text α) :
    (kmpScanWithCost P π m scanned q hinv T).1 = kmpScan P π m scanned q hinv T := by
  induction T generalizing scanned q with
  | nil => simp [kmpScanWithCost, kmpScan]
  | cons c T ih =>
      simp only [kmpScanWithCost, kmpScan]
      rw [kmpStepWithCost_result]
      simp [ih]

/-- The amortized potential invariant of the scan: `cost + final_q ≤ 2 · |T| + q`. -/
lemma kmpScanWithCost_potential (P : Text α) (π : List ℕ) (m : ℕ) (scanned : Text α) (q : ℕ)
    (hinv : ∀ i, π.getD i 0 < i + 1) (T : Text α) :
    (kmpScanWithCost P π m scanned q hinv T).2.1
        + (kmpScanWithCost P π m scanned q hinv T).2.2 ≤ 2 * T.length + q := by
  induction T generalizing scanned q with
  | nil => simp [kmpScanWithCost]
  | cons c T ih =>
      rw [kmpScanWithCost]
      let q' := (kmpStepWithCost P π q c hinv).1
      let cstep := (kmpStepWithCost P π q c hinv).2
      have hstep := kmpStepWithCost_cost_add_le P π q c hinv
      have hih := ih (scanned ++ [c]) q'
      change cstep + (kmpScanWithCost P π m (scanned ++ [c]) q' hinv T).2.1
          + (kmpScanWithCost P π m (scanned ++ [c]) q' hinv T).2.2 ≤ 2 * (T.length + 1) + q
      omega

/-- `kmpMatcher` paired with its matching-phase cost (the prefix construction
cost is tracked separately by `computePrefixFunctionWithCost`). -/
def kmpMatcherWithCost (P T : Text α) : List ℕ × ℕ :=
  if P.length = 0 then (List.range (T.length + 1), T.length + 1)
  else
    let r := kmpScanWithCost P (computePrefixFunction P) P.length [] 0 (computePrefixFunction_inv P) T
    (r.1, r.2.1)

/-- Erasing the cost recovers `kmpMatcher`. -/
lemma kmpMatcherWithCost_result (P T : Text α) :
    (kmpMatcherWithCost P T).1 = kmpMatcher P T := by
  unfold kmpMatcherWithCost kmpMatcher
  by_cases hP0 : P.length = 0
  · simp [hP0]
  · simp [hP0]
    exact kmpScanWithCost_result P (computePrefixFunction P) P.length [] 0 (computePrefixFunction_inv P) T

/-- The matching phase costs at most `2 · |T| + 1` steps. -/
theorem kmpMatcherWithCost_cost_le (P T : Text α) :
    (kmpMatcherWithCost P T).2 ≤ 2 * T.length + 1 := by
  unfold kmpMatcherWithCost
  by_cases hP0 : P.length = 0
  · simp [hP0]
    omega
  · simp [hP0]
    have h := kmpScanWithCost_potential P (computePrefixFunction P) P.length [] 0 (computePrefixFunction_inv P) T
    omega

/-- The total deterministic KMP work: prefix construction plus scan. -/
def kmpTotalCost (P T : Text α) : ℕ :=
  (computePrefixFunctionWithCost P).2 + (kmpMatcherWithCost P T).2

/--
**KMP total cost.**  The instrumented prefix construction plus the instrumented
all-occurrences scan costs at most `2·|P| + 2·|T| + 1` control steps, i.e. the
KMP algorithm runs in linear time `O(|P| + |T|)` (CLRS §32.4).
-/
theorem kmpTotalCost_le (P T : Text α) :
    kmpTotalCost P T ≤ 2 * P.length + 2 * T.length + 1 := by
  unfold kmpTotalCost
  have hpre := computePrefixFunctionWithCost_cost_le P
  have hscan := kmpMatcherWithCost_cost_le P T
  omega

end Chapter32
end CLRS
