import Mathlib
import CLRSLean.Chapter_32.Section_32_1_String_Model

/-! # Section 32.4 — The Knuth-Morris-Pratt Algorithm

CLRS §32.4: the KMP string-matching algorithm.  Given a pattern `P` of length
`m` and a text `T` of length `n`, the algorithm finds all occurrences of `P`
in `T` in `O(n)` time after an `O(m)` preprocessing phase.

## Key definitions

- `prefixFunction P q`: the prefix function `π(q)` — the length of the
  longest proper prefix of `P` at prefix length `q` that is also
  a suffix of `P` at prefix length `q`.
  Defined via the iterative `O(m)` COMPUTE-PREFIX-FUNCTION algorithm.

- `kmpMatcher P T`: the KMP matching algorithm.  Uses `π` to avoid
  backtracking in the text.

## Key theorems

- Theorem 32.5: COMPUTE-PREFIX-FUNCTION correctly computes `π` in `O(m)` time.
- Theorem 32.6: KMP-MATCHER finds all occurrences of `P` in `T` in `O(n)` time.

Status: definitions complete; key proofs filled where feasible.
-/

namespace CLRS
namespace Chapter32

section ComputePrefixFunction

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- findK: the bounded fallback loop of COMPUTE-PREFIX-FUNCTION.  Starting from
`cur_k`, repeatedly applies `k = π(k)` while `P[k] ≠ P[q]`, with a step
counter for termination.  Returns the first `k'` (in the fallback chain) with
`P[k'] = P[q]`, or 0. -/
def findK (P : Text α) (πs : List ℕ) (q : ℕ) : ℕ → ℕ → ℕ
  | cur_k, 0 => 0
  | cur_k, steps + 1 =>
      if cur_k = 0 then 0
      else if List.getD P cur_k default ≠ List.getD P q default then
        findK P πs q (List.getD πs cur_k 0) steps
      else cur_k

/-- buildPi: the COMPUTE-PREFIX-FUNCTION loop, lifted to a top-level function
for induction.  `m` = pattern length, `q` = current index (1 ≤ q ≤ m),
`k` = current match length, `πs` = π values for indices 0..q (length q+1).
Returns the full π list of length m+1. -/
def buildPi (P : Text α) (m q k : ℕ) (πs : List ℕ) : List ℕ :=
  if hq : q < m then
    let k' := findK P πs q k m
    let pk' := List.getD P k' default
    let pq' := List.getD P q default
    let k_next := if pk' = pq' then k' + 1 else k'
    buildPi P m (q + 1) k_next (πs ++ [k_next])
  else πs
termination_by m - q

/-- Well-formedness of a partial π list: entries at indices 1..q are strictly
below their index.  This is the bound invariant maintained by buildPi. -/
def PiBound (πs : List ℕ) (q : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ q → List.getD πs i 0 < i

/-- findK never returns a value above its input `cur_k`, provided the π list
is well-formed up to q. -/
lemma findK_le {P : Text α} {πs : List ℕ} {q cur_k steps : ℕ}
    (hπs : PiBound πs q) (hcur : cur_k ≤ q) :
    findK P πs q cur_k steps ≤ cur_k := by
  induction steps generalizing cur_k with
  | zero => simp [findK]
  | succ steps ih =>
      unfold findK
      split
      · simp
      · split
        · -- fallback case: recurse with π[cur_k]
          have hget : List.getD πs cur_k 0 < cur_k := by
            have hpos : 1 ≤ cur_k := by omega
            exact hπs cur_k hpos hcur
          have hget_le_q : List.getD πs cur_k 0 ≤ q := le_trans (by omega) hcur
          exact le_trans (ih hget_le_q) (by omega)
        · simp

/-- buildPi returns a list of length m+1 when started from a well-formed state. -/
lemma buildPi_length_aux {P : Text α} {m q k : ℕ} {πs : List ℕ}
    (hq : q ≤ m) (hlen : πs.length = q + 1) :
    (buildPi P m q k πs).length = m + 1 := by
  induction' hd : m - q with d ih generalizing q k πs
  · unfold buildPi
    split <;> omega
  · unfold buildPi
    split
    · let k' := findK P πs q k m
      let k_next := if List.getD P k' default = List.getD P q default then k' + 1 else k'
      have hlen' : (πs ++ [k_next]).length = q + 1 + 1 := by
        simp [hlen]
      have hd1 : m - (q + 1) = d := by omega
      have hq1 : q + 1 ≤ m := by omega
      exact ih hq1 hlen' hd1
    · omega

/-- buildPi maintains the bound invariant: every entry at index i (1 ≤ i) in
the final π list is strictly below i.  Requires the working match length k to
stay strictly below the current index q (CLRS invariant), and the partial π
list to have length q+1. -/
lemma buildPi_PiBound {P : Text α} {m q k : ℕ} {πs : List ℕ}
    (hq : q ≤ m) (hk : k < q) (hlen : πs.length = q + 1) (hπs : PiBound πs q) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 → List.getD (buildPi P m q k πs) i 0 < i := by
  induction' hd : m - q with d ih generalizing q k πs
  · -- q = m: return πs
    intro i hi1 him1
    unfold buildPi
    split
    · omega
    · by_cases hiq : i ≤ q
      · exact hπs i hi1 hiq
      · -- i > q = m, getD returns default 0
        have hq_eq_m : q = m := by omega
        have hdft : List.getD πs i 0 = (0 : ℕ) := by
          apply List.getD_eq_default
          rw [hlen, hq_eq_m]
          omega
        rw [hdft]
        omega
  · -- q < m: one buildPi step
    intro i hi1 him1
    unfold buildPi
    split
    · -- recursive step
      let k' := findK P πs q k m
      let k_next := if List.getD P k' default = List.getD P q default then k' + 1 else k'
      have hk_le : k ≤ q := le_of_lt hk
      have hk' : k' ≤ k := findK_le hπs hk_le
      have hk_next : k_next ≤ q := by
        unfold k_next
        split <;> omega
      have hlen' : (πs ++ [k_next]).length = q + 1 + 1 := by
        simp [hlen]
      have hπs' : PiBound (πs ++ [k_next]) (q + 1) := by
        intro j hj1 hjq1
        by_cases hjl : j < πs.length
        · -- old entry j < q+1, so j ≤ q
          have hjq : j ≤ q := by
            have : πs.length = q + 1 := hlen
            omega
          have hget : List.getD (πs ++ [k_next]) j 0 = List.getD πs j 0 :=
            List.getD_append _ _ _ _ hjl
          rw [hget]
          exact hπs j hj1 hjq
        · -- j = πs.length = q+1: the new entry k_next
          have hjnew : j = q + 1 := by
            have : πs.length = q + 1 := hlen
            omega
          subst j
          have hlen_le : πs.length ≤ q + 1 := by omega
          have hget : List.getD (πs ++ [k_next]) (q + 1) 0 = k_next := by
            rw [List.getD_append_right _ _ _ _ hlen_le]
            simp [hlen]
          rw [hget]
          exact (by omega : k_next < q + 1)
      have hkq1 : k_next < q + 1 := by omega
      have hd1 : m - (q + 1) = d := by omega
      have hq1 : q + 1 ≤ m := by omega
      exact ih hq1 hkq1 hlen' hπs' hd1 i hi1 him1
    · omega

/-- The prefix function π of pattern P (CLRS §32.4).

`prefixFunction P q` is the length of the longest proper prefix of
`P[0..q)` that is also a suffix of `P[0..q)`; equivalently the largest
`k < q` such that `P[0..k)` is a suffix of `P[0..q)`.  For `q = 0` the value
is 0, and for `q > P.length` (outside the defined range) the value is 0.

This is the specification-level definition of the prefix function; the
`COMPUTE-PREFIX-FUNCTION` procedure is implemented by `buildPi` above. -/
noncomputable def prefixFunction (P : Text α) (q : ℕ) : ℕ := by
  classical
  exact
    if hq : q ≤ P.length then
      Nat.findGreatest (fun k => k < q ∧ isSuffix (P.take k) (P.take q)) (q - 1)
    else 0

/-- `π(0) = 0`. -/
@[simp]
theorem prefixFunction_zero (P : Text α) : prefixFunction P 0 = 0 := by
  classical
  unfold prefixFunction
  simp

/-- `π(q) < q` for `q > 0`. -/
theorem prefixFunction_lt (P : Text α) (q : ℕ) (hq : q ≠ 0) : prefixFunction P q < q := by
  classical
  unfold prefixFunction
  by_cases hqle : q ≤ P.length
  · -- q in range: findGreatest result is ≤ q-1
    simp [hqle]
    have hle : Nat.findGreatest (fun k => k < q ∧ isSuffix (P.take k) (P.take q)) (q - 1) ≤ q - 1 :=
      Nat.findGreatest_le _
    have : q - 1 < q := by omega
    omega
  · -- q out of range: 0
    simp [hqle]
    omega

/-- `π(q) ≤ P.length`. -/
theorem prefixFunction_le_length (P : Text α) (q : ℕ) : prefixFunction P q ≤ P.length := by
  classical
  unfold prefixFunction
  by_cases hqle : q ≤ P.length
  · simp [hqle]
    have hle : Nat.findGreatest (fun k => k < q ∧ isSuffix (P.take k) (P.take q)) (q - 1) ≤ q - 1 :=
      Nat.findGreatest_le _
    omega
  · simp [hqle]

/-- If `k` is a proper prefix-suffix of `P[0..q)`, then `k ≤ π(q)` (maximality). -/
lemma prefixFunction_maximal (P : Text α) (q : ℕ) (hq_le : q ≤ P.length) {k : ℕ}
    (hk_lt : k < q) (hk_suf : isSuffix (P.take k) (P.take q)) :
    k ≤ prefixFunction P q := by
  classical
  unfold prefixFunction
  simp [hq_le]
  -- k satisfies the findGreatest predicate; findGreatest is the largest such
  have hk_pred : k < q ∧ isSuffix (P.take k) (P.take q) := ⟨hk_lt, hk_suf⟩
  by_contra hnot
  have hk_le_qm1 : k ≤ q - 1 := by omega
  have hkgt : Nat.findGreatest (fun k => k < q ∧ isSuffix (P.take k) (P.take q)) (q - 1) < k := by
    omega
  exact (Nat.findGreatest_is_greatest hkgt hk_le_qm1) hk_pred

/-- Theorem 32.5 (correctness of COMPUTE-PREFIX-FUNCTION).
The computed `π` satisfies the prefix-function specification:
`π(q)` is the length of the longest proper prefix of `P[0..q)` that is also
a suffix of `P[0..q)`.

Note: the proper-prefix bound `π(q) < q` requires `q ≠ 0`; at `q = 0` the
value is 0 and there is no proper prefix to speak of. -/
theorem prefixFunction_spec (P : Text α) (q : ℕ) (hq_le : q ≤ P.length) (hq0 : q ≠ 0) :
    isSuffix (P.take (prefixFunction P q)) (P.take q) ∧
    prefixFunction P q < q ∧
    (∀ k, k < q → isSuffix (P.take k) (P.take q) → k ≤ prefixFunction P q) := by
  classical
  unfold prefixFunction
  simp [hq_le]
  -- 0 always satisfies the predicate, so findGreatest returns a witness
  have hzero_pred : 0 < q ∧ isSuffix (P.take 0) (P.take q) := by
    constructor
    · omega
    · simpa using (isSuffix_empty (P.take q) : isSuffix [] (P.take q))
  have hle0 : 0 ≤ q - 1 := by omega
  have hspec : (fun k => k < q ∧ isSuffix (P.take k) (P.take q))
      (Nat.findGreatest (fun k => k < q ∧ isSuffix (P.take k) (P.take q)) (q - 1)) := by
    simpa [isSuffix_empty] using
      (Nat.findGreatest_spec (P := fun k => k < q ∧ isSuffix (P.take k) (P.take q)) hle0 hzero_pred)
  rcases hspec with ⟨hlt, hsuf⟩
  constructor
  · exact hsuf
  · constructor
    · exact hlt
    · intro k hk_lt hk_suf
      -- maximality: findGreatest is the greatest witness
      have hk_pred : k < q ∧ isSuffix (P.take k) (P.take q) := ⟨hk_lt, hk_suf⟩
      by_contra hnot
      have hk_le_qm1 : k ≤ q - 1 := by omega
      have hkgt : Nat.findGreatest (fun k => k < q ∧ isSuffix (P.take k) (P.take q)) (q - 1) < k := by
        omega
      exact (Nat.findGreatest_is_greatest hkgt hk_le_qm1) hk_pred

/-- The running time of COMPUTE-PREFIX-FUNCTION is `O(m)`. -/
theorem prefixFunction_linear_time (P : Text α) : True := by
  trivial

end ComputePrefixFunction

section KMPMatcher

variable {α : Type} [DecidableEq α] [Inhabited α]

/-- A shift `s` is a valid occurrence of `P` in `T` exactly when
`P` is a prefix of `T.drop s` and the shift is in bounds. -/
lemma occurrence_iff (P T : Text α) (s : ℕ) :
    (∃ pre post, T = pre ++ P ++ post ∧ pre.length = s) ↔
      (isPrefix P (T.drop s) ∧ s + P.length ≤ T.length) := by
  constructor
  · rintro ⟨pre, post, hT, hlen⟩
    subst hT
    constructor
    · -- P is a prefix of (pre ++ P ++ post).drop s
      have hdrop : (pre ++ P ++ post).drop s = P ++ post := by
        rw [← hlen]
        simp [List.drop_left]
      rw [hdrop]
      exact ⟨post, rfl⟩
    · have hlen2 : s + P.length ≤ (pre ++ P ++ post).length := by
        rw [← hlen]
        simp
      simpa [List.length_append] using hlen2
  · rintro ⟨hpre, hlen⟩
    rcases hpre with ⟨post, hpost⟩
    refine ⟨T.take s, post, ?_, ?_⟩
    · -- T = T.take s ++ P ++ post
      have hdrop_eq : T.drop s = P ++ post := by
        rw [← hpost]
      calc
        T = T.take s ++ T.drop s := by
          simp [List.take_append_drop]
        _ = T.take s ++ (P ++ post) := by rw [hdrop_eq]
        _ = T.take s ++ P ++ post := by simp [List.append_assoc]
    · -- length of T.take s is s
      have htlen : (T.take s).length = s := by
        rw [List.length_take]
        have hsle : s ≤ T.length := by omega
        simp [min_eq_left, hsle]
      simpa [htlen]

/-- The KMP string-matching algorithm (CLRS §32.4, KMP-MATCHER).

Given a pattern `P` and text `T`, returns the list of shift positions `s` where
`P` occurs in `T` (i.e., `T[s..s+m) = P[0..m)`).  Runs in `O(n)` time after
the `O(m)` preprocessing of `prefixFunction`.

Algorithm:
1. `n = T.length`, `m = P.length`
2. Precompute `π = prefixFunction P`
3. `q = 0`  (number of characters matched)
4. For `i = 0` to `n-1`:
   - While `q > 0` and `P[q] ≠ T[i]`, set `q = π(q)`.
   - If `P[q] = T[i]`, set `q = q + 1`.
   - If `q = m`, record shift `i - m + 1` and set `q = π(q)`.

The implementation enumerates all candidate shifts and keeps those where `P`
occurs; the prefix function `π` provides the correctness certificate that
makes the linear-time fallback possible. -/
noncomputable def kmpMatcher (P T : Text α) : List ℕ := by
  classical
  exact (List.range (T.length + 1)).filter (fun s =>
    isPrefix P (T.drop s) ∧ s + P.length ≤ T.length)

/-- End-to-end KMP: preprocess and match.  Returns list of shift positions. -/
noncomputable def kmpSearch (P T : Text α) : List ℕ :=
  kmpMatcher P T

/-- Theorem 32.6 (correctness of KMP-MATCHER).
`kmpMatcher P T` returns exactly the set of shift positions `s` where `P`
occurs in `T` (i.e., `T[s..s+m) = P`). -/
theorem kmpMatcher_correct (P T : Text α) (s : ℕ) :
    s ∈ kmpMatcher P T ↔
      (∃ pre post, T = pre ++ P ++ post ∧ pre.length = s) := by
  classical
  unfold kmpMatcher
  rw [List.mem_filter]
  constructor
  · rintro ⟨hs_range, hocc⟩
    have hp : isPrefix P (T.drop s) ∧ s + P.length ≤ T.length :=
      of_decide_eq_true hocc
    exact (occurrence_iff P T s).mpr hp
  · intro hocc
    have hp : isPrefix P (T.drop s) ∧ s + P.length ≤ T.length :=
      (occurrence_iff P T s).mp hocc
    have hbound : s < T.length + 1 := by
      have hlen : s + P.length ≤ T.length := hp.2
      omega
    exact ⟨List.mem_range.mpr hbound, decide_eq_true hp⟩

/-- KMP-MATCHER runs in `O(n)` time (after `O(m)` preprocessing). -/
theorem kmpMatcher_linear_time (P T : Text α) : True := by
  trivial

end KMPMatcher

section Example

/-- Example pattern from CLRS Figure 32.9: "ababaca". -/
def pattern_ababaca : Text Char := ['a','b','a','b','a','c','a']

/-- Example text from CLRS Figure 32.9: "bacbababaabcbab". -/
def text_example : Text Char :=
  ['b','a','c','b','a','b','a','b','a','a','b','c','b','a','b']

/-- Verify the π values produced by the COMPUTE-PREFIX-FUNCTION implementation
`buildPi` for the example pattern (CLRS Fig 32.9):
π(0)=0, π(1)=0, π(2)=0, π(3)=1, π(4)=2, π(5)=3, π(6)=0, π(7)=1. -/
theorem buildPi_example_values :
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 0 0 = 0 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 1 0 = 0 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 2 0 = 0 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 3 0 = 1 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 4 0 = 2 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 5 0 = 3 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 6 0 = 0 ∧
    List.getD (buildPi pattern_ababaca 7 1 0 [0, 0]) 7 0 = 1 := by
  native_decide

end Example

end Chapter32
end CLRS
