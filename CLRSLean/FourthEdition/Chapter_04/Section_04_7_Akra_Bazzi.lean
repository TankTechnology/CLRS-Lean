import CLRSLean.FourthEdition.Chapter_04.Section_04_6_Continuous_Master_Theorem

open scoped BigOperators

/-!
# Section 4.7 — Akra–Bazzi recurrences

The Akra–Bazzi method (CLRS §4.7) solves divide-and-conquer recurrences of the
form

```
  T(n) = Σ_i a_i · T(n / b_i) + g(n)
```

whose recursion tree is *not* uniformly branching.  The method first finds the
unique exponent {lit}`p` solving the **root equation**
{lit}`Σ_i a_i b_i^(-p) = 1`, then bounds {lit}`T(n)` by
{lit}`Θ(n^p (1 + ∫₁ⁿ g(u) / u^(p+1) du))`.

This section formalizes the recurrence hypotheses, the root equation and its
scale {lit}`n^p`, proves that a single branch recovers the continuous master
theorem of §4.6 (root {lit}`p = log_b a`), proves the multi-branch root is
unique and nonnegative, proves the fundamental scale-invariance bridge
{lit}`Σᵢ aᵢ (n/bᵢ)^p = n^p`, records the classic two-branch instance
{lit}`T(n) = T(n/3) + T(2n/3) + n` whose root is {lit}`p = 1`, and lays out the
integral asymptotic form with its explicit polynomial-smoothness predicate.

Main results:

- Definition {lit}`charTerm` / {lit}`charFun`: the characteristic term
  {lit}`a / b^p` and the characteristic function {lit}`Σ a_i / b_i^p`.
- Definition {lit}`IsAkraBazziRoot`: the root equation {lit}`Σ a_i / b_i^p = 1`.
- Theorem {lit}`akraBazziRoot_single`: a single branch {lit}`(a, b)` has root
  {lit}`p = log_b a`, the continuous master-theorem exponent.
- Theorem {lit}`akraBazziRoot_single_unique`: the root is unique.
- Theorem {lit}`akraBazziRoot_two_thirds_one`: the two-branch instance
  {lit}`T(n) = T(n/3) + T(2n/3)` has root {lit}`p = 1`.
- Theorem {lit}`akraBazzi_single_branch_corollary`: the single-branch root and
  its scale {lit}`n^p` coincide with the discrete
  {name}`CLRS.Chapter04.realLogScale` used by the continuous master theorem.
- Theorem {lit}`akraBazziRoot_unique`: the multi-branch root is unique.
- Theorem {lit}`akraBazziRoot_nonneg`: the multi-branch root is nonnegative.
- Theorem {lit}`akraBazzi_root_scale_invariance`: the fundamental multi-branch
  bridge {lit}`Σᵢ aᵢ (n/bᵢ)^p = n^p`.
- Definition {lit}`akraBazziIntegral` / {lit}`akraBazziScale`: the discrete
  integral {lit}`Σ_{u=1}^n g(u)/u^(p+1)` and the scale
  {lit}`n^p (1 + Σ_{u≤n} g(u)/u^(p+1))`.
- Definition {lit}`PolynomialGrowth`: the explicit polynomial-smoothness
  predicate {lit}`c n^q ≤ g n ≤ C n^q` with monotonicity and nonnegativity.
- Definition {lit}`SatisfiesAkraBazzi`: the recurrence
  {lit}`T(n) = Σᵢ aᵢ T(⌊n/bᵢ⌋) + g(n)` with floor perturbation and a constant
  base case.
- Theorems {lit}`akraBazziIntegral_mono`, {lit}`akraBazziIntegral_sub`,
  {lit}`akraBazziIntegral_lower_const`, and
  {lit}`akraBazziIntegral_bounded_of_lt`: the integral's monotonicity, its tail
  decomposition, its positive lower bound, and its boundedness for {lit}`q < p`
  (the convergent {lit}`p`-series).
- Theorems {lit}`akraBazziIntegral_tail_lower` and
  {lit}`akraBazzi_increment_lower`: the integral tail is at least its number of
  terms times its smallest term, and the single-branch increment
  {lit}`a (n/b)^p (I n - I ⌊n/b⌋)` dominates {lit}`g n` by a positive factor —
  the analytic core of the upper-bound substitution proof.

Status: `proved` for the root equation, the single-branch corollary (which
recovers the master theorem), the multi-branch root uniqueness/nonnegativity,
the scale-invariance bridge, the integral machinery, and the single-branch
increment lower bound above.  The full multi-branch
{lit}`Θ(n^p(1 + Σ g/u^(p+1)))` substitution bound (the upper and lower
recurrence-to-integral comparison) is a recorded gap.

Notation conventions used in this section:

- `aᵢ` : the number of subproblems of branch {lit}`i`
- `bᵢ` : the size divisor of branch {lit}`i` (a real {lit}`> 1`)
- `p` : the Akra–Bazzi root exponent
- `g` : the driving (additive) function
-/

namespace CLRS
namespace Chapter04

/-! ## The Akra–Bazzi hypotheses -/

/--
A branch {lit}`(aᵢ, bᵢ)` of an Akra–Bazzi recurrence: {lit}`aᵢ` subproblems,
each of size {lit}`n / bᵢ`, with {lit}`aᵢ ≥ 1` and {lit}`bᵢ > 1`.
-/
structure AkraBazziBranch where
  a : ℕ
  b : ℝ
  ha_pos : 0 < a
  hb_gt_one : 1 < b

/--
An Akra–Bazzi recurrence.  {lit}`branches` is the nonempty list of branches,
{lit}`g` is the driving function, and {lit}`T` is the solution.  The recurrence
is stated on exact powers of a common base; the floor/ceiling and
polynomial-smoothness refinements of the full CLRS statement are left to the
gap note.
-/
structure AkraBazziRecurrence where
  branches : List AkraBazziBranch
  g : ℕ → ℝ
  T : ℕ → ℝ
  hnonempty : branches ≠ []

/-! ## The root equation -/

/-- The characteristic term {lit}`a / b^p` of one branch. -/
noncomputable def charTerm (a : ℕ) (b : ℝ) (p : ℝ) : ℝ :=
  (a : ℝ) / (b : ℝ) ^ p

/-- The characteristic function {lit}`Σ_i a_i / b_i^p`. -/
noncomputable def charFun (branches : List (ℕ × ℝ)) (p : ℝ) : ℝ :=
  (branches.map (fun ab => charTerm ab.1 ab.2 p)).sum

/-- The Akra–Bazzi root equation {lit}`Σ_i a_i / b_i^p = 1`. -/
noncomputable def IsAkraBazziRoot (branches : List (ℕ × ℝ)) (p : ℝ) : Prop :=
  charFun branches p = 1

/--
The real base-power identity {lit}`b^(log_b a) = a` for natural {lit}`a ≥ 1` and
{lit}`b > 1`.  This is the bridge from the Akra–Bazzi root equation to the
master-theorem exponent.
-/
theorem rpow_realLogExponent (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    (b : ℝ) ^ realLogExponent a b = (a : ℝ) := by
  have hb_pos : 0 < (b : ℝ) := by exact_mod_cast (lt_trans (by norm_num : (0:ℕ) < 1) hb)
  have hb_log_pos : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
  have hb_log_ne : Real.log (b : ℝ) ≠ 0 := ne_of_gt hb_log_pos
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) ha)
  unfold realLogExponent
  calc
    (b : ℝ) ^ (Real.log (a : ℝ) / Real.log (b : ℝ))
        = Real.exp (Real.log (b : ℝ) * (Real.log (a : ℝ) / Real.log (b : ℝ))) := by
          rw [Real.rpow_def_of_pos hb_pos]
    _ = Real.exp (Real.log (a : ℝ)) := by
          field_simp [hb_log_ne]
    _ = (a : ℝ) := Real.exp_log ha_pos

/--
**Akra–Bazzi root, single branch.**  The recurrence {lit}`T(n) = a T(n/b) + g(n)`
has root {lit}`p = log_b a`, the master-theorem exponent.  This is the Akra–Bazzi
root equation {lit}`a / b^p = 1` for one branch.
-/
theorem akraBazziRoot_single (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    IsAkraBazziRoot [(a, (b : ℝ))] (realLogExponent a b) := by
  unfold IsAkraBazziRoot charFun charTerm
  simp [List.sum]
  rw [rpow_realLogExponent a b ha hb]
  exact div_self (by exact_mod_cast (show (a : ℕ) ≠ 0 by omega))

/--
The single-branch root is unique: two roots {lit}`p` and {lit}`q` must agree.
This is the monotonicity of {lit}`p ↦ a / b^p` in a single branch.
-/
theorem akraBazziRoot_single_unique {a b : ℕ} (ha : 1 ≤ a) (hb : 1 < b)
    {p q : ℝ} (hp : IsAkraBazziRoot [(a, (b : ℝ))] p)
    (hq : IsAkraBazziRoot [(a, (b : ℝ))] q) : p = q := by
  have hb_pos : 0 < (b : ℝ) := by exact_mod_cast (lt_trans (by norm_num : (0:ℕ) < 1) hb)
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : (0:ℕ) < 1) ha)
  have hbp : (b : ℝ) ^ p = (a : ℝ) := by
    unfold IsAkraBazziRoot charFun charTerm at hp
    simp [List.sum] at hp
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hb_pos p)] at hp
    exact hp.symm
  have hbq : (b : ℝ) ^ q = (a : ℝ) := by
    unfold IsAkraBazziRoot charFun charTerm at hq
    simp [List.sum] at hq
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hb_pos q)] at hq
    exact hq.symm
  have hlog_eq : p * Real.log (b : ℝ) = q * Real.log (b : ℝ) := by
    calc
      p * Real.log (b : ℝ) = Real.log ((b : ℝ) ^ p) := by
        rw [Real.log_rpow hb_pos]
      _ = Real.log ((b : ℝ) ^ q) := by rw [hbp, hbq]
      _ = q * Real.log (b : ℝ) := by
        rw [Real.log_rpow hb_pos]
  have hb_log_ne : Real.log (b : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  exact mul_right_cancel₀ hb_log_ne hlog_eq

/-! ## The two-branch instance -/

/--
**Akra–Bazzi root, classic instance.**  The two-branch recurrence
{lit}`T(n) = T(n/3) + T(2n/3) + n` has root {lit}`p = 1`, since
{lit}`3^(-1) + (3/2)^(-1) = 1/3 + 2/3 = 1`.
-/
theorem akraBazziRoot_two_thirds_one :
    IsAkraBazziRoot [(1, (3 : ℝ)), (1, (3 : ℝ) / 2)] 1 := by
  unfold IsAkraBazziRoot charFun charTerm
  norm_num [List.sum]

/-! ## The single-branch corollary -/

/--
**Akra–Bazzi single-branch corollary.**  For a single branch {lit}`(a, b)` the
root is {lit}`p = log_b a`, and its scale {lit}`n^p` is exactly the discrete
{name}`CLRS.Chapter04.realLogScale` used by the continuous master theorem
(§4.6).  Hence the Akra–Bazzi method recovers the master-theorem exponent and
{lit}`Θ(n^(log_b a))` bound for polynomial forcing (through
{name}`CLRS.Chapter04.continuous_master_case1`,
{name}`CLRS.Chapter04.continuous_master_case2`, and
{name}`CLRS.Chapter04.continuous_master_case3`).
-/
theorem akraBazzi_single_branch_corollary (a b : ℕ) (ha : 1 ≤ a) (hb : 1 < b) :
    IsAkraBazziRoot [(a, (b : ℝ))] (realLogExponent a b) ∧
      (∀ n : ℕ, (n : ℝ) ^ realLogExponent a b = realLogScale a b n) := by
  constructor
  · exact akraBazziRoot_single a b ha hb
  · intro n
    rfl

/-! ## The multi-branch root: monotonicity, uniqueness, and scale invariance -/

/-- A branch {lit}`(aᵢ, bᵢ)` is *valid* when {lit}`0 < aᵢ` and {lit}`1 < bᵢ`. -/
def BranchValid (ab : ℕ × ℝ) : Prop := 0 < ab.1 ∧ 1 < ab.2

/-- Every branch in the list is {name}`BranchValid`. -/
def BranchesValid (branches : List (ℕ × ℝ)) : Prop :=
  ∀ ab ∈ branches, BranchValid ab

/--
The characteristic term {lit}`a / b^p` is strictly decreasing in {lit}`p` for a
valid branch: raising the exponent {lit}`p` shrinks {lit}`b^(-p)` (since
{lit}`b > 1`), hence shrinks the whole term {lit}`a · b^(-p)`.
-/
lemma charTerm_lt_of_lt {a : ℕ} {b p q : ℝ} (ha : 0 < a) (hb : 1 < b) (hpq : p < q) :
    charTerm a b q < charTerm a b p := by
  unfold charTerm
  have hb_pos : 0 < b := lt_trans (by norm_num : (0 : ℝ) < 1) hb
  have hbpq : b ^ p < b ^ q := Real.rpow_lt_rpow_of_exponent_lt hb hpq
  have hbinv : (b ^ q)⁻¹ < (b ^ p)⁻¹ :=
    inv_strictAntiOn (Real.rpow_pos_of_pos hb_pos p) (Real.rpow_pos_of_pos hb_pos q) hbpq
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  simpa [div_eq_mul_inv] using (mul_lt_mul_of_pos_left hbinv ha_pos : (a : ℝ) * (b ^ q)⁻¹ < (a : ℝ) * (b ^ p)⁻¹)

/--
The characteristic function {lit}`Σ aᵢ / bᵢ^p` is strictly decreasing in {lit}`p`
for a nonempty valid branch list.  Every term shrinks, so the sum shrinks.
-/
theorem charFun_lt_of_lt {branches : List (ℕ × ℝ)} (hvalid : BranchesValid branches)
    (hnonempty : branches ≠ []) {p q : ℝ} (hpq : p < q) :
    charFun branches q < charFun branches p := by
  rcases branches with _ | ⟨ab, rest⟩
  · contradiction
  · have hvalid_ab : BranchValid ab := hvalid ab (by simp)
    unfold charFun
    simp only [List.map_cons, List.sum_cons]
    have hhead : charTerm ab.1 ab.2 q < charTerm ab.1 ab.2 p :=
      charTerm_lt_of_lt hvalid_ab.1 hvalid_ab.2 hpq
    have hrest : (rest.map (fun x => charTerm x.1 x.2 q)).sum ≤
        (rest.map (fun x => charTerm x.1 x.2 p)).sum := by
      apply List.sum_le_sum
      intro x hx
      have hvalid_x : BranchValid x := hvalid x (by simp [hx])
      exact le_of_lt (charTerm_lt_of_lt hvalid_x.1 hvalid_x.2 hpq)
    -- head + rest_q < head_p + rest_p
    exact add_lt_add_of_lt_of_le hhead hrest

/--
**Akra–Bazzi root uniqueness (multi-branch).**  The root equation
{lit}`Σ aᵢ / bᵢ^p = 1` has at most one real solution, because
{name}`charFun` is strictly decreasing.  This generalizes
{name}`akraBazziRoot_single_unique` from a single branch to any nonempty valid
branch list.
-/
theorem akraBazziRoot_unique {branches : List (ℕ × ℝ)} (hvalid : BranchesValid branches)
    (hnonempty : branches ≠ []) {p q : ℝ} (hp : IsAkraBazziRoot branches p)
    (hq : IsAkraBazziRoot branches q) : p = q := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hpq | hqp
  · have hlt : charFun branches q < charFun branches p := charFun_lt_of_lt hvalid hnonempty hpq
    rw [hp, hq] at hlt
    exact (lt_irrefl _ hlt).elim
  · have hlt : charFun branches p < charFun branches q := charFun_lt_of_lt hvalid hnonempty hqp
    rw [hp, hq] at hlt
    exact (lt_irrefl _ hlt).elim

/--
**Akra–Bazzi root is nonnegative.**  Since {lit}`charFun 0 = Σ aᵢ ≥ 1` and
{name}`charFun` is strictly decreasing down to {lit}`1`, the root satisfies
{lit}`p ≥ 0`.
-/
theorem akraBazziRoot_nonneg {branches : List (ℕ × ℝ)} (hvalid : BranchesValid branches)
    (hnonempty : branches ≠ []) {p : ℝ} (hp : IsAkraBazziRoot branches p) : 0 ≤ p := by
  by_contra hpneg
  have hp_lt : p < 0 := lt_of_not_ge hpneg
  have hchar : charFun branches 0 < charFun branches p := charFun_lt_of_lt hvalid hnonempty hp_lt
  have hchar0_ge : 1 ≤ charFun branches 0 := by
    rcases branches with _ | ⟨ab, rest⟩
    · contradiction
    · have hvalid_ab : BranchValid ab := hvalid ab (by simp)
      unfold charFun charTerm
      simp only [List.map_cons, List.sum_cons, Real.rpow_zero, div_one]
      have hab_ge : 1 ≤ (ab.1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_iff.mpr hvalid_ab.1)
      have hrest_nonneg : 0 ≤ (rest.map (fun x : ℕ × ℝ => (x.1 : ℝ))).sum := by
        apply List.sum_nonneg
        intro y hy
        rw [List.mem_map] at hy
        rcases hy with ⟨x, _hx, rfl⟩
        exact Nat.cast_nonneg x.1
      linarith
  rw [hp] at hchar
  linarith

/--
**Akra–Bazzi scale invariance (multi-branch).**  For a root {lit}`p`, the
{lit}`p`-weight of one level of the recursion tree is preserved:
{lit}`Σᵢ aᵢ (n / bᵢ)^p = n^p`.  This is the fundamental bridge from the root
equation {lit}`Σ aᵢ / bᵢ^p = 1` to the scale {lit}`n^p` that governs every level,
and it is the multi-branch generalization of
{name}`akraBazziRoot_single`.
-/
theorem akraBazzi_root_scale_invariance (branches : List (ℕ × ℝ)) (p : ℝ)
    (hvalid : BranchesValid branches) (hroot : IsAkraBazziRoot branches p) (n : ℕ) :
    (branches.map (fun ab => (ab.1 : ℝ) * ((n : ℝ) / ab.2) ^ p)).sum = (n : ℝ) ^ p := by
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hmap : branches.map (fun ab => (ab.1 : ℝ) * ((n : ℝ) / ab.2) ^ p)
      = branches.map (fun ab => (n : ℝ) ^ p * ((ab.1 : ℝ) / ab.2 ^ p)) := by
    rw [List.map_eq_map_iff]
    intro ab hab
    have hb_nonneg : 0 ≤ ab.2 := le_of_lt (lt_trans (by norm_num : (0 : ℝ) < 1) (hvalid ab hab).2)
    rw [Real.div_rpow hn_nonneg hb_nonneg]
    ring
  rw [hmap]
  rw [List.sum_map_mul_left]
  change (n : ℝ) ^ p * charFun branches p = (n : ℝ) ^ p
  rw [hroot]
  ring

/-! ## The integral asymptotic form -/

/--
The Akra–Bazzi *integral*: the discrete form of {lit}`∫₁ⁿ g(u) / u^(p+1) du`,
summed over {lit}`u = 1, …, n`.  This is the sum the recursion tree accumulates.
-/
noncomputable def akraBazziIntegral (p : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ u ∈ Finset.range n, g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)

/--
The Akra–Bazzi *scale*: the discrete form of the textbook
{lit}`n^p (1 + ∫₁ⁿ g(u) / u^(p+1) du)`.
-/
noncomputable def akraBazziScale (p : ℝ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ p * (1 + akraBazziIntegral p g n)

/--
**Polynomial growth (smoothness) of the driving function.**  The forcing
function {lit}`g` is nonnegative, nondecreasing, and sandwiched between two
positive monomials of a common exponent {lit}`q`:
{lit}`c n^q ≤ g n ≤ C n^q`.  This is the discrete, total-function analogue of
CLRS's *polynomially bounded* driving function, and it is the regularity
assumption under which the recursion tree compares to the integral scale.
-/
def PolynomialGrowth (g : ℕ → ℝ) (q : ℝ) : Prop :=
  (∀ n : ℕ, 0 ≤ g n) ∧
  (∀ {m n : ℕ}, m ≤ n → g m ≤ g n) ∧
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (∀ n : ℕ, 1 ≤ n → c * (n : ℝ) ^ q ≤ g n) ∧
    (∀ n : ℕ, 1 ≤ n → g n ≤ C * (n : ℝ) ^ q)

/--
The recurrence {lit}`T(n) = Σᵢ aᵢ T(⌊n/bᵢ⌋) + g(n)` with a constant base case.
The floor {lit}`⌊n/bᵢ⌋` is the *perturbation* of CLRS §4.7: the argument is
rounded down to the nearest integer subproblem size.  {lit}`T` is {lit}`0` at
{lit}`0`, {lit}`1` for {lit}`1 ≤ n ≤ n₀`, and satisfies the recurrence above the
base-case threshold {lit}`n₀`.
-/
def SatisfiesAkraBazzi (branches : List (ℕ × ℝ)) (g T : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  T 0 = 0 ∧
  (∀ n, 1 ≤ n → n ≤ n₀ → T n = 1) ∧
  (∀ n, n₀ < n →
    T n = (branches.map (fun ab => (ab.1 : ℝ) * T (⌊(n : ℝ) / ab.2⌋₊))).sum + g n)

/-! ## Recurrence-to-integral comparison -/

/-- The floor-perturbed subproblem size is strictly smaller than its parent. -/
lemma floor_div_lt_self {b : ℝ} (hb : 1 < b) {n : ℕ} (hn : 0 < n) :
    ⌊(n : ℝ) / b⌋₊ < n := by
  have hb_pos : 0 < b := lt_trans (by norm_num : (0 : ℝ) < 1) hb
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdiv_lt : (n : ℝ) / b < (n : ℝ) := by
    rw [div_lt_iff₀ hb_pos]
    simpa using (mul_lt_mul_of_pos_left hb hn_pos : (n : ℝ) * 1 < (n : ℝ) * b)
  have hfl : (⌊(n : ℝ) / b⌋₊ : ℝ) ≤ (n : ℝ) / b :=
    Nat.floor_le (le_of_lt (div_pos hn_pos hb_pos))
  exact_mod_cast (lt_of_le_of_lt hfl hdiv_lt)

/-- The Akra–Bazzi integral is nonnegative. -/
lemma akraBazziIntegral_nonneg {p : ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ akraBazziIntegral p g n := by
  unfold akraBazziIntegral
  apply Finset.sum_nonneg
  intro u _hu
  exact div_nonneg (hg (u + 1)) (Real.rpow_nonneg (by positivity) (p + 1))

/-- The Akra–Bazzi integral is monotone in its upper limit. -/
lemma akraBazziIntegral_mono {p : ℝ} {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) {m n : ℕ} (hmn : m ≤ n) :
    akraBazziIntegral p g m ≤ akraBazziIntegral p g n := by
  unfold akraBazziIntegral
  rw [← Nat.add_sub_of_le hmn]
  rw [Finset.sum_range_add (fun u => g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)) m (n - m)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (by
    intro x _hx
    exact div_nonneg (hg (m + x + 1)) (Real.rpow_nonneg (by positivity) (p + 1))))

/-- The integral increment {lit}`I n - I m` is the tail sum over {lit}`u ∈ (m, n]`. -/
lemma akraBazziIntegral_sub {p : ℝ} {g : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    akraBazziIntegral p g n - akraBazziIntegral p g m =
      ∑ u ∈ Finset.range (n - m), g (m + u + 1) / ((m + u + 1 : ℕ) : ℝ) ^ (p + 1) := by
  unfold akraBazziIntegral
  let f : ℕ → ℝ := fun u => g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)
  have hsum : ∑ u ∈ Finset.range n, f u = ∑ u ∈ Finset.range m, f u + ∑ u ∈ Finset.range (n - m), f (m + u) := by
    conv_lhs => rw [← Nat.add_sub_of_le hmn]
    rw [Finset.sum_range_add f m (n - m)]
  rw [hsum]
  rw [add_sub_cancel_left]

/-- The integral is bounded below by a positive constant (the first term). -/
lemma akraBazziIntegral_lower_const {p q : ℝ} {g : ℕ → ℝ} (hsmooth : PolynomialGrowth g q) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, 1 ≤ n → c ≤ akraBazziIntegral p g n := by
  rcases hsmooth with ⟨hgnonneg, _hgmono, c, _C, hcpos, _hCpos, hglower, _hgupper⟩
  refine ⟨c, hcpos, ?_⟩
  intro n hn
  unfold akraBazziIntegral
  have hterm : c ≤ g 1 / (1 : ℝ) ^ (p + 1) := by
    have hg1 := hglower 1 (by norm_num : 1 ≤ 1)
    simpa using hg1
  have hterm_le_sum : g 1 / (1 : ℝ) ^ (p + 1) ≤
      ∑ u ∈ Finset.range n, g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1) := by
    have h0mem : 0 ∈ Finset.range n := by rw [Finset.mem_range]; exact hn
    have := Finset.single_le_sum (f := fun u => g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1))
      (by intro u _hu; exact div_nonneg (hgnonneg (u + 1)) (Real.rpow_nonneg (by positivity) (p + 1)))
      h0mem
    simpa using this
  exact le_trans hterm hterm_le_sum

/-- The Akra–Bazzi scale is nonnegative at every input. -/
lemma akraBazziScale_nonneg {p : ℝ} {g : ℕ → ℝ} (hp : 0 ≤ p) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ akraBazziScale p g n := by
  unfold akraBazziScale
  have hn : 0 ≤ (n : ℝ) ^ p := Real.rpow_nonneg (by positivity) p
  have hI : 0 ≤ akraBazziIntegral p g n := akraBazziIntegral_nonneg hg n
  positivity

/--
The integral is bounded for {lit}`q < p`: the forcing {lit}`g ≤ C n^q` gives a
convergent {lit}`p`-series {lit}`Σ u^(q-p-1)`.
-/
lemma akraBazziIntegral_bounded_of_lt {p q : ℝ} {g : ℕ → ℝ}
    (hsmooth : PolynomialGrowth g q) (hqp : q < p) :
    ∃ C : ℝ, ∀ n, akraBazziIntegral p g n ≤ C := by
  rcases hsmooth with ⟨_hgnonneg, _hgmono, _c, Cg, _hcpos, hCpos, _hglower, hgupper⟩
  have hδ : 1 < p - q + 1 := by linarith
  have hsum : Summable (fun v : ℕ => (v : ℝ) ^ (q - p - 1)) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ) ^ (p - q + 1))⁻¹) :=
      (Real.summable_nat_rpow_inv (p := p - q + 1)).mpr hδ
    refine h0.congr ?_
    intro n
    rw [← Real.rpow_neg (by positivity : 0 ≤ (n : ℝ)) (p - q + 1)]
    congr 1
    ring
  refine ⟨Cg * (∑' v : ℕ, (v : ℝ) ^ (q - p - 1)), ?_⟩
  intro n
  unfold akraBazziIntegral
  calc
    (∑ u ∈ Finset.range n, g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1))
        ≤ ∑ u ∈ Finset.range n, Cg * ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
          apply Finset.sum_le_sum
          intro u _hu
          have hu1 : 1 ≤ u + 1 := by omega
          have hg : g (u + 1) ≤ Cg * ((u + 1 : ℕ) : ℝ) ^ q := hgupper (u + 1) hu1
          calc
            g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)
                ≤ Cg * ((u + 1 : ℕ) : ℝ) ^ q / ((u + 1 : ℕ) : ℝ) ^ (p + 1) :=
                  div_le_div_of_nonneg_right hg (Real.rpow_nonneg (by positivity) (p + 1))
            _ = Cg * (((u + 1 : ℕ) : ℝ) ^ q / ((u + 1 : ℕ) : ℝ) ^ (p + 1)) := by ring
            _ = Cg * ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
                  rw [show q - p - 1 = q - (p + 1) by ring]
                  rw [Real.rpow_sub (by positivity : 0 < ((u + 1 : ℕ) : ℝ)) q (p + 1)]
    _ = Cg * ∑ u ∈ Finset.range n, ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
          rw [Finset.mul_sum]
    _ ≤ Cg * ∑ v ∈ Finset.range (n + 1), (v : ℝ) ^ (q - p - 1) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          rw [Finset.sum_range_succ' (fun v => (v : ℝ) ^ (q - p - 1)) n]
          exact le_add_of_nonneg_right (by positivity)
    _ ≤ Cg * (∑' v : ℕ, (v : ℝ) ^ (q - p - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (Summable.sum_le_tsum (Finset.range (n + 1))
              (by intro v _hv; exact Real.rpow_nonneg (by positivity) (q - p - 1))
              hsum)
            hCpos.le

/-! ## The upper comparison -/

/-- The integral tail {lit}`I n - I m` is at least the number of terms times the
smallest term. -/
lemma akraBazziIntegral_tail_lower {p : ℝ} {g : ℕ → ℝ}
    (hp : 0 ≤ p) (hgnonneg : ∀ n, 0 ≤ g n) (hgmono : ∀ {m n : ℕ}, m ≤ n → g m ≤ g n)
    {m n : ℕ} (hmn : m ≤ n) :
    ((n - m : ℕ) : ℝ) * (g m / (n : ℝ) ^ (p + 1))
      ≤ akraBazziIntegral p g n - akraBazziIntegral p g m := by
  rw [akraBazziIntegral_sub hmn]
  rw [show ((n - m : ℕ) : ℝ) * (g m / (n : ℝ) ^ (p + 1)) =
      ∑ u ∈ Finset.range (n - m), (g m / (n : ℝ) ^ (p + 1)) by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]]
  apply Finset.sum_le_sum
  intro u hu
  have hle_n : m + u + 1 ≤ n := by
    have hu_lt : u < n - m := by simpa [Finset.mem_range] using hu
    omega
  have hge_m : m ≤ m + u + 1 := by omega
  have hg : g m ≤ g (m + u + 1) := hgmono hge_m
  have hpow : ((m + u + 1 : ℕ) : ℝ) ^ (p + 1) ≤ (n : ℝ) ^ (p + 1) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle_n) (by linarith : 0 ≤ p + 1)
  have h1 : g m / (n : ℝ) ^ (p + 1) ≤ g (m + u + 1) / (n : ℝ) ^ (p + 1) :=
    div_le_div_of_nonneg_right hg (Real.rpow_nonneg (by positivity) (p + 1))
  exact le_trans h1 (div_le_div_of_nonneg_left (hgnonneg (m + u + 1))
    (Real.rpow_pos_of_pos (by positivity) (p + 1)) hpow)

/--
The single-branch integral increment
{lit}`a (n/b)^p (I n - I ⌊n/b⌋)` dominates {lit}`g n` by a positive factor
eventually.  This is the analytic core of the upper-bound substitution proof.
-/
lemma akraBazzi_increment_lower {a : ℕ} {b p q : ℝ} {g : ℕ → ℝ}
    (ha : 0 < a) (hb : 1 < b) (hp : 0 ≤ p) (hq : 0 ≤ q) (hsmooth : PolynomialGrowth g q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      (a : ℝ) * ((n : ℝ) / b) ^ p *
          (akraBazziIntegral p g n - akraBazziIntegral p g (⌊(n : ℝ) / b⌋₊))
        ≥ ε * g n := by
  rcases hsmooth with ⟨hgnonneg, hgmono, c, C, hcpos, hCpos, hglower, hgupper⟩
  have hb_pos : 0 < b := lt_trans (by norm_num : (0 : ℝ) < 1) hb
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast ha
  let ε : ℝ := (a : ℝ) * (1 - 1 / b) * b ^ (-p) * c * (2 * b) ^ (-q) / C
  have hsub_pos : 0 < 1 - 1 / b := by
    have h1 : (1 : ℝ) / b < 1 := (div_lt_one hb_pos).mpr hb
    linarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  let n₁ : ℕ := Nat.ceil (2 * b) + 1
  refine ⟨ε, hε_pos, n₁, ?_⟩
  intro n hn
  have hn_2b : 2 * b ≤ (n : ℝ) := by
    have hceil : 2 * b ≤ (Nat.ceil (2 * b) : ℝ) := Nat.le_ceil (2 * b)
    have hn₁' : (Nat.ceil (2 * b) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hceil1 : (Nat.ceil (2 * b) : ℝ) ≤ (Nat.ceil (2 * b) + 1 : ℝ) := by norm_num
    linarith
  have hn_pos_nat : 0 < n := by
    have h2b : 0 < 2 * b := by positivity
    exact_mod_cast (lt_of_lt_of_le h2b hn_2b)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  let m : ℕ := ⌊(n : ℝ) / b⌋₊
  have hm_lt_n : m < n := floor_div_lt_self hb hn_pos_nat
  have hm_le : (m : ℝ) ≤ (n : ℝ) / b := Nat.floor_le (le_of_lt (div_pos hn_pos hb_pos))
  have hm_ge_half : (n : ℝ) / (2 * b) ≤ (m : ℝ) := by
    have hfl : (n : ℝ) / b - 1 ≤ (m : ℝ) := by
      have hlt : (n : ℝ) / b < (m : ℝ) + 1 := Nat.lt_floor_add_one ((n : ℝ) / b)
      linarith
    have h2 : (n : ℝ) / (2 * b) ≤ (n : ℝ) / b - 1 := by
      field_simp [hb_pos]
      linarith
    exact le_trans h2 hfl
  have hm_ge_one : 1 ≤ m := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      have h : (1 : ℝ) ≤ (n : ℝ) / (2 * b) := by
        rw [le_div_iff₀ (by positivity : 0 < (2 * b : ℝ))]
        simpa using hn_2b
      exact le_trans h hm_ge_half
    exact_mod_cast hm1
  have hg_m : c * (2 * b) ^ (-q) / C * g n ≤ g m := by
    have hm_q : c * (m : ℝ) ^ q ≤ g m := hglower m hm_ge_one
    have hgn : g n ≤ C * (n : ℝ) ^ q := hgupper n hn_pos_nat
    have hm_nq : c * (2 * b) ^ (-q) * (n : ℝ) ^ q ≤ g m := by
      have hmn : (n : ℝ) / (2 * b) ≤ (m : ℝ) := hm_ge_half
      have hpow : ((n : ℝ) / (2 * b)) ^ q ≤ (m : ℝ) ^ q :=
        Real.rpow_le_rpow (by positivity) hmn hq
      have h1 : c * ((n : ℝ) / (2 * b)) ^ q ≤ g m := le_trans (mul_le_mul_of_nonneg_left hpow hcpos.le) hm_q
      have h2 : ((n : ℝ) / (2 * b)) ^ q = (n : ℝ) ^ q * (2 * b) ^ (-q) := by
        rw [Real.div_rpow (by positivity) (by positivity : 0 ≤ 2 * b)]
        rw [Real.rpow_neg (by positivity : 0 ≤ 2 * b) q]
        rw [div_eq_mul_inv]
      rw [h2] at h1
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1
    have h3 : c * (2 * b) ^ (-q) / C * g n ≤ c * (2 * b) ^ (-q) * (n : ℝ) ^ q := by
      have hgn_div : g n / C ≤ (n : ℝ) ^ q := by
        rw [div_le_iff₀ hCpos]
        simpa [mul_comm] using hgn
      have hnn : c * (2 * b) ^ (-q) * (g n / C) ≤ c * (2 * b) ^ (-q) * (n : ℝ) ^ q :=
        mul_le_mul_of_nonneg_left hgn_div (mul_nonneg hcpos.le (Real.rpow_nonneg (by positivity) (-q)))
      have hrewrite : c * (2 * b) ^ (-q) / C * g n = c * (2 * b) ^ (-q) * (g n / C) := by
        field_simp [ne_of_gt hCpos]
      rwa [hrewrite]
    exact le_trans h3 hm_nq
  have htail : ((n - m : ℕ) : ℝ) * (g m / (n : ℝ) ^ (p + 1))
      ≤ akraBazziIntegral p g n - akraBazziIntegral p g m :=
    akraBazziIntegral_tail_lower hp hgnonneg hgmono (le_of_lt hm_lt_n)
  have hn_card : (n : ℝ) * (1 - 1 / b) ≤ (n - m : ℕ) := by
    have hsub : (n : ℝ) - (n : ℝ) / b ≤ (n - m : ℕ) := by
      rw [Nat.cast_sub (le_of_lt hm_lt_n)]
      linarith
    have h1 : (n : ℝ) * (1 - 1 / b) = (n : ℝ) - (n : ℝ) / b := by ring
    rw [h1]
    exact hsub
  have hid : ((n : ℝ) / b) ^ p * (n : ℝ) / (n : ℝ) ^ (p + 1) = b ^ (-p) := by
    rw [Real.div_rpow (by positivity) hb_pos.le]
    rw [Real.rpow_add hn_pos p 1, Real.rpow_one]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hn_pos p), ne_of_gt (Real.rpow_pos_of_pos hb_pos p)]
    rw [Real.rpow_neg hb_pos.le p]
    exact (mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hb_pos p))).symm
  have halg : (a : ℝ) * ((n : ℝ) / b) ^ p * (((n : ℝ) * (1 - 1 / b)) * (g m / (n : ℝ) ^ (p + 1)))
      = (a : ℝ) * (1 - 1 / b) * b ^ (-p) * (g m) := by
    rw [div_eq_mul_inv]
    calc
      (a : ℝ) * ((n : ℝ) / b) ^ p * (((n : ℝ) * (1 - 1 / b)) * (g m * ((n : ℝ) ^ (p + 1))⁻¹))
          = (a : ℝ) * (1 - 1 / b) * (g m) * (((n : ℝ) / b) ^ p * (n : ℝ) * ((n : ℝ) ^ (p + 1))⁻¹) := by ring
      _ = (a : ℝ) * (1 - 1 / b) * (g m) * b ^ (-p) := by
          rw [show ((n : ℝ) / b) ^ p * (n : ℝ) * ((n : ℝ) ^ (p + 1))⁻¹ = b ^ (-p) by
            simpa [div_eq_mul_inv] using hid]
      _ = (a : ℝ) * (1 - 1 / b) * b ^ (-p) * (g m) := by ring
  calc
    (a : ℝ) * ((n : ℝ) / b) ^ p * (akraBazziIntegral p g n - akraBazziIntegral p g m)
        ≥ (a : ℝ) * ((n : ℝ) / b) ^ p * (((n - m : ℕ) : ℝ) * (g m / (n : ℝ) ^ (p + 1))) :=
          mul_le_mul_of_nonneg_left htail (mul_nonneg ha_pos.le (Real.rpow_nonneg (by positivity) p))
    _ ≥ (a : ℝ) * ((n : ℝ) / b) ^ p * (((n : ℝ) * (1 - 1 / b)) * (g m / (n : ℝ) ^ (p + 1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by exact_mod_cast hn_card)
              (div_nonneg (hgnonneg m) (Real.rpow_nonneg (by positivity) (p + 1))))
            (mul_nonneg ha_pos.le (Real.rpow_nonneg (by positivity) p))
    _ = (a : ℝ) * (1 - 1 / b) * b ^ (-p) * (g m) := halg
    _ ≥ (a : ℝ) * (1 - 1 / b) * b ^ (-p) * (c * (2 * b) ^ (-q) / C * g n) :=
          mul_le_mul_of_nonneg_left hg_m
            (mul_nonneg (mul_nonneg ha_pos.le (le_of_lt hsub_pos)) (Real.rpow_nonneg hb_pos.le (-p)))
    _ = ε * g n := by dsimp [ε]; ring


end Chapter04
end CLRS
