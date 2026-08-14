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
theorem of §4.6 (root {lit}`p = log_b a`), proves the root is unique, and records
the classic two-branch instance {lit}`T(n) = T(n/3) + T(2n/3) + n` whose root is
{lit}`p = 1`.

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

Status: `proved` for the root equation, the single-branch corollary (which
recovers the master theorem), and the two-branch root instance.  The full
multi-branch {lit}`Θ(n^p(1 + ∫ g/u^(p+1)))` bound with its integral formulation
and polynomial-smoothness hypothesis is a recorded gap.

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
        have hab1 : 1 ≤ ab.1 := by omega
        exact_mod_cast hab1
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
  (∀ n, 0 ≤ g n) ∧
  (∀ {m n : ℕ}, m ≤ n → g m ≤ g n) ∧
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (∀ n, 1 ≤ n → c * (n : ℝ) ^ q ≤ g n) ∧
    (∀ n, 1 ≤ n → g n ≤ C * (n : ℝ) ^ q)

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
    rw [← mul_one (n : ℝ)]
    exact mul_lt_mul_of_pos_left hb hn_pos
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
  rw [Finset.sum_range_add (fun u => g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)) m (n - m)]
  have hm : m + (n - m) = n := Nat.add_sub_of_le hmn
  rw [hm]
  exact le_add_of_nonneg_right (akraBazziIntegral_nonneg (p := p) hg (n - m))

/-- The integral increment {lit}`I n - I m` is the tail sum over {lit}`u ∈ (m, n]`. -/
lemma akraBazziIntegral_sub {p : ℝ} {g : ℕ → ℝ} {m n : ℕ} (hmn : m ≤ n) :
    akraBazziIntegral p g n - akraBazziIntegral p g m =
      ∑ u ∈ Finset.range (n - m), g (m + u + 1) / ((m + u + 1 : ℕ) : ℝ) ^ (p + 1) := by
  unfold akraBazziIntegral
  rw [Finset.sum_range_add (fun u => g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1)) m (n - m)]
  rw [Nat.add_sub_of_le hmn]
  rw [add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro u _hu
  congr 1
  omega

/-- The integral is bounded below by a positive constant (the first term). -/
lemma akraBazziIntegral_lower_const {p : ℝ} {g : ℕ → ℝ} (hsmooth : PolynomialGrowth g q) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, 1 ≤ n → c ≤ akraBazziIntegral p g n := by
  rcases hsmooth with ⟨_hgnonneg, _hgmono, c, _C, hcpos, _hCpos, hglower, _hgupper⟩
  refine ⟨c, hcpos, ?_⟩
  intro n hn
  unfold akraBazziIntegral
  have hterm : c ≤ g 1 / (1 : ℝ) ^ (p + 1) := by
    have hg1 : c * (1 : ℝ) ^ q ≤ g 1 := hglower 1 (by norm_num)
    simpa using hg1
  have hterm_le_sum : g 1 / (1 : ℝ) ^ (p + 1) ≤
      ∑ u ∈ Finset.range n, g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1) := by
    have h0mem : 0 ∈ Finset.range n := by rw [Finset.mem_range]; exact hn
    exact Finset.single_le_sum (by
      intro u _hu
      exact div_nonneg (hsmooth.1 (u + 1)) (Real.rpow_nonneg (by positivity) (p + 1)))
      h0mem
  exact le_trans hterm hterm_le_sum

/-- The Akra–Bazzi scale is nonnegative at every input. -/
lemma akraBazziScale_nonneg {p : ℝ} {g : ℕ → ℝ} (hp : 0 ≤ p) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ akraBazziScale p g n := by
  unfold akraBazziScale
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
  have hsum : Summable (fun u : ℕ => ((u + 1 : ℕ) : ℝ) ^ (q - p - 1)) := by
    have hbase : Summable (fun n : ℕ => (n : ℝ) ^ (p - q + 1))⁻¹ :=
      (Real.summable_nat_rpow_inv (p - q + 1)).mpr hδ
    have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (p - q + 1))⁻¹ :=
      (summable_nat_add_iff 1).mp hbase
    refine hshift.congr ?_
    intro u
    rw [← Real.rpow_neg (by positivity : 0 ≤ ((u + 1 : ℕ) : ℝ)) (p - q + 1)]
    congr 1
    ring
  refine ⟨Cg * (∑' u, ((u + 1 : ℕ) : ℝ) ^ (q - p - 1)), ?_⟩
  intro n
  unfold akraBazziIntegral
  calc
    (∑ u ∈ Finset.range n, g (u + 1) / ((u + 1 : ℕ) : ℝ) ^ (p + 1))
        ≤ ∑ u ∈ Finset.range n, Cg * ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
          apply Finset.sum_le_sum
          intro u hu
          have hu1 : 1 ≤ u + 1 := by omega
          have hg : g (u + 1) ≤ Cg * ((u + 1 : ℕ) : ℝ) ^ q := hgupper (u + 1) hu1
          have hpow_pos : 0 < ((u + 1 : ℕ) : ℝ) ^ (p + 1) :=
            Real.rpow_pos_of_pos (by positivity) (p + 1)
          rw [Real.rpow_sub (by positivity) q (p + 1)]
          exact div_le_div_of_nonneg_right hg (Real.rpow_nonneg (by positivity) (p + 1))
    _ = Cg * ∑ u ∈ Finset.range n, ((u + 1 : ℕ) : ℝ) ^ (q - p - 1) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u _hu
          congr 1
          ring
    _ ≤ Cg * (∑' u, ((u + 1 : ℕ) : ℝ) ^ (q - p - 1)) := by
          exact mul_le_mul_of_nonneg_left
            (Summable.sum_le_tsum (Finset.range n)
              (by intro u hu; exact Real.rpow_nonneg (by positivity) (q - p - 1)) hsum)
            hCpos.le

/-! ## The upper comparison -/

/--
The single-step *gap* of the Akra–Bazzi scale: the scale at {lit}`n` exceeds the
weighted sum of its values at the perturbed arguments {lit}`⌊n/bᵢ⌋` by a positive
fraction of {lit}`g n`, eventually.  This is the key estimate that makes the
upper-bound substitution proof close.
-/
lemma akraBazzi_scale_gap_lower {branches : List (ℕ × ℝ)} {p q : ℝ} {g : ℕ → ℝ}
    (hvalid : BranchesValid branches) (hnonempty : branches ≠ [])
    (hp : 0 ≤ p) (hsmooth : PolynomialGrowth g q) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₁ : ℕ, ∀ n, n₁ ≤ n →
      akraBazziScale p g n -
        (branches.map (fun ab => (ab.1 : ℝ) * akraBazziScale p g (⌊(n : ℝ) / ab.2⌋₊))).sum
      ≥ ε * g n := by
  rcases hsmooth with ⟨hgnonneg, hgmono, c, C, hcpos, hCpos, hglower, hgupper⟩
  rcases List.exists_mem_of_ne_nil branches hnonempty with ⟨ab₀, hab₀_mem⟩
  have hvalid₀ : BranchValid ab₀ := hvalid ab₀ hab₀_mem
  let b₀ : ℝ := ab₀.2
  let a₀ : ℝ := ab₀.1
  have hb₀_gt_one : 1 < b₀ := hvalid₀.2
  have hb₀_pos : 0 < b₀ := lt_trans (by norm_num : (0 : ℝ) < 1) hb₀_gt_one
  have ha₀_pos : 0 < a₀ := by
    dsimp [a₀]
    exact_mod_cast hvalid₀.1
  let ε : ℝ := a₀ * c * (1 - 1 / b₀) * b₀ ^ (-p) * (2 * b₀) ^ (-q) / C
  have hsub_pos : 0 < 1 - 1 / b₀ := by
    have h1 : (1 : ℝ) / b₀ < 1 := by
      rw [div_lt_one hb₀_pos]
      exact hb₀_gt_one
    linarith
  have hε_pos : 0 < ε := by
    dsimp [ε]
    positivity
  let n₁ : ℕ := Nat.ceil (2 * b₀) + 1
  refine ⟨ε, hε_pos, n₁, ?_⟩
  intro n hn
  have hn_2b : 2 * b₀ ≤ (n : ℝ) := by
    have hceil : 2 * b₀ ≤ (Nat.ceil (2 * b₀) : ℝ) := Nat.le_ceil (2 * b₀)
    have hn_nat : Nat.ceil (2 * b₀) + 1 ≤ n := by omega
    have hn' : (Nat.ceil (2 * b₀) + 1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_nat
    exact le_trans hceil (le_trans (by linarith : (Nat.ceil (2 * b₀) : ℝ) ≤ (Nat.ceil (2 * b₀) + 1 : ℝ)) hn')
  have hn_pos : 0 < n := by
    have : 0 < (2 * b₀ : ℝ) := by positivity
    have : 0 < (n : ℝ) := lt_of_lt_of_le this hn_2b
    exact_mod_cast this
  let m₀ : ℕ := ⌊(n : ℝ) / b₀⌋₊
  have hm₀_lt_n : m₀ < n := floor_div_lt_self hb₀_gt_one hn_pos
  have hm₀_ge_half : (n : ℝ) / (2 * b₀) ≤ (m₀ : ℝ) := by
    have hfl : (n : ℝ) / b₀ - 1 ≤ (m₀ : ℝ) := by
      have hfl_le : (m₀ : ℝ) ≤ (n : ℝ) / b₀ := Nat.floor_le (le_of_lt (div_pos (by exact_mod_cast hn_pos) hb₀_pos))
      have hlt : (n : ℝ) / b₀ < (m₀ : ℝ) + 1 := Nat.lt_floor_add_one ((n : ℝ) / b₀)
      have hsub : (n : ℝ) / b₀ - 1 < (m₀ : ℝ) := by linarith
      exact le_of_lt hsub
    have h2 : (n : ℝ) / (2 * b₀) ≤ (n : ℝ) / b₀ - 1 := by
      rw [div_div_eq_div_mul, div_div_eq_div_mul]
      -- n/(2b₀) ≤ n/b₀ - 1  ⟺  n/(2b₀) + 1 ≤ n/b₀  ⟺  2b₀ ≤ n
      have : (n : ℝ) / b₀ - (n : ℝ) / (2 * b₀) = (n : ℝ) / (2 * b₀) := by
        field_simp [hb₀_pos]
        ring
      linarith [this, hn_2b]
    exact le_trans h2 hfl
  have hm₀_ge_one : 1 ≤ m₀ := by
    have : 1 ≤ (m₀ : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) / (2 * b₀) := by
        have : (2 * b₀ : ℝ) ≤ (n : ℝ) := hn_2b
        rw [le_div_iff₀ (by positivity : 0 < (2 * b₀ : ℝ))]
        exact this
      exact le_trans this hm₀_ge_half
    exact_mod_cast this
  -- The gap is bounded below by a single branch's integral increment.
  have hgap_lower : ε * g n ≤ a₀ * (n / b₀) ^ p *
      (akraBazziIntegral p g n - akraBazziIntegral p g m₀) := by
    have hincr : (1 - 1 / b₀) * c * (2 * b₀) ^ (-q) / C * g n ≤
        akraBazziIntegral p g n - akraBazziIntegral p g m₀ := by
      rw [akraBazziIntegral_sub (le_of_lt hm₀_lt_n)]
      have hcard : n - m₀ ≥ n - ⌊(n : ℝ) / b₀⌋₊ := by omega
      -- number of terms is n - m₀ ≥ n(1 - 1/b₀)
      have hn_card : (n : ℝ) * (1 - 1 / b₀) ≤ (n - m₀ : ℝ) := by
        have : (m₀ : ℝ) ≤ (n : ℝ) / b₀ := Nat.floor_le (le_of_lt (div_pos (by exact_mod_cast hn_pos) hb₀_pos))
        have : (n - m₀ : ℝ) = (n : ℝ) - (m₀ : ℝ) := by exact_mod_cast Nat.cast_sub (le_of_lt hm₀_lt_n)
        rw [this]
        linarith
      have hterm : ∀ u ∈ Finset.range (n - m₀),
          c * (2 * b₀) ^ (-q) / C * g n / (n : ℝ) ^ (p + 1)
            ≤ g (m₀ + u + 1) / ((m₀ + u + 1 : ℕ) : ℝ) ^ (p + 1) := by
        intro u hu
        have hu_lt : u < n - m₀ := by simpa [Finset.mem_range] using hu
        have hterm_le_n : (m₀ + u + 1 : ℕ) ≤ n := by omega
        have hterm_ge_m₀ : m₀ ≤ m₀ + u + 1 := by omega
        have hg_term : g m₀ ≤ g (m₀ + u + 1) := hgmono hterm_ge_m₀
        have hg_m0 : c * (2 * b₀) ^ (-q) / C * g n ≤ g m₀ := by
          have hm₀_q : c * ((m₀ : ℝ)) ^ q ≤ g m₀ := hglower m₀ hm₀_ge_one
          have hn_upper : g n ≤ C * (n : ℝ) ^ q := hgupper n hn_pos
          have hm₀_lower : (n : ℝ) / (2 * b₀) ≤ (m₀ : ℝ) := hm₀_ge_half
          have hpow : ((n : ℝ) / (2 * b₀)) ^ q ≤ (m₀ : ℝ) ^ q :=
            Real.rpow_le_rpow (by positivity) hm₀_lower (by linarith) -- needs 0 ≤ q
          sorry -- placeholder: exponent nonneg issue
        sorry
      sorry
    sorry
  sorry

/-! ## The multi-branch Akra–Bazzi theorem -/

/--
**Akra–Bazzi, multi-branch integral form.**  For a recurrence
{lit}`T(n) = Σᵢ aᵢ T(⌊n/bᵢ⌋) + g(n)` with valid branches, Akra–Bazzi root
{lit}`p`, and polynomially growing forcing {lit}`g`, the solution is
asymptotically
{lit}`Θ(n^p (1 + Σ_{u≤n} g(u) / u^(p+1)))`.

This is the textbook Theorem 4.5 with the perturbation (the floor
{lit}`⌊n/bᵢ⌋`) and the polynomial-smoothness hypothesis
({name}`PolynomialGrowth`) made explicit, and the integral realized as its
discrete exact-power sum.  The existing single-branch corollaries
({name}`akraBazziRoot_single`, {name}`akraBazzi_single_branch_corollary`)
remain as instances of the root equation.
-/
theorem akraBazzi_integral_form (branches : List (ℕ × ℝ)) (p q : ℝ) (g T : ℕ → ℝ) (n₀ : ℕ)
    (hvalid : BranchesValid branches) (hnonempty : branches ≠ [])
    (hroot : IsAkraBazziRoot branches p) (hp : 0 ≤ p)
    (hsmooth : PolynomialGrowth g q) (hT : SatisfiesAkraBazzi branches g T n₀) :
    Chapter03.isBigTheta T (akraBazziScale p g) := by
  sorry

end Chapter04
end CLRS
