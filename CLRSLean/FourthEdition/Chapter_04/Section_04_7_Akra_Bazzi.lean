import CLRSLean.FourthEdition.Chapter_04.Section_04_6_Continuous_Master_Theorem

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

end Chapter04
end CLRS
