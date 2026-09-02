import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Macros

/-!
# Polynomial clocks for bounded builders

Cook--Levin generators must run loops whose fixed degree is inherited from
the verifier's polynomial time bound.  The basic bounded-builder macros expose
linear and quadratic loops; this module turns those two verified kernels into
clocks of arbitrarily large fixed degree by repeatedly composing the quadratic
unit loop with itself.

The construction remains machine-level throughout: every clock below is
computed by a concrete compiled TM2, and recursive clock composition uses the
proved scratch-stack composition theorem rather than a semantic shortcut.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

open _root_.Turing

/-- Emit one unit token for each input symbol. -/
def unitClockBody (Γ : Type) : LoopBody Γ Unit where
  emit := fun _ => [()]
  cost := fun _ => 1
  emit_length_le_cost := by intro; simp

/-- The linear unit clock associated with an input word. -/
def unitClock {Γ : Type} (input : List Γ) : List Unit :=
  input.flatMap (unitClockBody Γ).emit

@[simp] theorem unitClock_length {Γ : Type} (input : List Γ) :
    (unitClock input).length = input.length := by
  simp [unitClock, unitClockBody]

/-- A concrete linear-time TM2 producing one unit token per input symbol. -/
noncomputable def unitClock_computableInPolyTime (Γ : Type) [Fintype Γ] :
    TM2ComputableInPolyTime id id (@unitClock Γ) := by
  change TM2ComputableInPolyTime id id
    (fun input : List Γ => input.flatMap (unitClockBody Γ).emit)
  exact boundedLoop_computableInPolyTime (unitClockBody Γ)

/-- Emit one unit token for each ordered pair of unit-clock symbols. -/
def squareUnitClockBody : LoopBody (Unit × Unit) Unit where
  emit := fun _ => [()]
  cost := fun _ => 1
  emit_length_le_cost := by intro; simp

/-- Square a unit clock by enumerating all ordered pairs of its tokens. -/
def squareUnitClock (input : List Unit) : List Unit :=
  nestedLoopOutput squareUnitClockBody input

@[simp] theorem squareUnitClock_length (input : List Unit) :
    (squareUnitClock input).length = input.length ^ 2 := by
  simp [squareUnitClock, nestedLoopOutput, squareUnitClockBody,
    List.length_flatMap, pow_two]

/-- A concrete quadratic-time TM2 that squares a unit clock. -/
noncomputable def squareUnitClock_computableInPolyTime :
    TM2ComputableInPolyTime id id squareUnitClock := by
  change TM2ComputableInPolyTime id id
    (nestedLoopOutput squareUnitClockBody)
  exact nestedLoop_computableInPolyTime squareUnitClockBody

/-- Repeatedly square the linear clock.  Depth `d` produces
`input.length ^ (2 ^ d)` unit tokens. -/
def iteratedSquareClock {Γ : Type} : Nat → List Γ → List Unit
  | 0, input => unitClock input
  | d + 1, input => squareUnitClock (iteratedSquareClock d input)

@[simp] theorem iteratedSquareClock_length {Γ : Type}
    (d : Nat) (input : List Γ) :
    (iteratedSquareClock d input).length = input.length ^ (2 ^ d) := by
  induction d with
  | zero => simp [iteratedSquareClock]
  | succ d ih =>
      simp only [iteratedSquareClock, squareUnitClock_length, ih]
      rw [← pow_mul]
      congr 1

/-- Every fixed-depth iterated clock is computed by a concrete polynomial-time
TM2.  The recursive step is the verified composition of the previous clock
with the verified quadratic clock. -/
noncomputable def iteratedSquareClock_computableInPolyTime
    {Γ : Type} [Fintype Γ] (d : Nat) :
    TM2ComputableInPolyTime id id (@iteratedSquareClock Γ d) := by
  induction d with
  | zero =>
      simpa [iteratedSquareClock] using unitClock_computableInPolyTime Γ
  | succ d ih =>
      let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
        ih squareUnitClock_computableInPolyTime
      simpa [iteratedSquareClock, Function.comp_def] using
        Classical.choice composed

/-! ## Scaling and domination of an arbitrary fixed polynomial -/

/-- Repeat a unit token a fixed number of times for every clock token. -/
def scaleUnitClockBody (coefficient : Nat) : LoopBody Unit Unit where
  emit := fun _ => List.replicate coefficient ()
  cost := fun _ => coefficient
  emit_length_le_cost := by intro; simp

/-- Scale a unit clock by a fixed natural coefficient. -/
def scaleUnitClock (coefficient : Nat) (input : List Unit) : List Unit :=
  input.flatMap (scaleUnitClockBody coefficient).emit

@[simp] theorem scaleUnitClock_length (coefficient : Nat)
    (input : List Unit) :
    (scaleUnitClock coefficient input).length =
      coefficient * input.length := by
  simp [scaleUnitClock, scaleUnitClockBody, List.length_flatMap,
    Nat.mul_comm]

/-- Scaling a unit clock is implemented by the verified bounded-loop TM2. -/
noncomputable def scaleUnitClock_computableInPolyTime (coefficient : Nat) :
    TM2ComputableInPolyTime id id (scaleUnitClock coefficient) := by
  change TM2ComputableInPolyTime id id
    (fun input : List Unit =>
      input.flatMap (scaleUnitClockBody coefficient).emit)
  exact boundedLoop_computableInPolyTime (scaleUnitClockBody coefficient)

/-- Sum of the coefficients of a polynomial over naturals. -/
def polynomialClockCoefficient (p : Polynomial Nat) : Nat :=
  p.sum fun _ coefficient => coefficient

/-- A concrete clock large enough to dominate `p.eval input.length` on every
nonempty input.  Its exponent `2 ^ p.natDegree` is deliberately loose: the
iterated-square implementation is substantially simpler than compiling a
different nested-loop machine for every exact degree. -/
def polynomialClock {Γ : Type} (p : Polynomial Nat)
    (input : List Γ) : List Unit :=
  scaleUnitClock (polynomialClockCoefficient p)
    (iteratedSquareClock p.natDegree input)

@[simp] theorem polynomialClock_length {Γ : Type} (p : Polynomial Nat)
    (input : List Γ) :
    (polynomialClock p input).length =
      polynomialClockCoefficient p * input.length ^ (2 ^ p.natDegree) := by
  simp [polynomialClock]

/-- The clock length dominates the value of its source polynomial whenever
the input is nonempty.  Empty input is intentionally handled as a separate
finite-control branch by downstream generators. -/
theorem polynomial_eval_le_polynomialClock_length {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) (hinput : 0 < input.length) :
    p.eval input.length ≤ (polynomialClock p input).length := by
  rw [Polynomial.eval_eq_sum, polynomialClock_length]
  unfold polynomialClockCoefficient Polynomial.sum
  calc
    p.support.sum (fun exponent =>
        p.coeff exponent * input.length ^ exponent) ≤
      p.support.sum (fun exponent =>
        p.coeff exponent * input.length ^ (2 ^ p.natDegree)) := by
          apply Finset.sum_le_sum
          intro exponent hexponent
          apply Nat.mul_le_mul_left
          apply pow_le_pow_right'
          · omega
          · exact (p.le_natDegree_of_mem_supp exponent hexponent).trans
              p.natDegree.lt_two_pow_self.le
    _ = (p.support.sum fun exponent => p.coeff exponent) *
        input.length ^ (2 ^ p.natDegree) := by
          rw [Finset.sum_mul]

/-- The polynomial clock itself is computed by a concrete polynomial-time
TM2: first build the required power clock, then apply the verified fixed
scaling loop. -/
noncomputable def polynomialClock_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    TM2ComputableInPolyTime id id (@polynomialClock Γ p) := by
  change TM2ComputableInPolyTime id id
    (fun input : List Γ => scaleUnitClock (polynomialClockCoefficient p)
      (iteratedSquareClock p.natDegree input))
  let composed := TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (iteratedSquareClock_computableInPolyTime (Γ := Γ) p.natDegree)
    (scaleUnitClock_computableInPolyTime (polynomialClockCoefficient p))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
