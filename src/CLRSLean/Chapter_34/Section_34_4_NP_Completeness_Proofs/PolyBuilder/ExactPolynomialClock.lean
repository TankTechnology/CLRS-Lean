import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Clock
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# Exact polynomial-valued clocks

The dominating clock in `PolyBuilder.Clock` is intentionally too large to be
used as an exact tableau horizon.  This file starts the exact construction.
It first appends one distinguished sentinel to the input and then repeatedly
enumerates ordered pairs.  A depth-`d` tuple therefore represents exactly
`2 ^ d` leaves drawn from `input.map some ++ [none]`.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-! ## Appending a unique sentinel -/

/-- Input symbols tagged by `some`, followed by one distinguished sentinel. -/
def sentinelInput {Γ : Type} (input : List Γ) : List (Option Γ) :=
  input.map some ++ [none]

/-- Finite control for the sentinel-appending builder. -/
inductive SentinelLabel (Γ : Type)
  | start
  | move
  | emit
  | push (symbol : Γ)
  | halt
deriving DecidableEq, Fintype

/-- Concrete builder for `input.map some ++ [none]`.  It pushes the terminal
sentinel first and then uses the standard two-reversal discipline. -/
def sentinelProgram {Γ : Type} [Fintype Γ] : Program Γ (Option Γ) := by
  classical
  exact
    { Label := SentinelLabel Γ
      main := .start
      op
        | .start => .pushOutput none .move
        | .move => .moveInputWork₁ .emit (fun _ => .move)
        | .emit => .popWork₁ .halt .push
        | .push symbol => .pushOutput (some symbol) .emit
        | .halt => .halt }

/-- Exact step count for sentinel insertion. -/
def sentinelSteps {Γ : Type} (input : List Γ) : Nat :=
  3 * input.length + 4

private def sentinelMoveCfg {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input moved : List Γ) :
    BuilderCfg (sentinelProgram (Γ := Γ)) :=
  { initialCfg (sentinelProgram (Γ := Γ)) input with
      label := some .move
      buffer₁ := buffer
      output := [none]
      work₁ := moved }

private def sentinelEmitCfg {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (work : List Γ) (output : List (Option Γ)) :
    BuilderCfg (sentinelProgram (Γ := Γ)) :=
  { initialCfg (sentinelProgram (Γ := Γ)) [] with
      label := some .emit
      buffer₁ := buffer
      output := output
      work₁ := work }

private theorem sentinel_move_eval {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (input moved : List Γ) :
    (flip Option.bind (step (sentinelProgram (Γ := Γ))))^[input.length + 1]
      (some (sentinelMoveCfg buffer input moved)) =
        some (sentinelEmitCfg none (input.reverse ++ moved) [none]) := by
  induction input generalizing buffer moved with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show (symbol :: rest).length + 1 = rest.length + 1 + 1 by simp,
        Function.iterate_succ_apply]
      change
        (flip Option.bind (step (sentinelProgram (Γ := Γ))))^[rest.length + 1]
          (some (sentinelMoveCfg (some symbol) rest (symbol :: moved))) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some symbol) (symbol :: moved)

private theorem sentinel_emit_eval {Γ : Type} [Fintype Γ]
    (buffer : Option Γ) (work : List Γ) (output : List (Option Γ)) :
    (flip Option.bind (step (sentinelProgram (Γ := Γ))))^[2 * work.length + 1]
      (some (sentinelEmitCfg buffer work output)) =
        some { haltCfg (sentinelProgram (Γ := Γ))
            (work.reverse.map some ++ output) with label := some .halt } := by
  induction work generalizing buffer output with
  | nil => rfl
  | cons symbol rest ih =>
      rw [show 2 * (symbol :: rest).length + 1 =
          (2 * rest.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step (sentinelProgram (Γ := Γ))))^[
            2 * rest.length + 1]
          (some (sentinelEmitCfg (some symbol) rest
            (some symbol :: output))) = _
      simpa [List.reverse_cons, List.map_append, List.append_assoc] using
        ih (some symbol) (some symbol :: output)

/-- Canonical exact run of the sentinel builder. -/
def sentinel_run {Γ : Type} [Fintype Γ] (input : List Γ) :
    EvalsToInTime (step (sentinelProgram (Γ := Γ)))
      (initialCfg (sentinelProgram (Γ := Γ)) input)
      (some (haltCfg (sentinelProgram (Γ := Γ)) (sentinelInput input)))
      (sentinelSteps input) := by
  have hstart : EvalsToInTime (step (sentinelProgram (Γ := Γ)))
      (initialCfg (sentinelProgram (Γ := Γ)) input)
      (some (sentinelMoveCfg none input [])) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  have hmove : EvalsToInTime (step (sentinelProgram (Γ := Γ)))
      (sentinelMoveCfg none input [])
      (some (sentinelEmitCfg none input.reverse [none]))
      (input.length + 1) := by
    exact ⟨⟨input.length + 1, by
      simpa using sentinel_move_eval (Γ := Γ) none input []⟩, le_rfl⟩
  have hemit : EvalsToInTime (step (sentinelProgram (Γ := Γ)))
      (sentinelEmitCfg none input.reverse [none])
      (some { haltCfg (sentinelProgram (Γ := Γ)) (sentinelInput input) with
        label := some .halt }) (2 * input.length + 1) := by
    refine ⟨⟨2 * input.length + 1, ?_⟩, le_rfl⟩
    simpa [sentinelInput] using
      sentinel_emit_eval (Γ := Γ) none input.reverse [none]
  have hhalt : EvalsToInTime (step (sentinelProgram (Γ := Γ)))
      { haltCfg (sentinelProgram (Γ := Γ)) (sentinelInput input) with
        label := some .halt }
      (some (haltCfg (sentinelProgram (Γ := Γ)) (sentinelInput input))) 1 := by
    exact ⟨⟨1, rfl⟩, le_rfl⟩
  let h₁ := EvalsToInTime.trans (step (sentinelProgram (Γ := Γ)))
    1 (input.length + 1) _ _ _ hstart hmove
  let h₂ := EvalsToInTime.trans (step (sentinelProgram (Γ := Γ)))
    ((input.length + 1) + 1) (2 * input.length + 1) _ _ _ h₁ hemit
  let h₃ := EvalsToInTime.trans (step (sentinelProgram (Γ := Γ)))
    ((2 * input.length + 1) + ((input.length + 1) + 1)) 1 _ _ _ h₂ hhalt
  have hsteps :
      1 + ((2 * input.length + 1) + ((input.length + 1) + 1)) =
        sentinelSteps input := by
    simp [sentinelSteps]
    omega
  rw [← hsteps]
  exact h₃

/-- Independent output contract for sentinel insertion. -/
theorem sentinel_builderOutputs {Γ : Type} [Fintype Γ] :
    BuilderOutputs (sentinelProgram (Γ := Γ)) sentinelInput sentinelSteps := by
  intro input
  exact ⟨sentinel_run input⟩

/-- Compiled output contract for sentinel insertion. -/
theorem sentinel_outputs {Γ : Type} [Fintype Γ] :
    Outputs (sentinelProgram (Γ := Γ)) sentinelInput sentinelSteps :=
  Outputs.of_builder_run sentinel_builderOutputs

/-- Linear runtime envelope for sentinel insertion. -/
noncomputable def sentinel_polyBound {Γ : Type} :
    PolyBound (@sentinelSteps Γ) where
  polynomial := 3 * Polynomial.X + 4
  bound input := by
    simp [sentinelSteps, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]

/-- Concrete polynomial-time machine appending the unique sentinel. -/
noncomputable def sentinelInput_computableInPolyTime
    (Γ : Type) [Fintype Γ] :
    _root_.Turing.TM2ComputableInPolyTime id id (@sentinelInput Γ) :=
  ComputableInPolyTime (sentinelProgram (Γ := Γ)) sentinelInput sentinelSteps
    sentinel_outputs sentinel_polyBound

/-! ## Repeated ordered-pair enumeration -/

/-- Perfect binary tuples with exactly `2 ^ depth` leaves. -/
abbrev TuplePower : Nat → Type → Type
  | 0, Γ => Γ
  | depth + 1, Γ => TuplePower depth Γ × TuplePower depth Γ

instance tuplePowerFintype {Γ : Type} [Fintype Γ] (depth : Nat) :
    Fintype (TuplePower depth Γ) := by
  induction depth with
  | zero => simpa [TuplePower] using (inferInstanceAs (Fintype Γ))
  | succ depth ih =>
      letI : Fintype (TuplePower depth Γ) := ih
      simpa [TuplePower] using
        (inferInstanceAs (Fintype (TuplePower depth Γ × TuplePower depth Γ)))

/-- Emit the ordered pair selected by one nested-loop iteration. -/
def tuplePairBody (Γ : Type) : LoopBody (Γ × Γ) (Γ × Γ) where
  emit pair := [pair]
  cost _ := 1
  emit_length_le_cost _ := le_rfl

/-- Enumerate all perfect tuples of a fixed power-of-two width. -/
def tuplePower {Γ : Type} : (depth : Nat) → List Γ → List (TuplePower depth Γ)
  | 0, input => input
  | depth + 1, input =>
      nestedLoopOutput (tuplePairBody (TuplePower depth Γ))
        (tuplePower depth input)

@[simp] theorem tuplePower_length {Γ : Type} (depth : Nat) (input : List Γ) :
    (tuplePower depth input).length = input.length ^ (2 ^ depth) := by
  induction depth with
  | zero => simp [tuplePower]
  | succ depth ih =>
      simp [tuplePower, nestedLoopOutput, tuplePairBody, ih]
      rw [← pow_add]
      congr 1
      simp only [pow_succ]
      omega

/-- Every fixed tuple depth is computed by concrete compositions of the
verified scan/copy and nested-loop machines. -/
noncomputable def tuplePower_computableInPolyTime
    {Γ : Type} [Fintype Γ] (depth : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id (@tuplePower Γ depth) := by
  induction depth with
  | zero =>
      change _root_.Turing.TM2ComputableInPolyTime id id
        (@id (List Γ))
      exact scanCopy_computableInPolyTime (Γ := Γ)
  | succ depth ih =>
      letI : Fintype (TuplePower depth Γ) := tuplePowerFintype depth
      let composed :=
        _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch ih
          (nestedLoop_computableInPolyTime
            (tuplePairBody (TuplePower depth Γ)))
      change _root_.Turing.TM2ComputableInPolyTime id id
        (fun input : List Γ =>
          nestedLoopOutput (tuplePairBody (TuplePower depth Γ))
            (tuplePower depth input))
      simpa [Function.comp_def] using Classical.choice composed

/-! ## Prefix selection and exact monomial counts -/

/-- Recognize tuples whose first `count` leaves are tagged input symbols and
whose remaining leaves are the unique sentinel.  The intended range is
`count ≤ 2 ^ depth`; the out-of-range base case is irrelevant to the public
correctness theorem. -/
def tuplePrefixMatches {Γ : Type} :
    (depth count : Nat) → TuplePower depth (Option Γ) → Bool
  | 0, 0, leaf => leaf.isNone
  | 0, _ + 1, leaf => leaf.isSome
  | depth + 1, count, tuple =>
      let half := 2 ^ depth
      if count ≤ half then
        tuplePrefixMatches depth count tuple.1 &&
          tuplePrefixMatches depth 0 tuple.2
      else
        tuplePrefixMatches depth half tuple.1 &&
          tuplePrefixMatches depth (count - half) tuple.2

/-- Filtering the row-major Cartesian square by a conjunction multiplies the
two one-dimensional filtered lengths. -/
private theorem filter_pair_row_length {α β : Type}
    (outer : α) (input : List β) (left : α → Bool) (right : β → Bool) :
    ((input.map fun inner => (outer, inner)).filter
      (fun pair => left pair.1 && right pair.2)).length =
      if left outer then (input.filter right).length else 0 := by
  induction input with
  | nil => simp
  | cons head tail ih =>
      cases hleft : left outer <;> cases hright : right head <;>
        simp [hleft, hright, ih]

private theorem filter_cartesian_length {α β : Type}
    (outerInput : List α) (innerInput : List β)
    (left : α → Bool) (right : β → Bool) :
    ((outerInput.flatMap fun outer =>
        innerInput.map fun inner => (outer, inner)).filter
      (fun pair => left pair.1 && right pair.2)).length =
      (outerInput.filter left).length *
        (innerInput.filter right).length := by
  induction outerInput with
  | nil => simp
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.filter_append, List.length_append,
        List.filter_cons, filter_pair_row_length, ih]
      cases left head <;> simp [Nat.add_mul] <;> omega

private theorem filter_nested_pair_length {α : Type}
    (input : List α) (left right : α → Bool) :
    ((nestedLoopOutput (tuplePairBody α) input).filter
      (fun pair => left pair.1 && right pair.2)).length =
      (input.filter left).length * (input.filter right).length := by
  have flatMap_singleton_eq_map {β γ : Type} (values : List β)
      (f : β → γ) : values.flatMap (fun value => [f value]) = values.map f := by
    induction values with
    | nil => rfl
    | cons head tail ih => simp [ih]
  simpa [nestedLoopOutput, tuplePairBody, flatMap_singleton_eq_map] using
    filter_cartesian_length input input left right

private theorem filter_map_some_length {Γ : Type} (input : List Γ) :
    ((input.map some).filter Option.isSome).length = input.length := by
  induction input with
  | nil => rfl
  | cons head tail ih => simp [ih]

/-- The prefix predicate selects exactly `input.length ^ count` tuples from
the sentinel-extended power tuple list.  In particular, exponent zero gives
one tuple even when the original input is empty. -/
theorem tuplePrefixMatches_count {Γ : Type} (depth count : Nat)
    (input : List Γ) (hcount : count ≤ 2 ^ depth) :
    ((tuplePower depth (sentinelInput input)).filter
      (tuplePrefixMatches depth count)).length = input.length ^ count := by
  induction depth generalizing count with
  | zero =>
      have hcount' : count ≤ 1 := by simpa using hcount
      interval_cases count <;> simp [tuplePower, sentinelInput,
        tuplePrefixMatches, filter_map_some_length]
  | succ depth ih =>
      have htotal : count ≤ 2 * 2 ^ depth := by
        calc
          count ≤ 2 ^ depth * 2 := by simpa [pow_succ] using hcount
          _ = 2 * 2 ^ depth := Nat.mul_comm _ _
      by_cases hleft : count ≤ 2 ^ depth
      · change
          ((nestedLoopOutput (tuplePairBody (TuplePower depth (Option Γ)))
            (tuplePower depth (sentinelInput input))).filter
              (tuplePrefixMatches (depth + 1) count)).length = _
        rw [show tuplePrefixMatches (depth + 1) count =
            (fun pair => tuplePrefixMatches depth count pair.1 &&
              tuplePrefixMatches depth 0 pair.2) by
            funext pair
            simp [tuplePrefixMatches, hleft]]
        rw [filter_nested_pair_length,
          ih count hleft, ih 0 (Nat.zero_le _)]
        simp
      · have hremaining : count - 2 ^ depth ≤ 2 ^ depth := by omega
        change
          ((nestedLoopOutput (tuplePairBody (TuplePower depth (Option Γ)))
            (tuplePower depth (sentinelInput input))).filter
              (tuplePrefixMatches (depth + 1) count)).length = _
        rw [show tuplePrefixMatches (depth + 1) count =
            (fun pair => tuplePrefixMatches depth (2 ^ depth) pair.1 &&
              tuplePrefixMatches depth (count - 2 ^ depth) pair.2) by
            funext pair
            simp [tuplePrefixMatches, hleft]]
        rw [filter_nested_pair_length,
          ih (2 ^ depth) (le_rfl), ih (count - 2 ^ depth) hremaining,
          ← pow_add]
        congr 1
        omega

/-! ## Exact monomial clocks -/

/-- Emit one clock token exactly for a matching prefix tuple. -/
def exactMonomialBody {Γ : Type} (depth count : Nat) :
    LoopBody (TuplePower depth (Option Γ)) Unit where
  emit tuple := if tuplePrefixMatches depth count tuple then [()] else []
  cost _ := 1
  emit_length_le_cost tuple := by
    cases tuplePrefixMatches depth count tuple <;> simp

/-- A concrete token list of exact length `input.length ^ degree`. -/
def exactMonomialClock {Γ : Type} (degree : Nat)
    (input : List Γ) : List Unit :=
  (tuplePower degree (sentinelInput input)).flatMap
    (exactMonomialBody degree degree).emit

private theorem filter_length_eq_flatMap_match {α : Type}
    (input : List α) (predicate : α → Bool) :
    (input.filter predicate).length =
      (input.flatMap fun value => if predicate value then [()] else []).length := by
  induction input with
  | nil => rfl
  | cons head tail ih =>
      cases hpredicate : predicate head <;> simp [hpredicate, ih]

@[simp] theorem exactMonomialClock_length {Γ : Type} (degree : Nat)
    (input : List Γ) :
    (exactMonomialClock degree input).length = input.length ^ degree := by
  rw [exactMonomialClock]
  change
    ((tuplePower degree (sentinelInput input)).flatMap fun tuple =>
      if tuplePrefixMatches degree degree tuple then [()] else []).length = _
  rw [← filter_length_eq_flatMap_match]
  exact tuplePrefixMatches_count degree degree input
    degree.lt_two_pow_self.le

/-- The exact monomial clock is a concrete composition: append the sentinel,
enumerate fixed-width tuples, and filter matching prefixes with a verified
bounded loop. -/
noncomputable def exactMonomialClock_computableInPolyTime
    {Γ : Type} [Fintype Γ] (degree : Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactMonomialClock Γ degree) := by
  letI : Fintype (TuplePower degree (Option Γ)) := tuplePowerFintype degree
  let sentinelThenTuples :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (sentinelInput_computableInPolyTime Γ)
      (tuplePower_computableInPolyTime (Γ := Option Γ) degree)
  let full :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice sentinelThenTuples)
      (boundedLoop_computableInPolyTime
        (exactMonomialBody (Γ := Γ) degree degree))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      (tuplePower degree (sentinelInput input)).flatMap
        (exactMonomialBody degree degree).emit)
  simpa [Function.comp_def] using Classical.choice full

/-! ## Exact polynomial clocks -/

/-- For one maximum-width tuple, concatenate the coefficient-many tokens for
every prefix length that it matches.  All loop-local work is finite because
the polynomial is fixed when the machine is constructed. -/
def exactPolynomialBody {Γ : Type} (p : Polynomial Nat) :
    LoopBody (TuplePower p.natDegree (Option Γ)) Unit where
  emit tuple :=
    (List.range (p.natDegree + 1)).flatMap fun exponent =>
      if tuplePrefixMatches p.natDegree exponent tuple then
        List.replicate (p.coeff exponent) ()
      else []
  cost tuple :=
    ((List.range (p.natDegree + 1)).flatMap fun exponent =>
      if tuplePrefixMatches p.natDegree exponent tuple then
        List.replicate (p.coeff exponent) ()
      else []).length
  emit_length_le_cost _ := le_rfl

/-- Concrete exact polynomial-valued token clock. -/
def exactPolynomialClock {Γ : Type} (p : Polynomial Nat)
    (input : List Γ) : List Unit :=
  (tuplePower p.natDegree (sentinelInput input)).flatMap
    (exactPolynomialBody p).emit

private theorem exactPolynomialBody_emit_length {Γ : Type}
    (p : Polynomial Nat) (tuple : TuplePower p.natDegree (Option Γ)) :
    ((exactPolynomialBody p).emit tuple).length =
      ((List.range (p.natDegree + 1)).map fun exponent =>
        if tuplePrefixMatches p.natDegree exponent tuple then
          p.coeff exponent
        else 0).sum := by
  rw [show (exactPolynomialBody p).emit tuple =
      (List.range (p.natDegree + 1)).flatMap fun exponent =>
        if tuplePrefixMatches p.natDegree exponent tuple then
          List.replicate (p.coeff exponent) ()
        else [] by rfl,
    List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro exponent _
  cases tuplePrefixMatches p.natDegree exponent tuple <;> simp

private theorem list_sum_commute {α β : Type}
    (outer : List α) (inner : List β) (value : α → β → Nat) :
    (outer.map fun x => (inner.map fun y => value x y).sum).sum =
      (inner.map fun y => (outer.map fun x => value x y).sum).sum := by
  have sum_map_add (values : List β) (left right : β → Nat) :
      (values.map fun y => left y + right y).sum =
        (values.map left).sum + (values.map right).sum := by
    induction values with
    | nil => rfl
    | cons head tail ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]
  induction outer with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      rw [← sum_map_add]

private theorem sum_if_true {α : Type} (input : List α)
    (predicate : α → Bool) (coefficient : Nat) :
    (input.map fun value => if predicate value then coefficient else 0).sum =
      coefficient * (input.filter predicate).length := by
  induction input with
  | nil => simp
  | cons head tail ih =>
      cases hpredicate : predicate head <;>
        simp [hpredicate, ih, Nat.mul_add, Nat.add_comm]

private theorem list_sum_range_eq_finset_sum (count : Nat)
    (value : Nat → Nat) :
    ((List.range count).map value).sum =
      ∑ index ∈ Finset.range count, value index := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.range_succ, Finset.sum_range_succ, ih]

/-- The concrete clock has exactly the value of its source polynomial on
every input, including empty input and nonzero constant terms. -/
@[simp] theorem exactPolynomialClock_length {Γ : Type}
    (p : Polynomial Nat) (input : List Γ) :
    (exactPolynomialClock p input).length = p.eval input.length := by
  let tuples := tuplePower p.natDegree (sentinelInput input)
  calc
    (exactPolynomialClock p input).length =
        (tuples.map fun tuple =>
          ((List.range (p.natDegree + 1)).map fun exponent =>
            if tuplePrefixMatches p.natDegree exponent tuple then
              p.coeff exponent
            else 0).sum).sum := by
          simp only [exactPolynomialClock, List.length_flatMap,
            exactPolynomialBody_emit_length, tuples]
    _ = ((List.range (p.natDegree + 1)).map fun exponent =>
          (tuples.map fun tuple =>
            if tuplePrefixMatches p.natDegree exponent tuple then
              p.coeff exponent
            else 0).sum).sum :=
      list_sum_commute tuples (List.range (p.natDegree + 1)) _
    _ = ((List.range (p.natDegree + 1)).map fun exponent =>
          p.coeff exponent * input.length ^ exponent).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro exponent hexponent
      rw [sum_if_true]
      congr 1
      apply tuplePrefixMatches_count
      have hexponent' : exponent ≤ p.natDegree := by
        simpa [List.mem_range] using hexponent
      exact hexponent'.trans p.natDegree.lt_two_pow_self.le
    _ = p.eval input.length := by
      rw [Polynomial.eval_eq_sum_range]
      exact list_sum_range_eq_finset_sum _ _

/-- The exact polynomial clock is computed by one fixed-depth tuple
enumerator followed by one verified bounded filter/scaling pass. -/
noncomputable def exactPolynomialClock_computableInPolyTime
    {Γ : Type} [Fintype Γ] (p : Polynomial Nat) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialClock Γ p) := by
  letI : Fintype (TuplePower p.natDegree (Option Γ)) :=
    tuplePowerFintype p.natDegree
  let sentinelThenTuples :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (sentinelInput_computableInPolyTime Γ)
      (tuplePower_computableInPolyTime (Γ := Option Γ) p.natDegree)
  let full :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice sentinelThenTuples)
      (boundedLoop_computableInPolyTime
        (exactPolynomialBody (Γ := Γ) p))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List Γ =>
      (tuplePower p.natDegree (sentinelInput input)).flatMap
        (exactPolynomialBody p).emit)
  simpa [Function.comp_def] using Classical.choice full

end CLRS.Chapter34.Turing.PolyBuilder
