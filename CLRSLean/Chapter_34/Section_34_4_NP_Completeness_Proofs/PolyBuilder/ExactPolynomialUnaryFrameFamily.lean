import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ExactPolynomialUnaryFrame

/-!
# Exact polynomial unary-frame families

A Cook--Levin runtime script contains many unary operands derived from the
same raw input length.  This module compiles any fixed finite list of natural
polynomials into the concatenation of their delimiter-bearing unary blocks.
The construction shares one tuple enumeration across all fields and uses a
verified nested loop to group its output by a fixed finite field tag.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-! ## Shared-depth exact polynomial clocks -/

/-- A deliberately simple shared tuple depth dominating every polynomial in
the fixed family. -/
def polynomialFamilyDegree (polynomials : List (Polynomial Nat)) : Nat :=
  (polynomials.map Polynomial.natDegree).sum

/-- Every member's degree is bounded by the shared family depth. -/
theorem polynomial_natDegree_le_familyDegree
    (polynomials : List (Polynomial Nat)) (p : Polynomial Nat)
    (hp : p ∈ polynomials) :
    p.natDegree ≤ polynomialFamilyDegree polynomials := by
  induction polynomials with
  | nil => simp at hp
  | cons head tail ih =>
      simp only [List.mem_cons] at hp
      simp only [polynomialFamilyDegree, List.map_cons, List.sum_cons]
      rcases hp with rfl | hp
      · omega
      · exact (ih hp).trans (Nat.le_add_left _ _)

/-- Indexed form of the shared-depth bound used by the finite field tags. -/
theorem polynomial_get_natDegree_le_familyDegree
    (polynomials : List (Polynomial Nat))
    (index : Fin polynomials.length) :
    (polynomials.get index).natDegree ≤
      polynomialFamilyDegree polynomials :=
  polynomial_natDegree_le_familyDegree polynomials _
    (List.get_mem polynomials index)

/-- Emit the coefficient-many unit tokens for every matching prefix length,
using a tuple depth that may be larger than the polynomial's own degree. -/
def exactPolynomialAtDepthBody {Γ : Type} (depth : Nat)
    (p : Polynomial Nat) :
    LoopBody (TuplePower depth (Option Γ)) Unit where
  emit tuple :=
    (List.range (p.natDegree + 1)).flatMap fun exponent =>
      if tuplePrefixMatches depth exponent tuple then
        List.replicate (p.coeff exponent) ()
      else []
  cost tuple :=
    ((List.range (p.natDegree + 1)).flatMap fun exponent =>
      if tuplePrefixMatches depth exponent tuple then
        List.replicate (p.coeff exponent) ()
      else []).length
  emit_length_le_cost _ := le_rfl

/-- Exact polynomial token clock evaluated within a shared tuple depth. -/
def exactPolynomialAtDepthClock {Γ : Type} (depth : Nat)
    (p : Polynomial Nat) (input : List Γ) : List Unit :=
  (tuplePower depth (sentinelInput input)).flatMap
    (exactPolynomialAtDepthBody depth p).emit

/-- Length of one shared-depth tuple's coefficient-token chunk. -/
private theorem exactPolynomialAtDepthBody_emit_length {Γ : Type}
    (depth : Nat) (p : Polynomial Nat)
    (tuple : TuplePower depth (Option Γ)) :
    ((exactPolynomialAtDepthBody depth p).emit tuple).length =
      ((List.range (p.natDegree + 1)).map fun exponent =>
        if tuplePrefixMatches depth exponent tuple then
          p.coeff exponent
        else 0).sum := by
  rw [show (exactPolynomialAtDepthBody depth p).emit tuple =
      (List.range (p.natDegree + 1)).flatMap fun exponent =>
        if tuplePrefixMatches depth exponent tuple then
          List.replicate (p.coeff exponent) ()
        else [] by rfl,
    List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro exponent _
  cases tuplePrefixMatches depth exponent tuple <;> simp

/-- Commute two finite list sums without requiring an additive algebra wrapper. -/
private theorem family_list_sum_commute {α β : Type}
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

/-- A Boolean-selected constant sum is the constant times the selected count. -/
private theorem family_sum_if_true {α : Type} (input : List α)
    (predicate : α → Bool) (coefficient : Nat) :
    (input.map fun value => if predicate value then coefficient else 0).sum =
      coefficient * (input.filter predicate).length := by
  induction input with
  | nil => simp
  | cons head tail ih =>
      cases hpredicate : predicate head <;>
        simp [hpredicate, ih, Nat.mul_add, Nat.add_comm]

/-- Bridge the list-range sum used by the machine body to polynomial's finset
sum convention. -/
private theorem family_list_sum_range_eq_finset_sum (count : Nat)
    (value : Nat → Nat) :
    ((List.range count).map value).sum =
      ∑ index ∈ Finset.range count, value index := by
  induction count with
  | zero => simp
  | succ count ih =>
      simp [List.range_succ, Finset.sum_range_succ, ih]

/-- A shared depth computes exactly the polynomial value whenever it dominates
the polynomial's degree. -/
@[simp] theorem exactPolynomialAtDepthClock_length {Γ : Type}
    (depth : Nat) (p : Polynomial Nat) (input : List Γ)
    (hdegree : p.natDegree ≤ depth) :
    (exactPolynomialAtDepthClock depth p input).length =
      p.eval input.length := by
  let tuples := tuplePower depth (sentinelInput input)
  calc
    (exactPolynomialAtDepthClock depth p input).length =
        (tuples.map fun tuple =>
          ((List.range (p.natDegree + 1)).map fun exponent =>
            if tuplePrefixMatches depth exponent tuple then
              p.coeff exponent
            else 0).sum).sum := by
          simp only [exactPolynomialAtDepthClock, List.length_flatMap,
            exactPolynomialAtDepthBody_emit_length, tuples]
    _ = ((List.range (p.natDegree + 1)).map fun exponent =>
          (tuples.map fun tuple =>
            if tuplePrefixMatches depth exponent tuple then
              p.coeff exponent
            else 0).sum).sum :=
      family_list_sum_commute tuples (List.range (p.natDegree + 1)) _
    _ = ((List.range (p.natDegree + 1)).map fun exponent =>
          p.coeff exponent * input.length ^ exponent).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro exponent hexponent
      rw [family_sum_if_true]
      congr 1
      apply tuplePrefixMatches_count
      have hexponent' : exponent ≤ p.natDegree := by
        simpa [List.mem_range] using hexponent
      exact (hexponent'.trans hdegree).trans depth.lt_two_pow_self.le
    _ = p.eval input.length := by
      rw [Polynomial.eval_eq_sum_range]
      exact family_list_sum_range_eq_finset_sum _ _

/-! ## Tuple and fixed-tag loop input -/

/-- Shared tuple type for one polynomial family and source alphabet. -/
abbrev PolynomialFamilyTuple (Γ : Type)
    (polynomials : List (Polynomial Nat)) :=
  TuplePower (polynomialFamilyDegree polynomials) (Option Γ)

/-- Nested-loop input symbols: all shared tuples followed by one tag per
polynomial field. -/
abbrev PolynomialFamilyLoopSym (Γ : Type)
    (polynomials : List (Polynomial Nat)) :=
  PolynomialFamilyTuple Γ polynomials ⊕ Fin polynomials.length

/-- Convert a sentinel-terminated tuple list into tuple symbols followed by
the fixed complete tag list. -/
def polynomialFamilyLoopInputBody {Γ : Type}
    (polynomials : List (Polynomial Nat)) :
    LoopBody (Option (PolynomialFamilyTuple Γ polynomials))
      (PolynomialFamilyLoopSym Γ polynomials) where
  emit
    | some tuple => [Sum.inl tuple]
    | none => (List.finRange polynomials.length).map Sum.inr
  cost symbol :=
    match symbol with
    | some _ => 1
    | none => polynomials.length
  emit_length_le_cost symbol := by
    cases symbol <;> simp

/-- Concrete semantic tuple-plus-tag list consumed by the family nested loop. -/
def polynomialFamilyLoopInput {Γ : Type}
    (polynomials : List (Polynomial Nat))
    (tuples : List (PolynomialFamilyTuple Γ polynomials)) :
    List (PolynomialFamilyLoopSym Γ polynomials) :=
  (sentinelInput tuples).flatMap
    (polynomialFamilyLoopInputBody polynomials).emit

/-- The tuple-plus-tag builder preserves tuple order and appends every fixed
field tag in increasing order. -/
@[simp] theorem polynomialFamilyLoopInput_eq {Γ : Type}
    (polynomials : List (Polynomial Nat))
    (tuples : List (PolynomialFamilyTuple Γ polynomials)) :
    polynomialFamilyLoopInput polynomials tuples =
      tuples.map Sum.inl ++
        (List.finRange polynomials.length).map Sum.inr := by
  induction tuples with
  | nil =>
      simp [polynomialFamilyLoopInput, sentinelInput,
        polynomialFamilyLoopInputBody]
  | cons tuple tuples ih =>
      change Sum.inl tuple :: polynomialFamilyLoopInput polynomials tuples = _
      simp [ih]

/-- Tuple-plus-tag construction is a concrete sentinel appender followed by a
verified bounded relabeling loop. -/
noncomputable def polynomialFamilyLoopInput_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (polynomials : List (Polynomial Nat)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (polynomialFamilyLoopInput (Γ := Γ) polynomials) := by
  letI : Fintype (PolynomialFamilyTuple Γ polynomials) :=
    tuplePowerFintype (polynomialFamilyDegree polynomials)
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (sentinelInput_computableInPolyTime
        (PolynomialFamilyTuple Γ polynomials))
      (boundedLoop_computableInPolyTime
        (polynomialFamilyLoopInputBody (Γ := Γ) polynomials))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun tuples =>
      (sentinelInput tuples).flatMap
        (polynomialFamilyLoopInputBody polynomials).emit)
  simpa [Function.comp_def] using Classical.choice composed

/-! ## Nested-loop unary frame serialization -/

/-- Tick chunk contributed by one shared tuple to one fixed polynomial field. -/
def polynomialFamilyTupleTicks {Γ : Type}
    (polynomials : List (Polynomial Nat))
    (index : Fin polynomials.length)
    (tuple : PolynomialFamilyTuple Γ polynomials) : List UnaryFrameSym :=
  ((exactPolynomialAtDepthBody
    (polynomialFamilyDegree polynomials) (polynomials.get index)).emit tuple).map
      fun _ => .tick

/-- Pair-local body of the family serializer.  Field-tag outer rows scan all
tuples for their ticks, then use the first inner tag as their separator. -/
def exactPolynomialUnaryFrameFamilyBody {Γ : Type}
    (polynomials : List (Polynomial Nat)) :
    LoopBody
      (PolynomialFamilyLoopSym Γ polynomials ×
        PolynomialFamilyLoopSym Γ polynomials)
      UnaryFrameSym where
  emit
    | (Sum.inr index, Sum.inl tuple) =>
        polynomialFamilyTupleTicks polynomials index tuple
    | (Sum.inr _, Sum.inr marker) =>
        if marker.val = 0 then [.separator] else []
    | _ => []
  cost pair :=
    match pair with
    | (Sum.inr index, Sum.inl tuple) =>
        (polynomialFamilyTupleTicks polynomials index tuple).length
    | (Sum.inr _, Sum.inr marker) =>
        if marker.val = 0 then 1 else 0
    | _ => 0
  emit_length_le_cost pair := by
    rcases pair with ⟨outer, inner⟩
    rcases outer with tuple | index
    · rcases inner with tuple | marker <;> rfl
    · rcases inner with tuple | marker
      · rfl
      · dsimp
        by_cases hmarker : marker.val = 0 <;> simp [hmarker]

/-- All symbols contributed by the shared tuples to one field are ticks, with
exactly that field's polynomial value as their count. -/
private theorem polynomialFamilyTupleTicks_all {Γ : Type}
    (polynomials : List (Polynomial Nat))
    (index : Fin polynomials.length) (input : List Γ) :
    (tuplePower (polynomialFamilyDegree polynomials)
        (sentinelInput input)).flatMap
        (polynomialFamilyTupleTicks polynomials index) =
      List.replicate ((polynomials.get index).eval input.length) .tick := by
  let tokens := exactPolynomialAtDepthClock
    (polynomialFamilyDegree polynomials) (polynomials.get index) input
  have htokensLength : tokens.length =
      (polynomials.get index).eval input.length := by
    exact exactPolynomialAtDepthClock_length _ _ _
      (polynomial_get_natDegree_le_familyDegree polynomials index)
  have htokens : tokens = List.replicate tokens.length () := by
    exact List.eq_replicate_length.mpr fun token _ => Subsingleton.elim token ()
  unfold polynomialFamilyTupleTicks
  rw [← List.map_flatMap]
  change tokens.map (fun _ => UnaryFrameSym.tick) = _
  rw [htokens, htokensLength]
  simp

/-- The fixed tag suffix contributes exactly one separator to every nonempty
field-tag outer row. -/
private theorem polynomialFamilySeparatorRow {Γ : Type}
    (polynomials : List (Polynomial Nat))
    (index : Fin polynomials.length) :
    ((List.finRange polynomials.length).map Sum.inr).flatMap
        (fun inner =>
          (exactPolynomialUnaryFrameFamilyBody
            (Γ := Γ) polynomials).emit (Sum.inr index, inner)) =
      [.separator] := by
  cases polynomials with
  | nil => exact Fin.elim0 index
  | cons head tail =>
      simp [List.finRange_succ, exactPolynomialUnaryFrameFamilyBody]

/-- One field-tag row emits exactly its polynomial's unary block. -/
theorem exactPolynomialUnaryFrameFamily_tagRow {Γ : Type}
    (polynomials : List (Polynomial Nat))
    (index : Fin polynomials.length) (input : List Γ) :
    let tuples := tuplePower (polynomialFamilyDegree polynomials)
      (sentinelInput input)
    (polynomialFamilyLoopInput polynomials tuples).flatMap
        (fun inner =>
          (exactPolynomialUnaryFrameFamilyBody polynomials).emit
            (Sum.inr index, inner)) =
      encodeUnaryFrameBlock ((polynomials.get index).eval input.length) := by
  dsimp only
  rw [polynomialFamilyLoopInput_eq, List.flatMap_append,
    List.flatMap_map]
  rw [show
      (tuplePower (polynomialFamilyDegree polynomials)
          (sentinelInput input)).flatMap
          (fun tuple =>
            (exactPolynomialUnaryFrameFamilyBody polynomials).emit
              (Sum.inr index, Sum.inl tuple)) =
        List.replicate ((polynomials.get index).eval input.length) .tick by
      simpa [exactPolynomialUnaryFrameFamilyBody] using
        polynomialFamilyTupleTicks_all polynomials index input]
  have hseparator := polynomialFamilySeparatorRow (Γ := Γ) polynomials index
  simpa [encodeUnaryFrameBlock] using hseparator

/-- Public semantic target: one unary block per fixed polynomial field. -/
def exactPolynomialUnaryFrames {Γ : Type}
    (polynomials : List (Polynomial Nat)) (input : List Γ) :
    List UnaryFrameSym :=
  encodeUnaryFrame (polynomials.map fun p => p.eval input.length)

/-- The shared tuple/tag nested loop emits exactly the public frame family. -/
theorem exactPolynomialUnaryFrames_eq {Γ : Type}
    (polynomials : List (Polynomial Nat)) (input : List Γ) :
    let tuples := tuplePower (polynomialFamilyDegree polynomials)
      (sentinelInput input)
    nestedLoopOutput (exactPolynomialUnaryFrameFamilyBody polynomials)
        (polynomialFamilyLoopInput polynomials tuples) =
      exactPolynomialUnaryFrames polynomials input := by
  dsimp only
  rw [nestedLoopOutput, polynomialFamilyLoopInput_eq, List.flatMap_append,
    List.flatMap_map]
  have htupleRows :
      (tuplePower (polynomialFamilyDegree polynomials)
          (sentinelInput input)).flatMap
          (fun outer =>
            (List.map Sum.inl
                (tuplePower (polynomialFamilyDegree polynomials)
                  (sentinelInput input)) ++
              List.map Sum.inr (List.finRange polynomials.length)).flatMap
                (fun inner =>
                  (exactPolynomialUnaryFrameFamilyBody polynomials).emit
                    (Sum.inl outer, inner))) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro outer _
    apply List.flatMap_eq_nil_iff.mpr
    intro inner _
    rcases inner with tuple | index <;> rfl
  rw [htupleRows, List.nil_append]
  rw [← polynomialFamilyLoopInput_eq]
  rw [List.flatMap_map]
  simp_rw [exactPolynomialUnaryFrameFamily_tagRow polynomials]
  rw [← List.flatMap_map, exactPolynomialUnaryFrames, encodeUnaryFrame]
  congr 1
  calc
    _ = ((List.finRange polynomials.length).map polynomials.get).map
        (fun p => p.eval input.length) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro index _
      rfl
    _ = _ := by rw [List.map_get_finRange]

/-! ## Concrete source-to-frame-family compiler -/

/-- One fixed compiled TM2 maps the raw source word to the entire exact unary
frame family for any fixed list of natural polynomials. -/
noncomputable def exactPolynomialUnaryFrames_computableInPolyTime
    {Γ : Type} [Fintype Γ]
    (polynomials : List (Polynomial Nat)) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@exactPolynomialUnaryFrames Γ polynomials) := by
  letI : Fintype (PolynomialFamilyTuple Γ polynomials) :=
    tuplePowerFintype (polynomialFamilyDegree polynomials)
  letI : Fintype (PolynomialFamilyLoopSym Γ polynomials) := by
    infer_instance
  let sourceTuples :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (sentinelInput_computableInPolyTime Γ)
      (tuplePower_computableInPolyTime
        (Γ := Option Γ) (polynomialFamilyDegree polynomials))
  let withTags :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice sourceTuples)
      (polynomialFamilyLoopInput_computableInPolyTime
        (Γ := Γ) polynomials)
  let full :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (Classical.choice withTags)
      (nestedLoop_computableInPolyTime
        (exactPolynomialUnaryFrameFamilyBody (Γ := Γ) polynomials))
  let pipeline := fun input : List Γ =>
    nestedLoopOutput (exactPolynomialUnaryFrameFamilyBody polynomials)
      (polynomialFamilyLoopInput polynomials
        (tuplePower (polynomialFamilyDegree polynomials)
          (sentinelInput input)))
  have hpipeline : _root_.Turing.TM2ComputableInPolyTime id id pipeline := by
    simpa only [pipeline, Function.comp_def] using Classical.choice full
  have hsemantics : pipeline = @exactPolynomialUnaryFrames Γ polynomials := by
    funext input
    exact exactPolynomialUnaryFrames_eq polynomials input
  rw [← hsemantics]
  exact hpipeline

end CLRS.Chapter34.Turing.PolyBuilder
