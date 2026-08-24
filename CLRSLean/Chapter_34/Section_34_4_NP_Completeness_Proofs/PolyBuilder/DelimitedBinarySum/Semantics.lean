import CLRSLean.Chapter_34.BinaryNat.Machine.Adder.Semantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DelimitedBinarySum.Runtime

/-! # Delimited binary sum: numeric semantics -/

namespace CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum

private theorem finishAdd_eq_addLittle (accumulator : List Bool) (carry : Bool)
    (work : List Bool) :
    finishAdd accumulator carry work =
      BinaryNat.Adder.addLittle [] accumulator carry ++ work := by
  induction accumulator generalizing carry work with
  | nil => cases carry <;> simp [finishAdd, BinaryNat.Adder.addLittle]
  | cons accumulatorBit accumulator ih =>
      let cell := BinaryNat.Adder.addCell false accumulatorBit carry
      rw [finishAdd, ih]
      simp only [BinaryNat.Adder.addLittle, List.append_assoc,
        List.singleton_append]

private theorem finishAdd_false_nil (accumulator : List Bool) :
    finishAdd accumulator false [] = accumulator.reverse := by
  rw [finishAdd_eq_addLittle]
  simp only [List.append_nil]
  induction accumulator with
  | nil => simp [BinaryNat.Adder.addLittle]
  | cons accumulatorBit accumulator ih =>
      simp [BinaryNat.Adder.addLittle, BinaryNat.Adder.addCell, ih,
        List.reverse_cons]

private theorem sumReversed_field (field : List Bool)
    (rest : List (Option Bool)) (accumulator : List Bool) (carry : Bool)
    (work : List Bool) :
    sumReversed (field.map some ++ none :: rest) accumulator carry work =
      sumReversed rest
        ((BinaryNat.Adder.addLittle field accumulator carry ++ work).reverse)
        false [] := by
  induction field generalizing accumulator carry work with
  | nil =>
      simp only [List.map_nil, List.nil_append, sumReversed]
      rw [finishAdd_eq_addLittle]
  | cons fieldBit field ih =>
      cases accumulator with
      | nil =>
          let cell := BinaryNat.Adder.addCell fieldBit false carry
          simp only [List.map_cons, List.cons_append, sumReversed]
          simpa [BinaryNat.Adder.addLittle, cell, List.append_assoc] using
            ih (accumulator := []) (carry := cell.2) (work := cell.1 :: work)
      | cons accumulatorBit accumulator =>
          let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
          simp only [List.map_cons, List.cons_append, sumReversed]
          simpa [BinaryNat.Adder.addLittle, cell, List.append_assoc] using
            ih (accumulator := accumulator) (carry := cell.2)
              (work := cell.1 :: work)

private theorem sumReversed_final_field (field accumulator work : List Bool)
    (carry : Bool) :
    sumReversed (field.map some) accumulator carry work =
      BinaryNat.Adder.addLittle field accumulator carry ++ work := by
  induction field generalizing accumulator carry work with
  | nil => simpa [sumReversed] using finishAdd_eq_addLittle accumulator carry work
  | cons fieldBit field ih =>
      cases accumulator with
      | nil =>
          let cell := BinaryNat.Adder.addCell fieldBit false carry
          simp only [List.map_cons, sumReversed]
          simpa [BinaryNat.Adder.addLittle, cell, List.append_assoc] using
            ih (accumulator := []) (carry := cell.2) (work := cell.1 :: work)
      | cons accumulatorBit accumulator =>
          let cell := BinaryNat.Adder.addCell fieldBit accumulatorBit carry
          simp only [List.map_cons, sumReversed]
          simpa [BinaryNat.Adder.addLittle, cell, List.append_assoc] using
            ih (accumulator := accumulator) (carry := cell.2)
              (work := cell.1 :: work)

/-- Appending one final delimiter does not change the total controller's
output: end-of-input already closes the last field. -/
theorem sumReversed_append_delimiter (symbols : List (Option Bool))
    (accumulator : List Bool) (carry : Bool) (work : List Bool) :
    sumReversed (symbols ++ [none]) accumulator carry work =
      sumReversed symbols accumulator carry work := by
  induction symbols generalizing accumulator carry work with
  | nil =>
      simp only [List.nil_append, sumReversed]
      rw [finishAdd_false_nil]
      simp
  | cons field symbols ih =>
      cases field with
      | none =>
          simp only [List.cons_append, sumReversed]
          exact ih _ false []
      | some fieldBit =>
          cases accumulator with
          | nil =>
              simp only [List.cons_append, sumReversed]
              exact ih [] _ (_ :: work)
          | cons accumulatorBit accumulator =>
              simp only [List.cons_append, sumReversed]
              exact ih accumulator _ (_ :: work)

private def littleFields (words : List (List Bool)) : List (Option Bool) :=
  words.flatMap fun word => word.map some ++ [none]

private theorem littleValue_reverse (word : List Bool) :
    BinaryNat.Adder.littleValue word.reverse = binaryNatValue word := by
  simp [BinaryNat.Adder.littleValue, binaryNatValue]

private theorem sumReversed_littleFields_value (words : List (List Bool))
    (accumulator : List Bool) :
    binaryNatValue (sumReversed (littleFields words) accumulator false []) =
      BinaryNat.Adder.littleValue accumulator +
        (words.map BinaryNat.Adder.littleValue).sum := by
  induction words generalizing accumulator with
  | nil =>
      simp [littleFields, sumReversed, finishAdd_eq_addLittle,
        BinaryNat.Adder.addLittle_value, BinaryNat.Adder.littleValue]
  | cons word words ih =>
      rw [show littleFields (word :: words) =
          word.map some ++ none :: littleFields words by
        simp [littleFields, List.append_assoc]]
      rw [sumReversed_field, ih]
      simp only [List.append_nil]
      rw [littleValue_reverse, BinaryNat.Adder.addLittle_value]
      simp [Nat.add_assoc, Nat.add_comm]

private theorem reversed_blocks_append_delimiter (words : List (List Bool)) :
    (words.flatMap fun word => none :: word.map some) ++ [none] =
      none :: littleFields words := by
  induction words with
  | nil => simp [littleFields]
  | cons word words ih =>
      simp only [List.flatMap_cons, littleFields, List.cons_append,
        List.append_assoc, List.cons.injEq, true_and]
      simpa [littleFields, List.append_assoc] using ih

private theorem reverse_encoded_fields (values : List Nat) :
    (values.flatMap fun value =>
        (encodeBinaryNat value).map some ++ [none]).reverse =
      values.reverse.flatMap fun value =>
        none :: (encodeBinaryNat value).reverse.map some := by
  simp [List.reverse_flatMap, Function.comp_def, List.reverse_append]

/-- Numeric correctness on the canonical field stream used by the TSP and
SUBSET-SUM verifiers. -/
theorem binaryNatValue_sumDelimited_encoded (values : List Nat) :
    binaryNatValue
        (sumDelimited (values.flatMap fun value =>
          (encodeBinaryNat value).map some ++ [none])) =
      values.sum := by
  rw [sumDelimited, reverse_encoded_fields]
  rw [← sumReversed_append_delimiter]
  let words := values.reverse.map fun value => (encodeBinaryNat value).reverse
  have hstream :
      (values.reverse.flatMap fun value =>
          none :: (encodeBinaryNat value).reverse.map some) =
        words.flatMap fun word => none :: word.map some := by
    have hstreamAux (xs : List Nat) :
        (xs.flatMap fun value =>
            none :: (encodeBinaryNat value).reverse.map some) =
          (xs.map fun value => (encodeBinaryNat value).reverse).flatMap
            (fun word => none :: word.map some) := by
      induction xs with
      | nil => rfl
      | cons value xs ih =>
          simp only [List.flatMap_cons, List.map_cons]
          rw [ih]
    exact hstreamAux values.reverse
  rw [hstream, reversed_blocks_append_delimiter]
  simp only [sumReversed, finishAdd, List.reverse_nil]
  rw [sumReversed_littleFields_value]
  have hzero : BinaryNat.Adder.littleValue [] = 0 := by
    simp [BinaryNat.Adder.littleValue]
  rw [hzero, Nat.zero_add]
  have hvalue (value : Nat) :
      BinaryNat.Adder.littleValue (encodeBinaryNat value).reverse = value := by
    rw [littleValue_reverse, binaryNatValue_encode]
  have hwordsAux (xs : List Nat) :
      ((xs.map fun value => (encodeBinaryNat value).reverse).map
          BinaryNat.Adder.littleValue).sum = xs.sum := by
    induction xs with
    | nil => rfl
    | cons value xs ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [hvalue, ih]
  have hwords :
      (words.map BinaryNat.Adder.littleValue).sum = values.reverse.sum := by
    exact hwordsAux values.reverse
  rw [hwords, List.sum_reverse]

end CLRS.Chapter34.Turing.PolyBuilder.DelimitedBinarySum
