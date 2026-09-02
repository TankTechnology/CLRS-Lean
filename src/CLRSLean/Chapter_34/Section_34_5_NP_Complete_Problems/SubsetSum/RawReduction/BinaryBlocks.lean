import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.RawReduction.NumericBounds
import CLRSLean.Chapter_34.BinaryNat.RoundTrip

/-!
# Fixed-width binary blocks for the SUBSET-SUM reduction

The mathematical reduction packs small column digits in a power-of-two
radix.  This file exposes the same number as a concrete list of fixed-width
binary blocks, followed by a streaming canonicalization pass.  It is the
semantic interface used by the reduction machine: no general multiplication
or exponentiation routine is needed at runtime.
-/

namespace CLRS.Chapter34.SubsetSumReduction

/-- A little-endian, zero-padded binary block of exactly `blockWidth` cells
whenever `digit < 2 ^ blockWidth`. -/
def fixedBinaryBlock (blockWidth digit : Nat) : List Bool :=
  (Nat.digitsAppend 2 blockWidth digit).map fun value => decide (value = 1)

theorem fixedBinaryBlock_toNat {blockWidth digit : Nat} :
    (fixedBinaryBlock blockWidth digit).map Bool.toNat =
      Nat.digitsAppend 2 blockWidth digit := by
  simp only [fixedBinaryBlock, List.map_map]
  have hmaps : List.map
      (Bool.toNat ∘ fun value => decide (value = 1))
      (Nat.digitsAppend 2 blockWidth digit) =
      List.map id (Nat.digitsAppend 2 blockWidth digit) := by
    apply List.map_congr_left
    intro value hvalue
    have hlt : value < 2 :=
      Nat.lt_of_mem_digitsAppend (by omega) blockWidth value hvalue
    interval_cases value <;> decide
  simpa only [List.map_id] using hmaps

theorem fixedBinaryBlock_length {blockWidth digit : Nat}
    (hdigit : digit < 2 ^ blockWidth) :
    (fixedBinaryBlock blockWidth digit).length = blockWidth := by
  simp [fixedBinaryBlock, Nat.length_digitsAppend (by omega) _ hdigit]

theorem fixedBinaryBlock_value {blockWidth digit : Nat}
    (hdigit : digit < 2 ^ blockWidth) :
    Nat.ofDigits 2 ((fixedBinaryBlock blockWidth digit).map Bool.toNat) =
      digit := by
  rw [fixedBinaryBlock_toNat]
  exact (Nat.setInvOn_digitsAppend_ofDigits (by omega) blockWidth).2 hdigit

/-- Little-endian concatenation of all fixed-width column blocks. -/
def packedBitsLE (blockWidth : Nat) : Nat → (Nat → Nat) → List Bool
  | 0, _ => []
  | width + 1, digits =>
      fixedBinaryBlock blockWidth (digits 0) ++
        packedBitsLE blockWidth width (fun column => digits (column + 1))

@[simp] theorem packedBitsLE_zero (blockWidth : Nat) (digits : Nat → Nat) :
    packedBitsLE blockWidth 0 digits = [] := rfl

@[simp] theorem packedBitsLE_succ (blockWidth width : Nat)
    (digits : Nat → Nat) :
    packedBitsLE blockWidth (width + 1) digits =
      fixedBinaryBlock blockWidth (digits 0) ++
        packedBitsLE blockWidth width (fun column => digits (column + 1)) := rfl

theorem packedBitsLE_length {blockWidth width : Nat}
    {digits : Nat → Nat}
    (hdigits : ∀ column < width, digits column < 2 ^ blockWidth) :
    (packedBitsLE blockWidth width digits).length = blockWidth * width := by
  induction width generalizing digits with
  | zero => simp
  | succ width ih =>
      rw [packedBitsLE_succ, List.length_append,
        fixedBinaryBlock_length (hdigits 0 (by omega)),
        ih (fun column hcolumn => hdigits (column + 1) (by omega))]
      simp [Nat.mul_succ, Nat.add_comm]

theorem packedBitsLE_value {blockWidth width : Nat}
    {digits : Nat → Nat}
    (hdigits : ∀ column < width, digits column < 2 ^ blockWidth) :
    Nat.ofDigits 2 ((packedBitsLE blockWidth width digits).map Bool.toNat) =
      packColumns (2 ^ blockWidth) width digits := by
  induction width generalizing digits with
  | zero => simp
  | succ width ih =>
      rw [packedBitsLE_succ, List.map_append, Nat.ofDigits_append,
        fixedBinaryBlock_value (hdigits 0 (by omega)), List.length_map,
        fixedBinaryBlock_length (hdigits 0 (by omega)),
        ih (fun column hcolumn => hdigits (column + 1) (by omega))]
      rfl

/-- Remove big-endian leading zeroes, using the unique one-bit encoding for
zero.  A fixed two-state streaming controller implements this function. -/
def canonicalizeBinaryBits : List Bool → List Bool
  | [] => [false]
  | false :: bits => canonicalizeBinaryBits bits
  | true :: bits => true :: bits

theorem canonicalizeBinaryBits_value (bits : List Bool) :
    binaryNatValue (canonicalizeBinaryBits bits) = binaryNatValue bits := by
  induction bits with
  | nil => simp [canonicalizeBinaryBits, binaryNatValue]
  | cons bit bits ih =>
      cases bit
      · rw [canonicalizeBinaryBits, ih]
        simp [binaryNatValue, List.reverse_cons, Nat.ofDigits_append]
      · rfl

theorem canonicalizeBinaryBits_isCanonical (bits : List Bool) :
    isCanonicalBinaryNat (canonicalizeBinaryBits bits) = true := by
  induction bits with
  | nil => simp [canonicalizeBinaryBits, isCanonicalBinaryNat]
  | cons bit bits ih =>
      cases bit
      · simpa [canonicalizeBinaryBits] using ih
      · simp [canonicalizeBinaryBits, isCanonicalBinaryNat]

theorem canonicalizeBinaryBits_eq_encode (bits : List Bool) :
    canonicalizeBinaryBits bits = encodeBinaryNat (binaryNatValue bits) := by
  symm
  apply encodeBinaryNat_of_decode_eq_some
  rw [decodeBinaryNat_eq_some_iff]
  exact ⟨canonicalizeBinaryBits_isCanonical bits,
    canonicalizeBinaryBits_value bits⟩

/-- Canonical big-endian encoding obtained from fixed-width little-endian
column blocks. -/
def encodePackedColumns (blockWidth width : Nat)
    (digits : Nat → Nat) : List Bool :=
  canonicalizeBinaryBits (packedBitsLE blockWidth width digits).reverse

theorem encodePackedColumns_eq {blockWidth width : Nat}
    {digits : Nat → Nat}
    (hdigits : ∀ column < width, digits column < 2 ^ blockWidth) :
    encodePackedColumns blockWidth width digits =
      encodeBinaryNat (packColumns (2 ^ blockWidth) width digits) := by
  rw [encodePackedColumns, canonicalizeBinaryBits_eq_encode]
  congr 1
  simp only [binaryNatValue, List.reverse_reverse]
  exact packedBitsLE_value hdigits

/-- Bit-block target stream for a formula. -/
def reductionTargetBits (formula : CNF) : List Bool :=
  encodePackedColumns (reductionBlockWidth formula)
    (reductionWidth formula) (targetDigit formula)

/-- Bit-block value stream for one generated item. -/
def reductionItemBits (formula : CNF) (item : SubsetSumItem) : List Bool :=
  encodePackedColumns (reductionBlockWidth formula)
    (reductionWidth formula) (itemDigit formula item)

theorem reductionTargetBits_eq (formula : CNF) :
    reductionTargetBits formula = encodeBinaryNat (reductionTarget formula) := by
  rw [reductionTargetBits, reductionTarget, reductionBase]
  exact encodePackedColumns_eq
    (fun column _ => targetDigit_lt_reductionBase formula column)

theorem reductionItemBits_eq {formula : CNF}
    (hthree : IsThreeCNF formula) (item : SubsetSumItem) :
    reductionItemBits formula item = encodeBinaryNat (itemValue formula item) := by
  rw [reductionItemBits, itemValue, reductionBase]
  apply encodePackedColumns_eq
  intro column _
  have hdigit := itemDigit_le_three hthree item column
  have hbase : 4 < 2 ^ reductionBlockWidth formula := by
    simpa [reductionBase] using four_lt_reductionBase formula
  omega

end CLRS.Chapter34.SubsetSumReduction
