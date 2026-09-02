import CLRSLean.Chapter_34.BinaryNat.Length
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Machine

/-!
# Unary-length to binary encoder: controller and pure counter semantics

The input symbols are Booleans only so the shared PolyBuilder work stacks can
hold the binary counter; their values are ignored, and only input length is
encoded.  The work counter is little-endian while it is incremented.  Popping
it onto the prepend-only output stack produces the public big-endian format.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Encoder

open PolyBuilder

/-- Executable carry propagation on a little-endian bit list. -/
def incrementBits : List Bool → List Bool
  | [] => [true]
  | false :: bits => true :: bits
  | true :: bits => false :: incrementBits bits

@[simp] theorem incrementBits_length_le (bits : List Bool) :
    (incrementBits bits).length ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [incrementBits]
  | cons bit bits ih =>
      cases bit <;> simp [incrementBits, ih]

/-- The executable list carry is exactly natural-number successor. -/
@[simp] theorem incrementBits_bits (n : Nat) :
    incrementBits n.bits = (n + 1).bits := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : n = 0
      · subst n
        simp [incrementBits]
      · have hleading : n.div2 = 0 → n.bodd = true := by
          intro hdiv
          cases hbit : n.bodd with
          | false =>
              apply False.elim
              apply hn
              rw [← Nat.bit_bodd_div2 n, hbit, hdiv]
              rfl
          | true => rfl
        have hbits : n.bits = n.bodd :: n.div2.bits := by
          calc
            n.bits = (Nat.bit n.bodd n.div2).bits :=
              congrArg Nat.bits (Nat.bit_bodd_div2 n).symm
            _ = n.bodd :: n.div2.bits :=
              Nat.bits_append_bit n.div2 n.bodd hleading
        cases hbit : n.bodd with
        | false =>
            have hnvalue : n = 2 * n.div2 := by
              have h := (Nat.bodd_add_div2 n).symm
              simpa [hbit] using h
            rw [hbits, hbit, incrementBits]
            rw [show n + 1 = 2 * n.div2 + 1 by omega,
              Nat.bit1_bits]
        | true =>
            have hnvalue : n = 2 * n.div2 + 1 := by
              have h := (Nat.bodd_add_div2 n).symm
              simpa [hbit, Nat.add_comm] using h
            have hlt : n.div2 < n := Nat.binaryRec_decreasing hn
            rw [hbits, hbit, incrementBits]
            rw [show n + 1 = 2 * (n.div2 + 1) by omega,
              Nat.bit0_bits (n.div2 + 1) (Nat.succ_ne_zero _),
              ih n.div2 hlt]

/-- Repeated executable increments. -/
def incrementMany : Nat → List Bool → List Bool
  | 0, bits => bits
  | count + 1, bits => incrementMany count (incrementBits bits)

@[simp] theorem incrementMany_bits (count n : Nat) :
    incrementMany count n.bits = (n + count).bits := by
  induction count generalizing n with
  | zero => simp [incrementMany]
  | succ count ih =>
      rw [incrementMany, incrementBits_bits, ih]
      congr 1
      omega

@[simp] theorem incrementMany_zero (count : Nat) :
    incrementMany count [] = count.bits := by
  simpa using incrementMany_bits count 0

/-- Public output convention for an internal little-endian counter. -/
def finishEncoding (bits : List Bool) : List Bool :=
  if bits = [] then [false] else bits.reverse

@[simp] theorem finishEncoding_bits (n : Nat) :
    finishEncoding n.bits = CLRS.Chapter34.encodeBinaryNat n := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have hbits : n.bits ≠ [] := by
      intro hnil
      apply hn
      apply Nat.size_eq_zero.mp
      rw [← Nat.size_eq_bits_len, hnil]
      rfl
    simp [finishEncoding, CLRS.Chapter34.encodeBinaryNat, hn, hbits]

inductive Label
  | input
  | carry
  | carryEmpty
  | carryZero
  | carryOne
  | restore
  | restorePush (bit : Bool)
  | outputFirst
  | outputRest
  | emit (bit : Bool)
  | zero
  | halt
deriving DecidableEq, Fintype

/-- Fixed controller for binary incrementation and final serialization. -/
def program : Program Bool Bool where
  Label := Label
  main := .input
  op
    | .input => .popInput .outputFirst (fun _ => .carry)
    | .carry => .popWork₁ .carryEmpty
        (fun bit => if bit then .carryOne else .carryZero)
    | .carryEmpty => .pushWork₁ true .restore
    | .carryZero => .pushWork₁ true .restore
    | .carryOne => .pushWork₂ false .carry
    | .restore => .popWork₂ .input .restorePush
    | .restorePush bit => .pushWork₁ bit .restore
    | .outputFirst => .popWork₁ .zero .emit
    | .outputRest => .popWork₁ .halt .emit
    | .emit bit => .pushOutput bit .outputRest
    | .zero => .pushOutput false .halt
    | .halt => .halt

def cfg (label : Label) (buffer₁ buffer₂ : Option Bool)
    (input output work₁ work₂ : List Bool) : BuilderCfg program :=
  { initialCfg program input with
      label := some label
      buffer₁ := buffer₁
      buffer₂ := buffer₂
      output := output
      work₁ := work₁
      work₂ := work₂ }

end CLRS.Chapter34.Turing.BinaryNat.Encoder
