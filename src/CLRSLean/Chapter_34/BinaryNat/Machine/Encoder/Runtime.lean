import CLRSLean.Chapter_34.BinaryNat.Machine.Encoder.Run

/-!
# Polynomial runtime of the unary-length to binary encoder
-/

noncomputable section

namespace CLRS.Chapter34.Turing.BinaryNat.Encoder

open PolyBuilder

theorem outputSteps_le (bits : List Bool) :
    outputSteps bits ≤ 2 * bits.length + 3 := by
  by_cases hbits : bits = []
  · simp [outputSteps, hbits]
  · simp [outputSteps, hbits]

theorem processSteps_le (bits input : List Bool) :
    processSteps bits input ≤
      input.length * (4 * (bits.length + input.length) + 4) +
        2 * (bits.length + input.length) + 4 := by
  induction input generalizing bits with
  | nil =>
      have hout := outputSteps_le bits
      simp only [processSteps, List.length_nil, Nat.add_zero,
        Nat.zero_mul, Nat.zero_add]
      omega
  | cons symbol rest ih =>
      let nextBits := incrementBits bits
      have hnextLength : nextBits.length + rest.length ≤
          bits.length + (symbol :: rest).length := by
        dsimp [nextBits]
        have hinc := incrementBits_length_le bits
        calc
          (incrementBits bits).length + rest.length ≤
              (bits.length + 1) + rest.length :=
            Nat.add_le_add_right hinc rest.length
          _ = bits.length + (symbol :: rest).length := by simp; omega
      have htail := ih nextBits
      let currentSize := bits.length + (symbol :: rest).length
      let nextSize := nextBits.length + rest.length
      have hfactor : 4 * nextSize + 4 ≤ 4 * currentSize + 4 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left 4 (by
            simpa [nextSize, currentSize] using hnextLength)) 4
      have hproduct :
          rest.length * (4 * nextSize + 4) ≤
            rest.length * (4 * currentSize + 4) :=
        Nat.mul_le_mul_left rest.length hfactor
      have htail' : processSteps nextBits rest ≤
          rest.length * (4 * currentSize + 4) +
            2 * currentSize + 4 := by
        change processSteps nextBits rest ≤
          rest.length * (4 * nextSize + 4) + 2 * nextSize + 4 at htail
        have hdouble : 2 * nextSize ≤ 2 * currentSize :=
          Nat.mul_le_mul_left 2 (by
            simpa [nextSize, currentSize] using hnextLength)
        exact htail.trans
          (Nat.add_le_add (Nat.add_le_add hproduct hdouble) le_rfl)
      have hcarry := carrySteps_le bits []
      simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hcarry
      have hhead : carrySteps bits [] + 1 ≤ 4 * currentSize + 4 := by
        have hsize : bits.length ≤ currentSize := by
          simp [currentSize]
        omega
      rw [processSteps]
      have hadd := Nat.add_le_add htail' hhead
      calc
        processSteps nextBits rest + carrySteps bits [] + 1 =
            processSteps nextBits rest + (carrySteps bits [] + 1) := by omega
        _ ≤ (rest.length * (4 * currentSize + 4) +
              2 * currentSize + 4) + (4 * currentSize + 4) := hadd
        _ = (symbol :: rest).length *
              (4 * (bits.length + (symbol :: rest).length) + 4) +
            2 * (bits.length + (symbol :: rest).length) + 4 := by
          simp only [List.length_cons]
          dsimp [currentSize]
          ring

/-- Exact runtime of the complete encoder. -/
def encoderSteps (input : List Bool) : Nat :=
  processSteps [] input

theorem encoderSteps_le (input : List Bool) :
    encoderSteps input ≤
      4 * input.length * input.length + 6 * input.length + 4 := by
  have h := processSteps_le [] input
  simp only [encoderSteps, List.length_nil, Nat.zero_add] at h ⊢
  nlinarith

theorem builderOutputs :
    BuilderOutputs program
      (fun input : List Bool =>
        CLRS.Chapter34.encodeBinaryNat input.length)
      encoderSteps := by
  intro input
  exact ⟨by simpa [encoderSteps] using run input⟩

theorem outputs :
    Outputs program
      (fun input : List Bool =>
        CLRS.Chapter34.encodeBinaryNat input.length)
      encoderSteps :=
  Outputs.of_builder_run builderOutputs

noncomputable def polyBound : PolyBound encoderSteps where
  polynomial :=
    4 * Polynomial.X * Polynomial.X + 6 * Polynomial.X + 4
  bound input := by
    have h := encoderSteps_le input
    simpa [Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] using h

/-- A genuine fixed TM2 converts a unary count (the length of an arbitrary
Boolean input word) to its canonical compact binary representation. -/
noncomputable def computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List Bool =>
        CLRS.Chapter34.encodeBinaryNat input.length) :=
  ComputableInPolyTime program
    (fun input : List Bool =>
      CLRS.Chapter34.encodeBinaryNat input.length)
    encoderSteps outputs polyBound

end CLRS.Chapter34.Turing.BinaryNat.Encoder
