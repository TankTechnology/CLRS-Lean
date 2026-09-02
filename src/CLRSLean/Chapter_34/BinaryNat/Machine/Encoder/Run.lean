import CLRSLean.Chapter_34.BinaryNat.Machine.Encoder.Increment

/-!
# Complete exact run of the unary-length to binary encoder
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Encoder

open PolyBuilder

def outputSteps (bits : List Bool) : Nat :=
  if bits = [] then 3 else 2 * bits.length + 2

private theorem outputRest_eval (bits : List Bool)
    (buffer₁ buffer₂ : Option Bool) (output : List Bool) :
    (flip Option.bind (step program))^[2 * bits.length + 1]
      (some (cfg .outputRest buffer₁ buffer₂ [] output bits [])) =
    some (cfg .halt none buffer₂ []
      (bits.reverse ++ output) [] []) := by
  induction bits generalizing buffer₁ output with
  | nil => rfl
  | cons bit bits ih =>
      rw [show 2 * (bit :: bits).length + 1 =
          (2 * bits.length + 1) + 1 + 1 by simp; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[2 * bits.length + 1]
          (some (cfg .outputRest (some bit) buffer₂ []
            (bit :: output) bits [])) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit) (bit :: output)

/-- Exact serialization and halt from the completed little-endian counter. -/
def output_run (bits : List Bool) (buffer₁ buffer₂ : Option Bool)
    (output : List Bool) :
    EvalsToInTime (step program)
      (cfg .outputFirst buffer₁ buffer₂ [] output bits [])
      (some (haltCfg program (finishEncoding bits ++ output)))
      (outputSteps bits) := by
  cases bits with
  | nil =>
      refine ⟨⟨3, ?_⟩, by simp [outputSteps]⟩
      rfl
  | cons bit bits =>
      let afterRest := cfg .halt none buffer₂ []
        ((bit :: bits).reverse ++ output) [] []
      have hprefix : EvalsToInTime (step program)
          (cfg .outputFirst buffer₁ buffer₂ [] output (bit :: bits) [])
          (some afterRest) (2 * bits.length + 3) := by
        refine ⟨⟨2 * bits.length + 3, ?_⟩, le_rfl⟩
        rw [show 2 * bits.length + 3 =
            (2 * bits.length + 1) + 1 + 1 by omega,
          Function.iterate_succ_apply, Function.iterate_succ_apply]
        change
          (flip Option.bind (step program))^[2 * bits.length + 1]
            (some (cfg .outputRest (some bit) buffer₂ []
              (bit :: output) bits [])) = some afterRest
        simpa [afterRest, List.reverse_cons, List.append_assoc] using
          outputRest_eval bits (some bit) buffer₂ (bit :: output)
      have hhalt : EvalsToInTime (step program) afterRest
          (some (haltCfg program ((bit :: bits).reverse ++ output))) 1 := by
        exact ⟨⟨1, rfl⟩, le_rfl⟩
      let full := EvalsToInTime.trans (step program)
        (2 * bits.length + 3) 1 _ afterRest _ hprefix hhalt
      convert full using 1 <;>
        simp [outputSteps, finishEncoding] <;> omega

/-- Exact remaining runtime from an arbitrary counter state. -/
def processSteps : List Bool → List Bool → Nat
  | bits, [] => outputSteps bits + 1
  | bits, _ :: rest =>
      processSteps (incrementBits bits) rest + carrySteps bits [] + 1

private def process_run (bits input : List Bool)
    (buffer₁ buffer₂ : Option Bool) (output : List Bool) :
    EvalsToInTime (step program)
      (cfg .input buffer₁ buffer₂ input output bits [])
      (some (haltCfg program
        (finishEncoding (incrementMany input.length bits) ++ output)))
      (processSteps bits input) := by
  induction input generalizing bits buffer₁ buffer₂ with
  | nil =>
      have hpop : EvalsToInTime (step program)
          (cfg .input buffer₁ buffer₂ [] output bits [])
          (some (cfg .outputFirst none buffer₂ [] output bits [])) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hout := output_run bits none buffer₂ output
      let full := EvalsToInTime.trans (step program)
        1 (outputSteps bits) _ _ _ hpop hout
      simpa [processSteps, incrementMany] using full
  | cons symbol rest ih =>
      have hpop : EvalsToInTime (step program)
          (cfg .input buffer₁ buffer₂ (symbol :: rest) output bits [])
          (some (cfg .carry (some symbol) buffer₂ rest output bits [])) 1 :=
        ⟨⟨1, rfl⟩, le_rfl⟩
      have hinc := increment_run bits (some symbol) buffer₂ rest output
      have htail := ih (incrementBits bits) (carryBuffer bits) none
      let throughIncrement := EvalsToInTime.trans (step program)
        1 (carrySteps bits []) _ _ _ hpop hinc
      let full := EvalsToInTime.trans (step program)
        (carrySteps bits [] + 1)
        (processSteps (incrementBits bits) rest)
        _ _ _ throughIncrement htail
      simpa [processSteps, incrementMany, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using full

/-- Exact complete builder execution. -/
def run (input : List Bool) :
    EvalsToInTime (step program)
      (initialCfg program input)
      (some (haltCfg program
        (CLRS.Chapter34.encodeBinaryNat input.length)))
      (processSteps [] input) := by
  convert process_run [] input none none [] using 1 <;>
    simp [cfg, initialCfg, program]

end CLRS.Chapter34.Turing.BinaryNat.Encoder
