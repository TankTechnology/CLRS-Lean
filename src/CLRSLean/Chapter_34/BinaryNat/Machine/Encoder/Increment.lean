import CLRSLean.Chapter_34.BinaryNat.Machine.Encoder.Core

/-!
# Exact carry and restoration phases of the binary encoder
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.BinaryNat.Encoder

open PolyBuilder

def restoreSteps (saved : List Bool) : Nat :=
  2 * saved.length + 1

private theorem restore_eval (saved : List Bool)
    (buffer₁ buffer₂ : Option Bool) (input output work : List Bool) :
    (flip Option.bind (step program))^[restoreSteps saved]
      (some (cfg .restore buffer₁ buffer₂ input output work saved)) =
    some (cfg .input buffer₁ none input output
      (saved.reverse ++ work) []) := by
  induction saved generalizing buffer₂ work with
  | nil => rfl
  | cons bit saved ih =>
      rw [show restoreSteps (bit :: saved) =
          restoreSteps saved + 1 + 1 by
            simp [restoreSteps]; omega,
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[restoreSteps saved]
          (some (cfg .restore buffer₁ (some bit) input output
            (bit :: work) saved)) = _
      simpa [List.reverse_cons, List.append_assoc] using
        ih (some bit) (bit :: work)

/-- Buffer left by the terminal carry scan. -/
def carryBuffer : List Bool → Option Bool
  | [] => none
  | false :: _ => some false
  | true :: bits => carryBuffer bits

/-- Exact cost of carrying through `bits` and restoring an existing saved
low-bit prefix. -/
def carrySteps : List Bool → List Bool → Nat
  | [], saved => restoreSteps saved + 2
  | false :: _, saved => restoreSteps saved + 2
  | true :: bits, saved => carrySteps bits (false :: saved) + 2

theorem carrySteps_le (bits saved : List Bool) :
    carrySteps bits saved ≤
      4 * bits.length + 2 * saved.length + 3 := by
  induction bits generalizing saved with
  | nil => simp [carrySteps, restoreSteps]
  | cons bit bits ih =>
      cases bit
      · simp [carrySteps, restoreSteps]
      · have h := ih (false :: saved)
        simp only [List.length_cons] at h
        simp only [carrySteps, List.length_cons]
        omega

private theorem carry_eval (bits saved : List Bool)
    (buffer₁ buffer₂ : Option Bool) (input output : List Bool) :
    (flip Option.bind (step program))^[carrySteps bits saved]
      (some (cfg .carry buffer₁ buffer₂ input output bits saved)) =
    some (cfg .input (carryBuffer bits) none input output
      (saved.reverse ++ incrementBits bits) []) := by
  induction bits generalizing saved buffer₁ buffer₂ with
  | nil =>
      rw [show carrySteps [] saved = restoreSteps saved + 1 + 1 by
        simp [carrySteps],
        Function.iterate_succ_apply, Function.iterate_succ_apply]
      change
        (flip Option.bind (step program))^[restoreSteps saved]
          (some (cfg .restore none buffer₂ input output [true] saved)) = _
      simpa [carryBuffer, incrementBits, List.append_assoc] using
        restore_eval saved none buffer₂ input output [true]
  | cons bit bits ih =>
      cases bit with
      | false =>
          rw [show carrySteps (false :: bits) saved =
              restoreSteps saved + 1 + 1 by
                simp [carrySteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[restoreSteps saved]
              (some (cfg .restore (some false) buffer₂ input output
                (true :: bits) saved)) = _
          simpa [carryBuffer, incrementBits, List.append_assoc] using
            restore_eval saved (some false) buffer₂ input output
              (true :: bits)
      | true =>
          rw [show carrySteps (true :: bits) saved =
              carrySteps bits (false :: saved) + 1 + 1 by
                simp [carrySteps],
            Function.iterate_succ_apply, Function.iterate_succ_apply]
          change
            (flip Option.bind (step program))^[carrySteps bits (false :: saved)]
              (some (cfg .carry (some true) buffer₂ input output bits
                (false :: saved))) = _
          simpa [carryBuffer, incrementBits, List.reverse_cons,
            List.append_assoc] using
            ih (false :: saved) (some true) buffer₂

/-- Exact independent-semantics run of one counter increment. -/
def increment_run (bits : List Bool) (buffer₁ buffer₂ : Option Bool)
    (input output : List Bool) :
    EvalsToInTime (step program)
      (cfg .carry buffer₁ buffer₂ input output bits [])
      (some (cfg .input (carryBuffer bits) none input output
        (incrementBits bits) []))
      (carrySteps bits []) := by
  exact ⟨⟨carrySteps bits [], by
    simpa using carry_eval bits [] buffer₁ buffer₂ input output⟩, le_rfl⟩

end CLRS.Chapter34.Turing.BinaryNat.Encoder
