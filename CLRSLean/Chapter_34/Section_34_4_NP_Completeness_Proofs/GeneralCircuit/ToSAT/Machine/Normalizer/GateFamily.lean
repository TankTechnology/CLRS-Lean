import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.GateBinary

/-!
# Guarded circuit normalizer: complete gate family
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-- Exact successful cost of one valid gate. -/
def gateSteps (gateIndex : Nat) : CircuitGate → Nat
  | .input inputIndex => 2 * gateIndex + 3 * inputIndex + 7
  | .const _ => 2 * gateIndex + 3
  | .not source => 2 * gateIndex + 3 * source + 7
  | .and left right | .or left right =>
      2 * gateIndex + 3 * left + 3 * right + 11

/-- Every constructor-specific theorem has one common exact interface. -/
theorem gate_phase (state : State) (gate : CircuitGate)
    (gateIndex inputCount : Nat) (hvalid : gate.ValidAt inputCount gateIndex)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[gateSteps gateIndex gate]
        (some (cfg (some .gates) state
          (encodeCircuitGate gate ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRow gateIndex gate).reverse ++ rows)
          inputCount (gateIndex + 1) 0 0 0) := by
  cases gate with
  | input inputIndex =>
      simp only [CircuitGate.ValidAt] at hvalid
      obtain ⟨slack, hcount⟩ := Nat.exists_eq_add_of_lt hvalid
      simpa [gateSteps, hcount] using
        inputGate_phase state inputIndex slack gateIndex input output rows
  | const value =>
      simpa [gateSteps] using
        constantGate_phase state value gateIndex input output rows inputCount
  | not source =>
      simp only [CircuitGate.ValidAt] at hvalid
      obtain ⟨slack, hindex⟩ := Nat.exists_eq_add_of_lt hvalid
      simpa [gateSteps, hindex] using
        notGate_phase state source slack inputCount input output rows
  | and left right =>
      rcases hvalid with ⟨hleft, hright⟩
      simpa [gateSteps] using
        andGate_phase state left right gateIndex inputCount hleft hright
          input output rows
  | or left right =>
      rcases hvalid with ⟨hleft, hright⟩
      simpa [gateSteps] using
        orGate_phase state left right gateIndex inputCount hleft hright
          input output rows

/-- Exact cost of a gate list beginning at a chronological index. -/
def gateFamilyStepsFrom : Nat → List CircuitGate → Nat
  | _, [] => 0
  | gateIndex, gate :: gates =>
      gateSteps gateIndex gate + gateFamilyStepsFrom (gateIndex + 1) gates

/-- Normalize every row of a valid ordered gate family, preserving the input
counter and leaving the reverse of the exact indexed record on `rows`. -/
theorem gateFamily_phase (state : State) (gates : List CircuitGate)
    (gateIndex inputCount : Nat)
    (hvalid : ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + i))
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[gateFamilyStepsFrom gateIndex gates]
        (some (cfg (some .gates) state
          (gates.flatMap encodeCircuitGate ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (cfg (some .gates) finalState input output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0) := by
  induction gates generalizing state gateIndex rows with
  | nil =>
      refine ⟨state, ?_⟩
      simp [gateFamilyStepsFrom, encodeNormalizedGateRowsFrom]
  | cons gate gates ih =>
      have hhead : gate.ValidAt inputCount gateIndex := by
        simpa using hvalid 0 (by simp)
      have htail : ∀ i (hi : i < gates.length),
          (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + 1 + i) := by
        intro i hi
        have h := hvalid (i + 1) (by simpa using hi)
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      rcases gate_phase state gate gateIndex inputCount hhead
          (gates.flatMap encodeCircuitGate ++ input) output rows with
        ⟨s₁, h₁⟩
      rcases ih s₁ (gateIndex + 1)
          htail ((encodeNormalizedGateRow gateIndex gate).reverse ++ rows) with
        ⟨s₂, h₂⟩
      refine ⟨s₂, ?_⟩
      have hfull := step_comp _ _ h₁ h₂
      simpa [gateFamilyStepsFrom, encodeNormalizedGateRowsFrom,
        List.reverse_append, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfull

private theorem compareBoundPrefix_phase (state : State) (ret : Return)
    (bound extra saved inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[bound]
        (some (cfg (some (.compareOperand ret)) state input output rows
          (withBound ret bound inputCount gateCount).1
          (withBound ret bound inputCount gateCount).2
          (bound + extra) saved outputIndex)) =
        some (cfg (some (.compareOperand ret)) finalState input output rows
          (withBound ret 0 inputCount gateCount).1
          (withBound ret 0 inputCount gateCount).2
          extra (saved + bound) outputIndex) := by
  induction bound generalizing state saved with
  | zero => exact ⟨state, by simp⟩
  | succ bound ih =>
      rcases ih { state with counterPresent := true } (saved + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := compare_operand_tick_step state ret input output rows bound
        inputCount gateCount (bound + extra) saved outputIndex
      have hfirst' :
          step (cfg (some (.compareOperand ret)) state input output rows
            (withBound ret (bound + 1) inputCount gateCount).1
            (withBound ret (bound + 1) inputCount gateCount).2
            (bound + 1 + extra) saved outputIndex) =
          some (cfg (some (.compareOperand ret))
            { state with counterPresent := true }
            input output rows
            (withBound ret bound inputCount gateCount).1
            (withBound ret bound inputCount gateCount).2
            (bound + extra) (saved + 1) outputIndex) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfirst
      have hfull := step_then bound hfirst' hrun
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

private theorem boundZero_reject_step (state : State) (ret : Return)
    (extra inputCount gateCount saved outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    step (cfg (some (.compareOperand ret)) state input output rows
      (withBound ret 0 inputCount gateCount).1
      (withBound ret 0 inputCount gateCount).2
      extra saved outputIndex) =
      some (cfg (some .clearInput) { state with counterPresent := false }
        input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        extra.pred saved outputIndex) := by
  cases extra with
  | zero =>
      simpa using compare_operand_zero_bound_zero_step state ret input output rows
        inputCount gateCount saved outputIndex
  | succ extra =>
      simpa using compare_operand_positive_bound_zero_step state ret extra input
        output rows inputCount gateCount saved outputIndex

/-- Rejection core for the first invalid gate row: once an operand is at least
its selected bound, the shared comparison and cleanup path halts with exactly
the invalid sentinel.  Gate-constructor reject theorems instantiate this core
after their canonical tag and operand parsers. -/
theorem firstInvalidGate_reject (state : State) (ret : Return)
    (bound extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some (.compareOperand ret)) state input output rows
          (withBound ret bound inputCount gateCount).1
          (withBound ret bound inputCount gateCount).2
          (bound + extra) 0 outputIndex)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  rcases compareBoundPrefix_phase state ret bound extra 0 inputCount gateCount
      outputIndex input output rows with ⟨s₁, h₁⟩
  have h₁' : transition^[bound]
      (some (cfg (some (.compareOperand ret)) state input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        (bound + extra) 0 outputIndex)) =
      some (cfg (some (.compareOperand ret)) s₁ input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        extra bound outputIndex) := by
    simpa using h₁
  have h₂ : transition^[1]
      (some (cfg (some (.compareOperand ret)) s₁ input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        extra bound outputIndex)) =
      some (cfg (some .clearInput) { s₁ with counterPresent := false }
        input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        extra.pred bound outputIndex) := by
    change step (cfg (some (.compareOperand ret)) s₁ input output rows
      (withBound ret 0 inputCount gateCount).1
      (withBound ret 0 inputCount gateCount).2
      extra bound outputIndex) = _
    exact boundZero_reject_step s₁ ret extra inputCount gateCount bound
      outputIndex input output rows
  have h₃ := clearAndEmitInvalid_phase { s₁ with counterPresent := false }
    input output rows
    (withBound ret 0 inputCount gateCount).1
    (withBound ret 0 inputCount gateCount).2
    extra.pred bound outputIndex
  have h₁₂ := step_comp _ _ h₁' h₂
  have hfull := step_comp _ _ h₁₂ h₃
  exact ⟨bound + 1 +
    clearAndEmitInvalidSteps input output rows
      (withBound ret 0 inputCount gateCount).1
      (withBound ret 0 inputCount gateCount).2
      extra.pred bound outputIndex, hfull⟩

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
