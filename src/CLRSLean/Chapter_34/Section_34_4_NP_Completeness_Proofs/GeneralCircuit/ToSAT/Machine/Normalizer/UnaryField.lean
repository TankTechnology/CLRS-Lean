import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.Steps

/-!
# Guarded circuit normalizer: exact unary phases

The theorems here are independent of gate semantics.  They prove exact runs
for the input-count parser, shared operand parser, strict-bound subtraction,
and restoration of the selected unary counter.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-- Compose two exact machine segments in chronological order. -/
theorem step_comp {A B C : Option machine.Cfg} (n₁ n₂ : Nat)
    (h₁ : transition^[n₁] A = B) (h₂ : transition^[n₂] B = C) :
    transition^[n₁ + n₂] A = C := by
  simpa [Nat.add_comm] using (show transition^[n₂ + n₁] A = C by
    rw [Function.iterate_add_apply, h₁, h₂])

/-- Compose one concrete step with one following exact phase. -/
theorem step_then {A : Option machine.Cfg} {B C : machine.Cfg} (n : Nat)
    (h₁ : step B = some C) (h₂ : transition^[n] (some C) = A) :
    transition^[n + 1] (some B) = A := by
  rw [Function.iterate_add_apply]
  change transition^[n] (step B) = A
  rw [h₁]
  exact h₂

/-- The initial unary field is consumed exactly and accumulated on the
`inputCount` stack. -/
theorem inputCount_phase (state : State) (count offset : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (gateCount operand saved outputIndex : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .inputCount) state (encNat count ++ input) output rows
          offset gateCount operand saved outputIndex)) =
        some (cfg (some .gates) finalState input output rows
          (offset + count) gateCount operand saved outputIndex) := by
  induction count generalizing state offset with
  | zero =>
      refine ⟨{ state with inputBuffer := some .endMark }, ?_⟩
      change step (cfg (some .inputCount) state (.endMark :: input) output rows
        offset gateCount operand saved outputIndex) = _
      exact input_count_end_step state input output rows offset gateCount operand
        saved outputIndex
  | succ count ih =>
      rcases ih { state with inputBuffer := some .argMark } (offset + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := input_count_arg_step state (encNat count ++ input)
        output rows offset gateCount operand saved outputIndex
      have hfull := step_then (count + 1) hfirst hrun
      simpa [encNat, List.replicate_succ, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfull

private theorem replicate_tick_append_cons (count : Nat)
    (rows : List NormalizedCircuitSym) :
    List.replicate count .tick ++ .tick :: rows =
      .tick :: (List.replicate count .tick ++ rows) := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ, ih]

/-- Copy a chronological gate index to the reversed row stream while moving
the source counter to `saved`. -/
theorem rowIndexCopy_phase (state : State) (kind : GateKind)
    (count saved : Nat) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount operand outputIndex : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some (.rowIndexCopy kind)) state input output rows
          inputCount count operand saved outputIndex)) =
        some (cfg (some (.rowIndexRestore kind)) finalState input output
          (.fieldEnd :: (List.replicate count .tick ++ rows))
          inputCount 0 operand (saved + count) outputIndex) := by
  induction count generalizing state rows saved with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some (.rowIndexCopy kind)) state input output rows
        inputCount 0 operand saved outputIndex) = _
      simpa using row_index_copy_done_step state kind input output rows inputCount
        operand saved outputIndex
  | succ count ih =>
      rcases ih { state with counterPresent := true } (saved + 1) (.tick :: rows) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := row_index_copy_tick_step state kind input output rows inputCount
        count operand saved outputIndex
      have hfull := step_then (count + 1) hfirst hrun
      rw [replicate_tick_append_cons] at hfull
      simpa [List.replicate_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using hfull

/-- Restore a saved chronological index to the gate counter. -/
theorem rowIndexRestore_phase (state : State) (kind : GateKind)
    (count gateCount : Nat) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount operand outputIndex : Nat) :
    ∃ finalState,
      transition^[count]
        (some (cfg (some (.rowIndexRestore kind)) state input output rows
          inputCount gateCount operand count outputIndex)) =
        some (cfg (some (.rowIndexRestore kind)) finalState input output rows
          inputCount (gateCount + count) operand 0 outputIndex) := by
  induction count generalizing state gateCount with
  | zero => exact ⟨state, rfl⟩
  | succ count ih =>
      rcases ih { state with counterPresent := true } (gateCount + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := row_index_restore_tick_step state kind input output rows
        inputCount gateCount operand count outputIndex
      have hfull := step_then count hfirst hrun
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

/-- Complete chronological-index annotation and enter the gate-specific
continuation with the gate counter restored. -/
theorem rowPrefix_phase (state : State) (kind : GateKind) (count : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount operand outputIndex : Nat) :
    ∃ finalState,
      transition^[2 * count + 2]
        (some (cfg (some (.rowIndexCopy kind)) state input output rows
          inputCount count operand 0 outputIndex)) =
        some (cfg (some (afterRowPrefixLabel kind)) finalState input output
          (afterRowPrefixRows kind
            (.fieldEnd :: (List.replicate count .tick ++ rows)))
          inputCount (afterRowPrefixGateCount kind count) operand 0 outputIndex) := by
  rcases rowIndexCopy_phase state kind count 0 input output rows inputCount operand
      outputIndex with ⟨s₁, h₁⟩
  rcases rowIndexRestore_phase s₁ kind count 0 input output
      (.fieldEnd :: (List.replicate count .tick ++ rows)) inputCount operand
      outputIndex with ⟨s₂, h₂⟩
  have h₁' : transition^[count + 1]
      (some (cfg (some (.rowIndexCopy kind)) state input output rows
        inputCount count operand 0 outputIndex)) =
      some (cfg (some (.rowIndexRestore kind)) s₁ input output
        (.fieldEnd :: (List.replicate count .tick ++ rows))
        inputCount 0 operand count outputIndex) := by
    simpa using h₁
  have h₂' : transition^[count]
      (some (cfg (some (.rowIndexRestore kind)) s₁ input output
        (.fieldEnd :: (List.replicate count .tick ++ rows))
        inputCount 0 operand count outputIndex)) =
      some (cfg (some (.rowIndexRestore kind)) s₂ input output
        (.fieldEnd :: (List.replicate count .tick ++ rows))
        inputCount count operand 0 outputIndex) := by
    simpa using h₂
  have h₃ : transition^[1]
      (some (cfg (some (.rowIndexRestore kind)) s₂ input output
        (.fieldEnd :: (List.replicate count .tick ++ rows))
        inputCount count operand 0 outputIndex)) =
      some (cfg (some (afterRowPrefixLabel kind))
        { s₂ with counterPresent := false }
        input output
        (afterRowPrefixRows kind
          (.fieldEnd :: (List.replicate count .tick ++ rows)))
        inputCount (afterRowPrefixGateCount kind count) operand 0 outputIndex) := by
    change step (cfg (some (.rowIndexRestore kind)) s₂ input output
      (.fieldEnd :: (List.replicate count .tick ++ rows))
      inputCount count operand 0 outputIndex) = _
    exact row_index_restore_done_step s₂ kind input output
      (.fieldEnd :: (List.replicate count .tick ++ rows)) inputCount count operand
      outputIndex
  have h₁₂ := step_comp _ _ h₁' h₂'
  have hfull := step_comp _ _ h₁₂ h₃
  refine ⟨{ s₂ with counterPresent := false }, ?_⟩
  have hsteps : count + 1 + count + 1 = 2 * count + 2 := by omega
  rw [← hsteps]
  exact hfull

/-- Row-stack effect of parsing an operand. -/
def operandRows (ret : Return) (count : Nat)
    (rows : List NormalizedCircuitSym) : List NormalizedCircuitSym :=
  match ret with
  | .outputGate => rows
  | _ => .fieldEnd :: (List.replicate count .tick ++ rows)

/-- Output-index effect of parsing an operand. -/
def operandOutputIndex (ret : Return) (count outputIndex : Nat) : Nat :=
  match ret with
  | .outputGate => outputIndex + count
  | _ => outputIndex

/-- Label reached immediately after a well-terminated operand field. -/
def afterOperandLabel (ret : Return) : Label :=
  match ret with
  | .outputGate => .checkTrailing
  | _ => .compareOperand ret

def operandTickRows (ret : Return) (rows : List NormalizedCircuitSym) :
    List NormalizedCircuitSym :=
  match ret with
  | .outputGate => rows
  | _ => .tick :: rows

def operandTickOutputIndex (ret : Return) (outputIndex : Nat) : Nat :=
  match ret with
  | .outputGate => outputIndex + 1
  | _ => outputIndex

private theorem operandRows_succ (ret : Return) (count : Nat)
    (rows : List NormalizedCircuitSym) :
    operandRows ret (count + 1) rows =
      operandRows ret count (operandTickRows ret rows) := by
  cases ret <;>
    simp [operandRows, operandTickRows, List.replicate_succ,
      replicate_tick_append_cons]

private theorem operandOutputIndex_succ (ret : Return) (count outputIndex : Nat) :
    operandOutputIndex ret (count + 1) outputIndex =
      operandOutputIndex ret count (operandTickOutputIndex ret outputIndex) := by
  cases ret <;> simp [operandOutputIndex, operandTickOutputIndex] <;> omega

/-- A shared parser consumes one unary operand, stages its normalized field for
gate operands, and separately retains a final output index. -/
theorem operand_phase (state : State) (ret : Return) (count offset : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount saved outputIndex : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some (.parseOperand ret)) state
          (encNat count ++ input) output rows
          inputCount gateCount offset saved outputIndex)) =
        some (cfg (some (afterOperandLabel ret)) finalState input output
          (operandRows ret count rows) inputCount gateCount (offset + count) saved
          (operandOutputIndex ret count outputIndex)) := by
  induction count generalizing state offset rows outputIndex with
  | zero =>
      refine ⟨{ state with inputBuffer := some .endMark }, ?_⟩
      change step (cfg (some (.parseOperand ret)) state (.endMark :: input)
        output rows inputCount gateCount offset saved outputIndex) = _
      have hend := operand_end_step state ret input output rows inputCount
        gateCount offset saved outputIndex
      cases ret <;>
        simpa [afterOperandLabel, operandRows, operandOutputIndex] using
          hend
  | succ count ih =>
      rcases ih { state with inputBuffer := some .argMark } (offset + 1)
          (operandTickRows ret rows)
          (operandTickOutputIndex ret outputIndex) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := operand_arg_step state ret (encNat count ++ input)
        output rows inputCount gateCount offset saved outputIndex
      have hfirst' :
          step (cfg (some (.parseOperand ret)) state
            (.argMark :: (encNat count ++ input)) output rows
            inputCount gateCount offset saved outputIndex) =
          some (cfg (some (.parseOperand ret))
            { state with inputBuffer := some .argMark }
            (encNat count ++ input) output (operandTickRows ret rows)
            inputCount gateCount (offset + 1) saved
            (operandTickOutputIndex ret outputIndex)) := by
        cases ret <;> simpa [operandTickRows, operandTickOutputIndex] using hfirst
      have hfull := step_then (count + 1) hfirst' hrun
      rw [operandRows_succ, operandOutputIndex_succ]
      simpa [encNat, List.replicate_succ, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfull

/-- Subtract an operand from its selected bound and consume one additional
unit witnessing strict inequality. -/
theorem compareOperand_phase (state : State) (ret : Return)
    (count extra inputCount gateCount saved outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some (.compareOperand ret)) state input output rows
          (withBound ret (count + extra + 1) inputCount gateCount).1
          (withBound ret (count + extra + 1) inputCount gateCount).2
          count saved outputIndex)) =
        some (cfg (some (.restoreBound ret)) finalState input output rows
          (withBound ret extra inputCount gateCount).1
          (withBound ret extra inputCount gateCount).2
          0 (saved + count + 1) outputIndex) := by
  induction count generalizing state saved with
  | zero =>
      refine ⟨{ state with counterPresent := true }, ?_⟩
      simp only [Nat.zero_add]
      change step (cfg (some (.compareOperand ret)) state input output rows
        (withBound ret (extra + 1) inputCount gateCount).1
        (withBound ret (extra + 1) inputCount gateCount).2
        0 saved outputIndex) = _
      simpa [Nat.add_assoc] using compare_operand_done_step state ret input output
        rows extra inputCount gateCount saved outputIndex
  | succ count ih =>
      rcases ih { state with counterPresent := true } (saved + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := compare_operand_tick_step state ret input output rows
        (count + extra + 1) inputCount gateCount count saved outputIndex
      have hfull := step_then (count + 1) hfirst hrun
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

/-- Move every saved unit back to the selected bound stack. -/
theorem restoreBound_phase (state : State) (ret : Return)
    (count bound inputCount gateCount operand outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[count]
        (some (cfg (some (.restoreBound ret)) state input output rows
          (withBound ret bound inputCount gateCount).1
          (withBound ret bound inputCount gateCount).2
          operand count outputIndex)) =
        some (cfg (some (.restoreBound ret)) finalState input output rows
          (withBound ret (bound + count) inputCount gateCount).1
          (withBound ret (bound + count) inputCount gateCount).2
          operand 0 outputIndex) := by
  induction count generalizing state bound with
  | zero =>
      exact ⟨state, rfl⟩
  | succ count ih =>
      rcases ih { state with counterPresent := true } (bound + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := restore_bound_tick_step state ret input output rows bound
        inputCount gateCount operand count outputIndex
      have hfull := step_then count hfirst hrun
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
