import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.GateFamily

/-!
# Guarded circuit normalizer: canonical successful run
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

private theorem replicate_tick_append_cons (count : Nat)
    (output : List NormalizedCircuitSym) :
    List.replicate count .tick ++ .tick :: output =
      .tick :: (List.replicate count .tick ++ output) := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ, ih]

/-- Parse and validate the final output index after its raw tag has already
been consumed. -/
theorem outputIndex_phase (state : State) (outputIndex slack inputCount : Nat)
    (output rows : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[3 * outputIndex + 5]
        (some (cfg (some (.parseOperand .outputGate)) state
          (encNat outputIndex) output rows
          inputCount (outputIndex + slack + 1) 0 0 0)) =
        some (cfg (some .rowsToOutput) finalState [] output rows
          inputCount (outputIndex + slack + 1) 0 0 outputIndex) := by
  rcases operand_phase state .outputGate outputIndex 0 [] output rows inputCount
      (outputIndex + slack + 1) 0 0 with ⟨s₁, h₁⟩
  have h₁' : transition^[outputIndex + 1]
      (some (cfg (some (.parseOperand .outputGate)) state (encNat outputIndex)
        output rows inputCount (outputIndex + slack + 1) 0 0 0)) =
      some (cfg (some .checkTrailing) s₁ [] output rows inputCount
        (outputIndex + slack + 1) outputIndex 0 outputIndex) := by
    simpa [afterOperandLabel, operandRows, operandOutputIndex] using h₁
  have h₂ : transition^[1]
      (some (cfg (some .checkTrailing) s₁ [] output rows inputCount
        (outputIndex + slack + 1) outputIndex 0 outputIndex)) =
      some (cfg (some (.compareOperand .outputGate))
        { s₁ with inputBuffer := none }
        [] output rows inputCount (outputIndex + slack + 1)
        outputIndex 0 outputIndex) := by
    change step (cfg (some .checkTrailing) s₁ [] output rows inputCount
      (outputIndex + slack + 1) outputIndex 0 outputIndex) = _
    exact check_trailing_empty_step s₁ output rows inputCount
      (outputIndex + slack + 1) outputIndex 0 outputIndex
  rcases compareOperand_phase { s₁ with inputBuffer := none } .outputGate
      outputIndex slack inputCount 0 0 outputIndex [] output rows with
    ⟨s₃, h₃⟩
  have h₃' : transition^[outputIndex + 1]
      (some (cfg (some (.compareOperand .outputGate))
        { s₁ with inputBuffer := none }
        [] output rows inputCount (outputIndex + slack + 1)
        outputIndex 0 outputIndex)) =
      some (cfg (some (.restoreBound .outputGate)) s₃ [] output rows
        inputCount slack 0 (outputIndex + 1) outputIndex) := by
    simpa [withBound] using h₃
  rcases restoreBound_phase s₃ .outputGate (outputIndex + 1) slack inputCount
      0 0 outputIndex [] output rows with ⟨s₄, h₄⟩
  have h₄' : transition^[outputIndex + 1]
      (some (cfg (some (.restoreBound .outputGate)) s₃ [] output rows
        inputCount slack 0 (outputIndex + 1) outputIndex)) =
      some (cfg (some (.restoreBound .outputGate)) s₄ [] output rows
        inputCount (outputIndex + slack + 1) 0 0 outputIndex) := by
    simpa [withBound, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h₄
  have h₅ : transition^[1]
      (some (cfg (some (.restoreBound .outputGate)) s₄ [] output rows
        inputCount (outputIndex + slack + 1) 0 0 outputIndex)) =
      some (cfg (some .rowsToOutput) { s₄ with counterPresent := false }
        [] output rows inputCount (outputIndex + slack + 1) 0 0 outputIndex) := by
    change step (cfg (some (.restoreBound .outputGate)) s₄ [] output rows
      inputCount (outputIndex + slack + 1) 0 0 outputIndex) = _
    simpa [afterBoundLabel, afterBoundRows, afterBoundGateCount] using
      restore_bound_done_step s₄ .outputGate [] output rows inputCount
        (outputIndex + slack + 1) 0 outputIndex
  have h₁₂ := step_comp _ _ h₁' h₂
  have h₁₃ := step_comp _ _ h₁₂ h₃'
  have h₁₄ := step_comp _ _ h₁₃ h₄'
  have hfull := step_comp _ _ h₁₄ h₅
  refine ⟨{ s₄ with counterPresent := false }, ?_⟩
  have hsteps : outputIndex + 1 + 1 + (outputIndex + 1) +
      (outputIndex + 1) + 1 = 3 * outputIndex + 5 := by omega
  rw [← hsteps]
  exact hfull

private theorem rowsToOutput_phase (state : State)
    (staged output : List NormalizedCircuitSym)
    (inputCount gateCount outputIndex : Nat) :
    ∃ finalState,
      transition^[staged.length + 1]
        (some (cfg (some .rowsToOutput) state [] output staged
          inputCount gateCount 0 0 outputIndex)) =
        some (cfg (some .emitGateCount) finalState []
          (.fieldEnd :: (staged.reverse ++ output)) []
          inputCount gateCount 0 0 outputIndex) := by
  induction staged generalizing state output with
  | nil =>
      refine ⟨{ state with normalizedBuffer := none }, ?_⟩
      change step (cfg (some .rowsToOutput) state [] output []
        inputCount gateCount 0 0 outputIndex) = _
      simpa using rows_to_output_done_step state output inputCount gateCount 0 0
        outputIndex
  | cons head staged ih =>
      rcases ih { state with normalizedBuffer := some head } (head :: output) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := rows_to_output_step state head staged output inputCount
        gateCount 0 0 outputIndex
      have hfull := step_then (staged.length + 1) hfirst hrun
      simpa [List.reverse_cons, List.append_assoc] using hfull

private theorem emitGateCount_phase (state : State) (count : Nat)
    (output : List NormalizedCircuitSym)
    (inputCount outputIndex : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .emitGateCount) state [] output []
          inputCount count 0 0 outputIndex)) =
        some (cfg (some .emitOutputIndex) finalState []
          (.fieldEnd :: .gateCountMark ::
            (List.replicate count .tick ++ output)) []
          inputCount 0 0 0 outputIndex) := by
  induction count generalizing state output with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .emitGateCount) state [] output []
        inputCount 0 0 0 outputIndex) = _
      exact emit_gate_count_done_step state output inputCount 0 0 outputIndex
  | succ count ih =>
      rcases ih { state with counterPresent := true } (.tick :: output) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := emit_gate_count_tick_step state output inputCount count 0 0
        outputIndex
      have hfull := step_then (count + 1) hfirst hrun
      rw [replicate_tick_append_cons] at hfull
      simpa [List.replicate_succ, List.append_assoc] using hfull

private theorem emitOutputIndex_phase (state : State) (count : Nat)
    (output : List NormalizedCircuitSym) (inputCount : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .emitOutputIndex) state [] output []
          inputCount 0 0 0 count)) =
        some (cfg (some .emitInputCount) finalState []
          (.fieldEnd :: .outputIndexMark ::
            (List.replicate count .tick ++ output)) []
          inputCount 0 0 0 0) := by
  induction count generalizing state output with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .emitOutputIndex) state [] output []
        inputCount 0 0 0 0) = _
      exact emit_output_index_done_step state output inputCount 0 0
  | succ count ih =>
      rcases ih { state with counterPresent := true } (.tick :: output) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := emit_output_index_tick_step state output inputCount 0 0 count
      have hfull := step_then (count + 1) hfirst hrun
      rw [replicate_tick_append_cons] at hfull
      simpa [List.replicate_succ, List.append_assoc] using hfull

private theorem emitInputCount_phase (state : State) (count : Nat)
    (output : List NormalizedCircuitSym) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .emitInputCount) state [] output [] count 0 0 0 0)) =
        some (cfg (some .done) finalState []
          (.validMark :: .inputCountMark ::
            (List.replicate count .tick ++ output)) [] 0 0 0 0 0) := by
  induction count generalizing state output with
  | zero =>
      refine ⟨{ state with counterPresent := false }, ?_⟩
      change step (cfg (some .emitInputCount) state [] output [] 0 0 0 0 0) = _
      exact emit_input_count_done_step state output 0 0
  | succ count ih =>
      rcases ih { state with counterPresent := true } (.tick :: output) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := emit_input_count_tick_step state output count 0 0
      have hfull := step_then (count + 1) hfirst hrun
      rw [replicate_tick_append_cons] at hfull
      simpa [List.replicate_succ, List.append_assoc] using hfull

/-- Record assembled by the final reverse-row and header phases. -/
def normalizedRecordFromParts (inputCount outputIndex gateCount : Nat)
    (rowStream : List NormalizedCircuitSym) : List NormalizedCircuitSym :=
  [.validMark, .inputCountMark] ++ encodeNormalizedNat inputCount ++
    [.outputIndexMark] ++ encodeNormalizedNat outputIndex ++
    [.gateCountMark] ++ encodeNormalizedNat gateCount ++ rowStream

def validFinishSteps (rowStream : List NormalizedCircuitSym)
    (inputCount outputIndex gateCount : Nat) : Nat :=
  (rowStream.length + 1) + (gateCount + 1) + (outputIndex + 1) +
    (inputCount + 1) + 1

/-- Drain reversed rows, prepend the three unary header fields, reset state,
and halt with the exact normalized record. -/
theorem validFinish_phase (state : State) (rowStream : List NormalizedCircuitSym)
    (inputCount outputIndex gateCount : Nat) :
    transition^[validFinishSteps rowStream inputCount outputIndex gateCount]
      (some (cfg (some .rowsToOutput) state [] [] rowStream.reverse
        inputCount gateCount 0 0 outputIndex)) =
      some (_root_.Turing.haltList machine
        (normalizedRecordFromParts inputCount outputIndex gateCount rowStream)) := by
  rcases rowsToOutput_phase state rowStream.reverse [] inputCount gateCount
      outputIndex with ⟨s₁, h₁⟩
  have h₁' : transition^[rowStream.length + 1]
      (some (cfg (some .rowsToOutput) state [] [] rowStream.reverse
        inputCount gateCount 0 0 outputIndex)) =
      some (cfg (some .emitGateCount) s₁ [] (.fieldEnd :: rowStream) []
        inputCount gateCount 0 0 outputIndex) := by
    simpa using h₁
  rcases emitGateCount_phase s₁ gateCount (.fieldEnd :: rowStream)
      inputCount outputIndex with ⟨s₂, h₂⟩
  rcases emitOutputIndex_phase s₂ outputIndex
      (.fieldEnd :: .gateCountMark ::
        (List.replicate gateCount .tick ++ .fieldEnd :: rowStream))
      inputCount with ⟨s₃, h₃⟩
  rcases emitInputCount_phase s₃ inputCount
      (.fieldEnd :: .outputIndexMark ::
        (List.replicate outputIndex .tick ++
          .fieldEnd :: .gateCountMark ::
            (List.replicate gateCount .tick ++ .fieldEnd :: rowStream))) with
    ⟨s₄, h₄⟩
  have h₅ : transition^[1]
      (some (cfg (some .done) s₄ []
        (.validMark :: .inputCountMark ::
          (List.replicate inputCount .tick ++
            .fieldEnd :: .outputIndexMark ::
              (List.replicate outputIndex .tick ++
                .fieldEnd :: .gateCountMark ::
                  (List.replicate gateCount .tick ++ .fieldEnd :: rowStream))))
        [] 0 0 0 0 0)) =
      some (_root_.Turing.haltList machine
        (normalizedRecordFromParts inputCount outputIndex gateCount rowStream)) := by
    change step (cfg (some .done) s₄ []
      (.validMark :: .inputCountMark ::
        (List.replicate inputCount .tick ++
          .fieldEnd :: .outputIndexMark ::
            (List.replicate outputIndex .tick ++
              .fieldEnd :: .gateCountMark ::
                (List.replicate gateCount .tick ++ .fieldEnd :: rowStream))))
      [] 0 0 0 0 0) = _
    simpa [normalizedRecordFromParts, encodeNormalizedNat, List.append_assoc] using
      done_step s₄ (normalizedRecordFromParts inputCount outputIndex gateCount rowStream)
  have h₁₂ := step_comp _ _ h₁' h₂
  have h₁₃ := step_comp _ _ h₁₂ h₃
  have h₁₄ := step_comp _ _ h₁₃ h₄
  have hfull := step_comp _ _ h₁₄ h₅
  simpa [validFinishSteps, Nat.add_assoc] using hfull

/-- Exact successful run on a canonical well-formed circuit encoding. -/
theorem canonical_run (c : Circuit) (hwellFormed : c.WellFormed) :
    ∃ steps,
      transition^[steps]
        (some (_root_.Turing.initList machine (encodeCircuit c))) =
      some (_root_.Turing.haltList machine (encodeNormalizedCircuit c)) := by
  rcases inputCount_phase initialState c.inputCount 0
      (c.gates.flatMap encodeCircuitGate ++ .outputMark :: encNat c.output)
      [] [] 0 0 0 0 with ⟨s₁, h₁⟩
  have h₁' : transition^[c.inputCount + 1]
      (some (cfg (some .inputCount) initialState (encodeCircuit c)
        [] [] 0 0 0 0 0)) =
      some (cfg (some .gates) s₁
        (c.gates.flatMap encodeCircuitGate ++ .outputMark :: encNat c.output)
        [] [] c.inputCount 0 0 0 0) := by
    simpa [encodeCircuit, List.append_assoc] using h₁
  have hinit : _root_.Turing.initList machine (encodeCircuit c) =
      cfg (some .inputCount) initialState (encodeCircuit c) [] [] 0 0 0 0 0 := by
    apply _root_.Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext stack
      cases stack <;>
        simp [cfg, machine, stackContents, _root_.Turing.initList]
  have hvalid : ∀ i (hi : i < c.gates.length),
      (c.gates.get ⟨i, hi⟩).ValidAt c.inputCount (0 + i) := by
    intro i hi
    simpa using hwellFormed.2 i hi
  rcases gateFamily_phase s₁ c.gates 0 c.inputCount hvalid
      (.outputMark :: encNat c.output) [] [] with ⟨s₂, h₂⟩
  have h₂' : transition^[gateFamilyStepsFrom 0 c.gates]
      (some (cfg (some .gates) s₁
        (c.gates.flatMap encodeCircuitGate ++ .outputMark :: encNat c.output)
        [] [] c.inputCount 0 0 0 0)) =
      some (cfg (some .gates) s₂ (.outputMark :: encNat c.output) []
        (encodeNormalizedGateRowsFrom 0 c.gates).reverse
        c.inputCount c.gates.length 0 0 0) := by
    simpa using h₂
  have h₃ : transition^[1]
      (some (cfg (some .gates) s₂ (.outputMark :: encNat c.output) []
        (encodeNormalizedGateRowsFrom 0 c.gates).reverse
        c.inputCount c.gates.length 0 0 0)) =
      some (cfg (some (.parseOperand .outputGate))
        { s₂ with inputBuffer := some .outputMark }
        (encNat c.output) [] (encodeNormalizedGateRowsFrom 0 c.gates).reverse
        c.inputCount c.gates.length 0 0 0) := by
    change step (cfg (some .gates) s₂ (.outputMark :: encNat c.output) []
      (encodeNormalizedGateRowsFrom 0 c.gates).reverse
      c.inputCount c.gates.length 0 0 0) = _
    exact gates_output_step s₂ (encNat c.output) []
      (encodeNormalizedGateRowsFrom 0 c.gates).reverse c.inputCount
      c.gates.length 0 0 0
  obtain ⟨outputSlack, houtput⟩ := Nat.exists_eq_add_of_lt hwellFormed.1
  rcases outputIndex_phase { s₂ with inputBuffer := some .outputMark }
      c.output outputSlack c.inputCount []
      (encodeNormalizedGateRowsFrom 0 c.gates).reverse with ⟨s₄, h₄⟩
  have h₄' : transition^[3 * c.output + 5]
      (some (cfg (some (.parseOperand .outputGate))
        { s₂ with inputBuffer := some .outputMark }
        (encNat c.output) [] (encodeNormalizedGateRowsFrom 0 c.gates).reverse
        c.inputCount c.gates.length 0 0 0)) =
      some (cfg (some .rowsToOutput) s₄ [] []
        (encodeNormalizedGateRowsFrom 0 c.gates).reverse
        c.inputCount c.gates.length 0 0 c.output) := by
    simpa [houtput] using h₄
  have h₅ := validFinish_phase s₄
    (encodeNormalizedGateRowsFrom 0 c.gates) c.inputCount c.output
    c.gates.length
  have h₁₂ := step_comp _ _ h₁' h₂'
  have h₁₃ := step_comp _ _ h₁₂ h₃
  have h₁₄ := step_comp _ _ h₁₃ h₄'
  have hfull := step_comp _ _ h₁₄ h₅
  refine ⟨(c.inputCount + 1) + gateFamilyStepsFrom 0 c.gates + 1 +
    (3 * c.output + 5) +
    validFinishSteps (encodeNormalizedGateRowsFrom 0 c.gates)
      c.inputCount c.output c.gates.length, ?_⟩
  rw [hinit]
  simpa [encodeCircuit, encodeNormalizedCircuit, normalizedRecordFromParts,
    Nat.add_assoc, List.append_assoc] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
