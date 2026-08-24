import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Emitter.GateFamily

/-! # General-circuit formula emitter: canonical record header -/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter

open StateTransition

private abbrev transition := flip Option.bind step

theorem inputCount_phase (state : State) (count offset : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (saved : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .inputCount) state
          (encodeNormalizedNat count ++ input) output offset saved)) =
      some (cfg (some .expectOutput) finalState input
        (.varMark :: .andMark :: output) (offset + count) saved) := by
  induction count generalizing state offset with
  | zero =>
      refine ⟨{ state with inputBuffer := some .fieldEnd }, ?_⟩
      change step (cfg (some .inputCount) state (.fieldEnd :: input) output
        offset saved) = _
      simpa [encodeNormalizedNat] using
        input_count_end_step state input output offset saved
  | succ count ih =>
      have hfirst := input_count_tick_step state
        (encodeNormalizedNat count ++ input) output offset saved
      rcases ih { state with inputBuffer := some .tick } (offset + 1) with
        ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_then (count + 1) hfirst htail
      simpa [encodeNormalizedNat, List.replicate_succ, List.append_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

theorem gateCount_phase (state : State) (count : Nat)
    (input : List NormalizedCircuitSym) (output : List FormulaSym)
    (inputCount saved : Nat) :
    ∃ finalState,
      transition^[count + 1]
        (some (cfg (some .gateCount) state
          (encodeNormalizedNat count ++ input) output inputCount saved)) =
      some (cfg (some .rows) finalState input output inputCount saved) := by
  induction count generalizing state with
  | zero =>
      refine ⟨{ state with inputBuffer := some .fieldEnd }, ?_⟩
      change step (cfg (some .gateCount) state (.fieldEnd :: input) output
        inputCount saved) = _
      simpa [encodeNormalizedNat] using
        gate_count_end_step state input output inputCount saved
  | succ count ih =>
      have hfirst := gate_count_tick_step state
        (encodeNormalizedNat count ++ input) output inputCount saved
      rcases ih { state with inputBuffer := some .tick } with
        ⟨finalState, htail⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_then (count + 1) hfirst htail
      simpa [encodeNormalizedNat, List.replicate_succ,
        List.append_assoc] using hfull

def headerSteps (c : Circuit) : Nat :=
  1 + 1 + (c.inputCount + 1) + 1 +
    ((2 * c.inputCount + 2) + (c.output + 1)) + 1 +
    (c.gates.length + 1)

/-- Parse a canonical guarded header and emit the outer conjunction and output
variable, leaving exactly the chronological row stream. -/
theorem header_phase (c : Circuit) :
    ∃ finalState,
      transition^[headerSteps c]
        (some (_root_.Turing.initList reverseMachine
          (encodeNormalizedCircuit c))) =
      some (cfg (some .rows) finalState
        (encodeNormalizedGateRowsFrom 0 c.gates)
        ((.andMark :: varEnc (c.inputCount + c.output)).reverse)
        c.inputCount 0) := by
  have hinit : _root_.Turing.initList reverseMachine
      (encodeNormalizedCircuit c) =
      cfg (some .start) initialState (encodeNormalizedCircuit c) [] 0 0 := by
    apply _root_.Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext stack
      cases stack <;>
        simp [cfg, reverseMachine, stackContents, _root_.Turing.initList]
  have hstart := start_valid_step initialState
    (.inputCountMark :: encodeNormalizedNat c.inputCount ++
      .outputIndexMark :: encodeNormalizedNat c.output ++
      .gateCountMark :: encodeNormalizedNat c.gates.length ++
      encodeNormalizedGateRowsFrom 0 c.gates) [] 0 0
  have hmarker := expect_input_count_step
    { initialState with inputBuffer := some .validMark }
    (encodeNormalizedNat c.inputCount ++
      .outputIndexMark :: encodeNormalizedNat c.output ++
      .gateCountMark :: encodeNormalizedNat c.gates.length ++
      encodeNormalizedGateRowsFrom 0 c.gates) [] 0 0
  rcases inputCount_phase
      { initialState with inputBuffer := some .inputCountMark }
      c.inputCount 0
      (.outputIndexMark :: encodeNormalizedNat c.output ++
        .gateCountMark :: encodeNormalizedNat c.gates.length ++
        encodeNormalizedGateRowsFrom 0 c.gates) [] 0 with
    ⟨afterCount, hcount⟩
  have houtputMarker := expect_output_step afterCount
    (encodeNormalizedNat c.output ++
      .gateCountMark :: encodeNormalizedNat c.gates.length ++
      encodeNormalizedGateRowsFrom 0 c.gates)
    [.varMark, .andMark] c.inputCount 0
  rcases variable_phase
      { afterCount with inputBuffer := some .outputIndexMark }
      .output c.inputCount c.output
      (.gateCountMark :: encodeNormalizedNat c.gates.length ++
        encodeNormalizedGateRowsFrom 0 c.gates) [.andMark] with
    ⟨afterOutput, houtput⟩
  have hgateMarker := expect_gate_count_step afterOutput
    (encodeNormalizedNat c.gates.length ++
      encodeNormalizedGateRowsFrom 0 c.gates)
    ((varEnc (c.inputCount + c.output)).reverse ++ [.andMark])
    c.inputCount 0
  rcases gateCount_phase
      { afterOutput with inputBuffer := some .gateCountMark }
      c.gates.length (encodeNormalizedGateRowsFrom 0 c.gates)
      ((varEnc (c.inputCount + c.output)).reverse ++ [.andMark])
      c.inputCount 0 with ⟨finalState, hgates⟩
  refine ⟨finalState, ?_⟩
  rw [hinit]
  have h₁ := step_then 0 hstart (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at h₁
  have h₂ := step_then 0 hmarker (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at h₂
  have h₃ := step_then 0 houtputMarker (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at h₃
  have h₄ := step_then 0 hgateMarker (by rfl)
  simp only [Nat.zero_add, Function.iterate_zero_apply] at h₄
  have hcount' := hcount
  simp only [Nat.zero_add, List.append_assoc] at hcount'
  have h₁₂ := step_comp _ _ h₁ h₂
  have h₁₂' :
      transition^[2]
        (some (cfg (some .start) initialState (encodeNormalizedCircuit c)
          [] 0 0)) =
      some (cfg (some .inputCount)
        { initialState with inputBuffer := some .inputCountMark }
        (encodeNormalizedNat c.inputCount ++
          (.outputIndexMark :: (encodeNormalizedNat c.output ++
            (.gateCountMark :: (encodeNormalizedNat c.gates.length ++
              encodeNormalizedGateRowsFrom 0 c.gates))))) [] 0 0) := by
    convert h₁₂ using 1 <;>
      simp [encodeNormalizedCircuit, List.append_assoc]
  have h₁₃ := step_comp _ _ h₁₂' hcount'
  have h₃' :
      transition^[1]
        (some (cfg (some .expectOutput) afterCount
          (.outputIndexMark :: (encodeNormalizedNat c.output ++
            (.gateCountMark :: (encodeNormalizedNat c.gates.length ++
              encodeNormalizedGateRowsFrom 0 c.gates))))
          [.varMark, .andMark] c.inputCount 0)) =
      some (cfg (some (.copyPrefix .output))
        { afterCount with inputBuffer := some .outputIndexMark }
        (encodeNormalizedNat c.output ++
          (.gateCountMark :: (encodeNormalizedNat c.gates.length ++
            encodeNormalizedGateRowsFrom 0 c.gates)))
        [.varMark, .andMark] c.inputCount 0) := by
    convert h₃ using 1 <;> simp [List.append_assoc]
  have h₁₄ := step_comp _ _ h₁₃ h₃'
  have h₁₅ := step_comp _ _ h₁₄ houtput
  have h₁₅' :
      transition^[2 + (c.inputCount + 1) + 1 +
          ((2 * c.inputCount + 2) + (c.output + 1))]
        (some (cfg (some .start) initialState (encodeNormalizedCircuit c)
          [] 0 0)) =
      some (cfg (some .expectGateCount) afterOutput
        (.gateCountMark :: (encodeNormalizedNat c.gates.length ++
          encodeNormalizedGateRowsFrom 0 c.gates))
        ((varEnc (c.inputCount + c.output)).reverse ++ [.andMark])
        c.inputCount 0) := by
    convert h₁₅ using 1 <;>
      simp only [afterOffsetLabel, afterOffsetOutput, varEnc,
        List.replicate_add, List.reverse_cons, List.reverse_append,
        List.reverse_replicate, List.reverse_nil, List.nil_append,
        List.replicate_one,
        List.cons_append, List.append_assoc, Nat.add_assoc]
  have h₁₆ := step_comp _ _ h₁₅' h₄
  have hfull := step_comp _ _ h₁₆ hgates
  have hsteps :
      2 + (c.inputCount + 1) + 1 +
          ((2 * c.inputCount + 2) + (c.output + 1)) + 1 +
          (c.gates.length + 1) = headerSteps c := by
    simp [headerSteps]
  rw [hsteps] at hfull
  simpa only [List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.append_assoc] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Emitter
