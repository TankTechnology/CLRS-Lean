import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.CanonicalRejectBounds

/-!
# Guarded circuit normalizer: whole malformed-input bounds

The raw decoder has two failure shapes: structural failure while scanning the
gate stream, and a successful structural parse with nonempty trailing input.
This module bounds the latter and then rejoins both cases at the initial
configuration.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

/-- A stream budget plus a linear header fits the public sextic envelope. -/
theorem gateStreamRejectBound_add_le_stepBound (n fuel header : Nat)
    (hfuel : fuel ≤ n) (hheader : header ≤ n + 1) :
    gateStreamRejectBound n 0 fuel + header ≤ stepBound n := by
  let a := n + 1
  have ha : 1 ≤ a := by simp [a]
  have hfuel' : fuel + 1 ≤ a := by omega
  have hunit : streamUnitBound n 0 ≤ 524288 * a ^ 4 := by
    simpa [a] using streamUnitBound_zero_le_quartic n
  have hproduct : gateStreamRejectBound n 0 fuel ≤ 524288 * a ^ 5 := by
    simp only [gateStreamRejectBound]
    calc
      (fuel + 1) * streamUnitBound n 0 ≤ a * (524288 * a ^ 4) :=
        Nat.mul_le_mul hfuel' hunit
      _ = 524288 * a ^ 5 := by ring
  have hpow56 : a ^ 5 ≤ a ^ 6 := pow_le_pow_right₀ ha (by omega)
  have hpow16 : a ≤ a ^ 6 := by
    simpa using (pow_le_pow_right₀ ha (show 1 ≤ 6 by omega))
  change gateStreamRejectBound n 0 fuel + header ≤
    1048576 * a ^ 6 + 1048576
  omega

/-- A decoded gate stream with trailing garbage rejects within the same
fuel-times-unit budget as a structurally malformed stream. -/
theorem gateStreamTrailing_rejectsIn (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputCount gateIndex : Nat)
    (output rows : List NormalizedCircuitSym) (gates : List CircuitGate)
    (outputIndex : Nat) (trailing : List CircuitSym)
    (capacity baseStorage : Nat)
    (hfuel : symbols.length ≤ fuel)
    (hcapacity : symbols.length ≤ capacity)
    (hinputCount : inputCount ≤ capacity)
    (hindexFuel : gateIndex + fuel ≤ capacity)
    (hstorage : output.length + rows.length ≤
      baseStorage + gateIndex * (2 * capacity + 3))
    (hdecode : decodeCircuitGates fuel symbols =
      some (gates, outputIndex, trailing))
    (htrailing : trailing ≠ []) :
    RejectsIn
      (cfg (some .gates) state symbols output rows inputCount gateIndex 0 0 0)
      (gateStreamRejectBound capacity baseStorage fuel) := by
  have hsymbols :=
    eq_encodeCircuitGates_append_of_decodeCircuitGates_eq_some hdecode
  have hraw : (gates.flatMap encodeCircuitGate).length ≤ capacity := by
    have hle : (gates.flatMap encodeCircuitGate).length ≤ symbols.length := by
      rw [hsymbols]
      simp
    exact hle.trans hcapacity
  have hrawFuel : (gates.flatMap encodeCircuitGate).length ≤ fuel := by
    have hle : (gates.flatMap encodeCircuitGate).length ≤ symbols.length := by
      rw [hsymbols]
      simp
    exact hle.trans hfuel
  have hgatesFuel : gates.length ≤ fuel := by
    exact (gates_length_le_flat_encoding gates).trans
      hrawFuel
  have hindex : gateIndex + gates.length ≤ capacity := by omega
  have houtput : outputIndex + 2 ≤ capacity := by
    have hle : outputIndex + 2 ≤ symbols.length := by
      rw [hsymbols]
      simp [encNat]
      omega
    exact hle.trans hcapacity
  have hencodedCapacity :
      (gates.flatMap encodeCircuitGate ++
        .outputMark :: encNat outputIndex ++ trailing).length ≤ capacity := by
    rw [← hsymbols]
    exact hcapacity
  rw [hsymbols]
  by_cases hgates : ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + i)
  · rcases gateFamily_phase state gates gateIndex inputCount hgates
        (.outputMark :: encNat outputIndex ++ trailing) output rows with
      ⟨afterGates, hgaterun⟩
    have htag : step
        (cfg (some .gates) afterGates
          (.outputMark :: encNat outputIndex ++ trailing) output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0) =
        some (cfg (some (.parseOperand .outputGate))
          { afterGates with inputBuffer := some .outputMark }
          (encNat outputIndex ++ trailing) output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0) := by
      exact gates_output_step afterGates (encNat outputIndex ++ trailing) output
        ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
        inputCount (gateIndex + gates.length) 0 0 0
    rcases operand_phase { afterGates with inputBuffer := some .outputMark }
        .outputGate outputIndex 0 trailing output
        ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
        inputCount (gateIndex + gates.length) 0 0 with ⟨afterOutput, hopen⟩
    have hopen' : (flip Option.bind step)^[outputIndex + 1]
        (some (cfg (some (.parseOperand .outputGate))
          { afterGates with inputBuffer := some .outputMark }
          (encNat outputIndex ++ trailing) output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0)) =
        some (cfg (some .checkTrailing) afterOutput trailing output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) outputIndex 0 outputIndex) := by
      simpa [afterOperandLabel, operandRows, operandOutputIndex] using hopen
    cases trailing with
    | nil => contradiction
    | cons head tail =>
        have hnewRows : output.length +
            ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++
              rows).length ≤
            baseStorage + (gateIndex + gates.length) *
              (2 * capacity + 3) := by
          have hadded := normalizedRows_length_le_capacity gateIndex gates
            capacity hindex hraw
          rw [List.length_append, List.length_reverse]
          nlinarith
        have htailCapacity : tail.length ≤ capacity := by
          have hle : tail.length ≤
              (head :: tail).length := by simp
          have htrailingLe : (head :: tail).length ≤
              (gates.flatMap encodeCircuitGate ++
                .outputMark :: encNat outputIndex ++ head :: tail).length := by
            simp
            omega
          exact hle.trans (htrailingLe.trans (by
            simpa using hencodedCapacity))
        have hreject := trailingGarbage_rejectsIn afterOutput head tail output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) outputIndex 0 outputIndex
        have hlinear :
            clearAndEmitInvalidSteps tail output
                ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
                inputCount (gateIndex + gates.length) outputIndex 0 outputIndex +
              1 ≤
            64 * (capacity + tail.length + output.length +
              ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++
                rows).length + inputCount + (gateIndex + gates.length) + 1) := by
          simp [clearAndEmitInvalidSteps]
          omega
        have hlocal := linear_le_gateLocal capacity tail output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) _ hlinear
        have hrejectUnit : RejectsIn
            (cfg (some .checkTrailing) afterOutput (head :: tail) output
              ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
              inputCount (gateIndex + gates.length) outputIndex 0 outputIndex)
            (streamUnitBound capacity baseStorage) :=
          RejectsIn.mono hreject (hlocal.trans
            (gateLocal_le_streamUnit capacity baseStorage tail output
              ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
              inputCount (gateIndex + gates.length) htailCapacity hinputCount
              (by omega) hnewRows))
        have hparsed := RejectsIn.before_steps (outputIndex + 1) hopen'
          hrejectUnit
        have htagged := RejectsIn.before_step htag hparsed
        have hfull := RejectsIn.before_steps
          (gateFamilyStepsFrom gateIndex gates)
          (by simpa [List.append_assoc] using hgaterun) htagged
        have hgateSteps := gateFamilyStepsFrom_le_streamUnits capacity
          baseStorage gateIndex gates hindex hraw
        have hunitLarge : outputIndex + 2 ≤
            streamUnitBound capacity baseStorage := by
          simp [streamUnitBound, streamMagnitude]
          nlinarith
        have hfull' : RejectsIn
            (cfg (some .gates) state
              (gates.flatMap encodeCircuitGate ++
                .outputMark :: encNat outputIndex ++ head :: tail) output rows
              inputCount gateIndex 0 0 0)
            (streamUnitBound capacity baseStorage + (outputIndex + 1) + 1 +
              gateFamilyStepsFrom gateIndex gates) := by
          simpa [List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp only [gateStreamRejectBound]
          have hrowsFuel : gates.length + 2 ≤ fuel + 1 := by
            have hlen : outputIndex + 3 + gates.length ≤ fuel := by
              have hall :
                  (gates.flatMap encodeCircuitGate).length + outputIndex + 3 ≤
                    symbols.length := by
                rw [hsymbols]
                simp [encNat]
                omega
              have hgatesRaw := gates_length_le_flat_encoding gates
              omega
            omega
          nlinarith)
  · have hreject := gateFamily_rejectsIn_of_not_valid state gates gateIndex
        inputCount hgates (.outputMark :: encNat outputIndex ++ trailing)
        output rows capacity baseStorage (by
          simpa [List.append_assoc] using hencodedCapacity) hinputCount hindex
        hstorage
    have hreject' : RejectsIn
        (cfg (some .gates) state
          (gates.flatMap encodeCircuitGate ++
            .outputMark :: encNat outputIndex ++ trailing) output rows
          inputCount gateIndex 0 0 0)
        (gateFamilyRejectBound capacity baseStorage gates) := by
      simpa [List.append_assoc] using hreject
    exact RejectsIn.mono hreject' (by
      simp [gateFamilyRejectBound, gateStreamRejectBound]
      nlinarith)

/-- Every raw input rejected by the public decoder reaches the invalid output
within the public polynomial budget. -/
theorem malformed_rejectsIn (input : List CircuitSym)
    (hdecode : decodeCircuit input = none) :
    RejectsIn (_root_.Turing.initList machine input) (stepBound input.length) := by
  have hinit : _root_.Turing.initList machine input =
      cfg (some .inputCount) initialState input [] [] 0 0 0 0 0 := by
    apply _root_.Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext stack
      cases stack <;>
        simp [cfg, machine, stackContents, _root_.Turing.initList]
  cases hnat : decNat input with
  | none =>
      rw [hinit]
      have hreject := malformedInputCount_rejectsIn initialState input [] []
        0 0 0 0 0 hnat
      exact RejectsIn.mono hreject (by
        simp [malformedFieldBound, stepBound]
        have ha : 1 ≤ input.length + 1 := by omega
        have hpow16 : input.length + 1 ≤ (input.length + 1) ^ 6 := by
          simpa using (pow_le_pow_right₀ ha (show 1 ≤ 6 by omega))
        nlinarith)
  | some decodedNat =>
      rcases decodedNat with ⟨inputCount, rest⟩
      have hinput := eq_encNat_append_of_decNat_eq_some hnat
      have hinputCount : inputCount ≤ input.length := by
        rw [hinput]
        simp [encNat]
      have hrest : rest.length ≤ input.length := by
        rw [hinput]
        simp
      rcases inputCount_phase initialState inputCount 0 rest [] [] 0 0 0 0 with
        ⟨afterCount, hcount⟩
      have hcount' : (flip Option.bind step)^[inputCount + 1]
          (some (cfg (some .inputCount) initialState input [] [] 0 0 0 0 0)) =
          some (cfg (some .gates) afterCount rest [] [] inputCount 0 0 0 0) := by
        simpa [hinput] using hcount
      cases hgates : decodeCircuitGates rest.length rest with
      | none =>
          have hreject := gateStreamDecodeNone_rejectsIn afterCount rest.length
            rest inputCount 0 [] [] input.length 0 (by simp) hrest
            hinputCount (by simpa using hrest) (by simp) hgates
          have hfull := RejectsIn.before_steps (inputCount + 1) hcount' hreject
          rw [hinit]
          exact RejectsIn.mono hfull
            (gateStreamRejectBound_add_le_stepBound input.length rest.length
              (inputCount + 1) hrest (by omega))
      | some decodedGates =>
          rcases decodedGates with ⟨gates, outputIndex, trailing⟩
          have htrailing : trailing ≠ [] := by
            intro hempty
            subst trailing
            simp [decodeCircuit, hnat, hgates] at hdecode
          have hreject := gateStreamTrailing_rejectsIn afterCount rest.length
            rest inputCount 0 [] [] gates outputIndex trailing input.length 0
            (by simp) hrest hinputCount (by simpa using hrest) (by simp)
            hgates htrailing
          have hfull := RejectsIn.before_steps (inputCount + 1) hcount' hreject
          rw [hinit]
          exact RejectsIn.mono hfull
            (gateStreamRejectBound_add_le_stepBound input.length rest.length
              (inputCount + 1) hrest (by omega))

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
