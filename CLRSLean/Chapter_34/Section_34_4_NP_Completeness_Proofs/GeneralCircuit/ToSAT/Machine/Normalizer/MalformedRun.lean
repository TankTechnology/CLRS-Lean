import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.CanonicalRun

/-!
# Guarded circuit normalizer: malformed and rejecting runs

This file first closes the reusable syntax-failure paths.  Each theorem follows
the concrete parser to its first bad symbol and then invokes the single proved
cleanup routine.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

private abbrev transition := flip Option.bind step

private theorem rejectAfterCleanupStep {start : machine.Cfg}
    (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hstep : step start = some (cfg (some .clearInput) state input output rows
      inputCount gateCount operand saved outputIndex)) :
    ∃ steps,
      transition^[steps] (some start) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  have h₁ : transition^[1] (some start) =
      some (cfg (some .clearInput) state input output rows
        inputCount gateCount operand saved outputIndex) := by
    change step start = _
    exact hstep
  have h₂ := clearAndEmitInvalid_phase state input output rows inputCount
    gateCount operand saved outputIndex
  exact ⟨1 + clearAndEmitInvalidSteps input output rows inputCount gateCount
    operand saved outputIndex, step_comp _ _ h₁ h₂⟩

/-- A truncated or mistagged first unary field rejects and halts. -/
theorem malformedInputCount_run (state : State) (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hdecode : decNat input = none) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .inputCount) state input output rows
          inputCount gateCount operand saved outputIndex)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  induction input generalizing state inputCount with
  | nil =>
      apply rejectAfterCleanupStep
        { state with inputBuffer := none } [] output rows inputCount gateCount
          operand saved outputIndex
      exact input_count_empty_step state output rows inputCount gateCount operand
        saved outputIndex
  | cons symbol input ih =>
      cases symbol with
      | argMark =>
          simp only [decNat] at hdecode
          have htail : decNat input = none := by
            cases h : decNat input <;> simp_all
          rcases ih { state with inputBuffer := some .argMark } (inputCount + 1)
              htail with ⟨steps, hrun⟩
          refine ⟨steps + 1, ?_⟩
          have hfirst := input_count_arg_step state input output rows inputCount
            gateCount operand saved outputIndex
          exact step_then steps hfirst hrun
      | endMark => simp [decNat] at hdecode
      | inputMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .inputMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact input_count_bad_step state .inputMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | constFalseMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .constFalseMark } input output rows
              inputCount gateCount operand saved outputIndex
          exact input_count_bad_step state .constFalseMark (by decide) (by decide)
            input output rows inputCount gateCount operand saved outputIndex
      | constTrueMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .constTrueMark } input output rows
              inputCount gateCount operand saved outputIndex
          exact input_count_bad_step state .constTrueMark (by decide) (by decide)
            input output rows inputCount gateCount operand saved outputIndex
      | notMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .notMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact input_count_bad_step state .notMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | andMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .andMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact input_count_bad_step state .andMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | orMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .orMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact input_count_bad_step state .orMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | outputMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .outputMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact input_count_bad_step state .outputMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex

/-- A malformed unary gate/output operand rejects with all partially staged
ticks removed by cleanup. -/
theorem malformedOperand_run (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hdecode : decNat input = none) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some (.parseOperand ret)) state input output rows
          inputCount gateCount operand saved outputIndex)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  induction input generalizing state operand rows outputIndex with
  | nil =>
      apply rejectAfterCleanupStep
        { state with inputBuffer := none } [] output rows inputCount gateCount
          operand saved outputIndex
      exact operand_empty_step state ret output rows inputCount gateCount operand
        saved outputIndex
  | cons symbol input ih =>
      cases symbol with
      | argMark =>
          simp only [decNat] at hdecode
          have htail : decNat input = none := by
            cases h : decNat input <;> simp_all
          let nextRows := operandTickRows ret rows
          let nextOutputIndex := operandTickOutputIndex ret outputIndex
          rcases ih (state := { state with inputBuffer := some .argMark })
              (operand := operand + 1) (rows := nextRows)
              (outputIndex := nextOutputIndex) htail with ⟨steps, hrun⟩
          refine ⟨steps + 1, ?_⟩
          have hfirst := operand_arg_step state ret input output rows inputCount
            gateCount operand saved outputIndex
          have hfirst' :
              step (cfg (some (.parseOperand ret)) state (.argMark :: input)
                output rows inputCount gateCount operand saved outputIndex) =
              some (cfg (some (.parseOperand ret))
                { state with inputBuffer := some .argMark }
                input output nextRows inputCount gateCount (operand + 1) saved
                nextOutputIndex) := by
            cases ret <;>
              simpa [nextRows, nextOutputIndex, operandTickRows,
                operandTickOutputIndex] using hfirst
          exact step_then steps hfirst' hrun
      | endMark => simp [decNat] at hdecode
      | inputMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .inputMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact operand_bad_step state ret .inputMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | constFalseMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .constFalseMark } input output rows
              inputCount gateCount operand saved outputIndex
          exact operand_bad_step state ret .constFalseMark (by decide) (by decide)
            input output rows inputCount gateCount operand saved outputIndex
      | constTrueMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .constTrueMark } input output rows
              inputCount gateCount operand saved outputIndex
          exact operand_bad_step state ret .constTrueMark (by decide) (by decide)
            input output rows inputCount gateCount operand saved outputIndex
      | notMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .notMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact operand_bad_step state ret .notMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | andMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .andMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact operand_bad_step state ret .andMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | orMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .orMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact operand_bad_step state ret .orMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex
      | outputMark =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := some .outputMark } input output rows inputCount
              gateCount operand saved outputIndex
          exact operand_bad_step state ret .outputMark (by decide) (by decide) input
            output rows inputCount gateCount operand saved outputIndex

private theorem gatePrefix_phase (state : State) (kind : GateKind)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount : Nat) :
    ∃ finalState,
      transition^[2 * gateCount + 3]
        (some (cfg (some .gates) state (rawGateTag kind :: input) output rows
          inputCount gateCount 0 0 0)) =
        some (cfg (some (afterRowPrefixLabel kind)) finalState input output
          (afterRowPrefixRows kind
            (.fieldEnd ::
              (List.replicate gateCount .tick ++ .gateRowMark :: rows)))
          inputCount (afterRowPrefixGateCount kind gateCount) 0 0 0) := by
  have h₁ : transition^[1]
      (some (cfg (some .gates) state (rawGateTag kind :: input) output rows
        inputCount gateCount 0 0 0)) =
      some (cfg (some (.rowIndexCopy kind))
        { state with inputBuffer := some (rawGateTag kind) }
        input output (.gateRowMark :: rows) inputCount gateCount 0 0 0) := by
    change step (cfg (some .gates) state (rawGateTag kind :: input) output rows
      inputCount gateCount 0 0 0) = _
    exact gates_tag_step state kind input output rows inputCount gateCount 0 0 0
  rcases rowPrefix_phase
      { state with inputBuffer := some (rawGateTag kind) } kind gateCount input
      output (.gateRowMark :: rows) inputCount 0 0 with ⟨s₂, h₂⟩
  refine ⟨s₂, ?_⟩
  have hfull := step_comp _ _ h₁ h₂
  have hsteps : 1 + (2 * gateCount + 2) = 2 * gateCount + 3 := by omega
  rw [← hsteps]
  exact hfull

private theorem invalidOperand_run (state : State) (ret : Return)
    (hret : ret ≠ .outputGate) (bound extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some (.parseOperand ret)) state
          (encNat (bound + extra) ++ input) output rows
          (withBound ret bound inputCount gateCount).1
          (withBound ret bound inputCount gateCount).2
          0 0 outputIndex)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  rcases operand_phase state ret (bound + extra) 0 input output rows
      (withBound ret bound inputCount gateCount).1
      (withBound ret bound inputCount gateCount).2 0 outputIndex with
    ⟨s₁, h₁⟩
  have h₁' : transition^[bound + extra + 1]
      (some (cfg (some (.parseOperand ret)) state
        (encNat (bound + extra) ++ input) output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        0 0 outputIndex)) =
      some (cfg (some (.compareOperand ret)) s₁ input output
        (operandRows ret (bound + extra) rows)
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        (bound + extra) 0 (operandOutputIndex ret (bound + extra) outputIndex)) := by
    have hlabel : afterOperandLabel ret = .compareOperand ret := by
      cases ret <;> simp_all [afterOperandLabel]
    simpa [hlabel] using h₁
  rcases firstInvalidGate_reject s₁ ret bound extra inputCount gateCount
      (operandOutputIndex ret (bound + extra) outputIndex) input output
      (operandRows ret (bound + extra) rows) with ⟨rejectSteps, hreject⟩
  exact ⟨(bound + extra + 1) + rejectSteps,
    step_comp _ _ h₁' hreject⟩

/-- A canonical gate whose range/dependency condition fails halts with the
single invalid sentinel. -/
theorem invalidGate_run (state : State) (gate : CircuitGate)
    (gateIndex inputCount : Nat) (hinvalid : ¬ gate.ValidAt inputCount gateIndex)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .gates) state
          (encodeCircuitGate gate ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  cases gate with
  | input inputIndex =>
      simp only [CircuitGate.ValidAt] at hinvalid
      have hle : inputCount ≤ inputIndex := Nat.not_lt.mp hinvalid
      obtain ⟨extra, hindex⟩ := Nat.exists_eq_add_of_le hle
      rcases gatePrefix_phase state .input (encNat inputIndex ++ input) output rows
          inputCount gateIndex with ⟨s₁, h₁⟩
      rcases invalidOperand_run s₁ .inputGate (by decide) inputCount extra 0
          gateIndex 0 input output
          (afterRowPrefixRows .input
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
        ⟨rejectSteps, hreject⟩
      refine ⟨(2 * gateIndex + 3) + rejectSteps, ?_⟩
      have h₁' := h₁
      simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
        afterRowPrefixGateCount, hindex] at h₁' hreject ⊢
      exact step_comp _ _ h₁' hreject
  | const value => simp [CircuitGate.ValidAt] at hinvalid
  | not source =>
      simp only [CircuitGate.ValidAt] at hinvalid
      have hle : gateIndex ≤ source := Nat.not_lt.mp hinvalid
      obtain ⟨extra, hsource⟩ := Nat.exists_eq_add_of_le hle
      rcases gatePrefix_phase state .not (encNat source ++ input) output rows
          inputCount gateIndex with ⟨s₁, h₁⟩
      rcases invalidOperand_run s₁ .notGate (by decide) gateIndex extra inputCount
          0 0 input output
          (afterRowPrefixRows .not
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
        ⟨rejectSteps, hreject⟩
      refine ⟨(2 * gateIndex + 3) + rejectSteps, ?_⟩
      have h₁' := h₁
      simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
        afterRowPrefixGateCount, hsource] at h₁' hreject ⊢
      exact step_comp _ _ h₁' hreject
  | and left right =>
      simp only [CircuitGate.ValidAt, not_and_or] at hinvalid
      rcases gatePrefix_phase state .and
          (encNat left ++ encNat right ++ input) output rows inputCount gateIndex with
        ⟨s₁, h₁⟩
      rcases hinvalid with hleft | hright
      · have hle : gateIndex ≤ left := Nat.not_lt.mp hleft
        obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
        rcases invalidOperand_run s₁ .andLeft (by decide) gateIndex extra
            inputCount 0 0 (encNat right ++ input) output
            (afterRowPrefixRows .and
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
          ⟨rejectSteps, hreject⟩
        refine ⟨(2 * gateIndex + 3) + rejectSteps, ?_⟩
        have h₁' := h₁
        simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount, hleftEq, List.append_assoc] at h₁' hreject ⊢
        exact step_comp _ _ h₁' hreject
      · by_cases hleftValid : left < gateIndex
        · obtain ⟨leftSlack, hleftEq⟩ := Nat.exists_eq_add_of_lt hleftValid
          have hle : gateIndex ≤ right := Nat.not_lt.mp hright
          obtain ⟨rightExtra, hrightEq⟩ := Nat.exists_eq_add_of_le hle
          rcases boundedOperand_phase s₁ .andLeft (by decide) left leftSlack
              inputCount 0 0 (encNat right ++ input) output
              (afterRowPrefixRows .and
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
            ⟨s₂, h₂⟩
          rcases invalidOperand_run s₂ .andRight (by decide) gateIndex
              rightExtra inputCount 0 0 input output
              (afterBoundRows .andLeft
                (operandRows .andLeft left
                  (afterRowPrefixRows .and
                    (.fieldEnd ::
                      (List.replicate gateIndex .tick ++ .gateRowMark :: rows))))) with
            ⟨rejectSteps, hreject⟩
          refine ⟨(2 * gateIndex + 3) + (3 * left + 4) + rejectSteps, ?_⟩
          have h₁' := h₁
          have h₂' := h₂
          simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
            afterRowPrefixGateCount, afterBoundLabel, afterBoundGateCount,
            operandOutputIndex, withBound, hleftEq, hrightEq,
            List.append_assoc] at h₁' h₂' hreject ⊢
          exact step_comp _ _ (step_comp _ _ h₁' h₂') hreject
        · have hle : gateIndex ≤ left := Nat.not_lt.mp hleftValid
          obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
          rcases invalidOperand_run s₁ .andLeft (by decide) gateIndex extra
              inputCount 0 0 (encNat right ++ input) output
              (afterRowPrefixRows .and
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
            ⟨rejectSteps, hreject⟩
          refine ⟨(2 * gateIndex + 3) + rejectSteps, ?_⟩
          have h₁' := h₁
          simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
            afterRowPrefixGateCount, hleftEq, List.append_assoc] at h₁' hreject ⊢
          exact step_comp _ _ h₁' hreject
  | or left right =>
      simp only [CircuitGate.ValidAt, not_and_or] at hinvalid
      rcases gatePrefix_phase state .or
          (encNat left ++ encNat right ++ input) output rows inputCount gateIndex with
        ⟨s₁, h₁⟩
      rcases hinvalid with hleft | hright
      · have hle : gateIndex ≤ left := Nat.not_lt.mp hleft
        obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
        rcases invalidOperand_run s₁ .orLeft (by decide) gateIndex extra
            inputCount 0 0 (encNat right ++ input) output
            (afterRowPrefixRows .or
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
          ⟨rejectSteps, hreject⟩
        refine ⟨(2 * gateIndex + 3) + rejectSteps, ?_⟩
        have h₁' := h₁
        simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount, hleftEq, List.append_assoc] at h₁' hreject ⊢
        exact step_comp _ _ h₁' hreject
      · by_cases hleftValid : left < gateIndex
        · obtain ⟨leftSlack, hleftEq⟩ := Nat.exists_eq_add_of_lt hleftValid
          have hle : gateIndex ≤ right := Nat.not_lt.mp hright
          obtain ⟨rightExtra, hrightEq⟩ := Nat.exists_eq_add_of_le hle
          rcases boundedOperand_phase s₁ .orLeft (by decide) left leftSlack
              inputCount 0 0 (encNat right ++ input) output
              (afterRowPrefixRows .or
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
            ⟨s₂, h₂⟩
          rcases invalidOperand_run s₂ .orRight (by decide) gateIndex
              rightExtra inputCount 0 0 input output
              (afterBoundRows .orLeft
                (operandRows .orLeft left
                  (afterRowPrefixRows .or
                    (.fieldEnd ::
                      (List.replicate gateIndex .tick ++ .gateRowMark :: rows))))) with
            ⟨rejectSteps, hreject⟩
          refine ⟨(2 * gateIndex + 3) + (3 * left + 4) + rejectSteps, ?_⟩
          have h₁' := h₁
          have h₂' := h₂
          simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
            afterRowPrefixGateCount, afterBoundLabel, afterBoundGateCount,
            operandOutputIndex, withBound, hleftEq, hrightEq,
            List.append_assoc] at h₁' h₂' hreject ⊢
          exact step_comp _ _ (step_comp _ _ h₁' h₂') hreject
        · have hle : gateIndex ≤ left := Nat.not_lt.mp hleftValid
          obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
          rcases invalidOperand_run s₁ .orLeft (by decide) gateIndex extra
              inputCount 0 0 (encNat right ++ input) output
              (afterRowPrefixRows .or
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
            ⟨rejectSteps, hreject⟩
          refine ⟨(2 * gateIndex + 3) + rejectSteps, ?_⟩
          have h₁' := h₁
          simp [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
            afterRowPrefixGateCount, hleftEq, List.append_assoc] at h₁' hreject ⊢
          exact step_comp _ _ h₁' hreject

private theorem binaryGateDecode_run (state : State) (isAnd : Bool)
    (symbols : List CircuitSym) (inputCount gateIndex : Nat)
    (output rows : List NormalizedCircuitSym)
    (hdecode : decodeCircuitGate
      (rawGateTag (binaryKind isAnd) :: symbols) = none) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .gates) state
          (rawGateTag (binaryKind isAnd) :: symbols) output rows
          inputCount gateIndex 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  cases hleft : decNat symbols with
  | none =>
      rcases gatePrefix_phase state (binaryKind isAnd) symbols output rows
          inputCount gateIndex with ⟨s₁, h₁⟩
      rcases malformedOperand_run s₁ (binaryLeftReturn isAnd) symbols output
          (afterRowPrefixRows (binaryKind isAnd)
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
          inputCount gateIndex 0 0 0 hleft with ⟨rejectSteps, hreject⟩
      refine ⟨2 * gateIndex + 3 + rejectSteps, ?_⟩
      have h₁' := h₁
      cases isAnd <;>
        simp [binaryKind, binaryLeftReturn, rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount] at h₁' hreject ⊢ <;>
        exact step_comp _ _ h₁' hreject
  | some decoded =>
      rcases decoded with ⟨left, middle⟩
      have hright : decNat middle = none := by
        apply Option.eq_none_iff_forall_ne_some.mpr
        rintro ⟨right, rest⟩ hsome
        cases isAnd with
        | false =>
            change decodeCircuitGate (.orMark :: symbols) = none at hdecode
            simp [decodeCircuitGate, hleft, hsome] at hdecode
        | true =>
            change decodeCircuitGate (.andMark :: symbols) = none at hdecode
            simp [decodeCircuitGate, hleft, hsome] at hdecode
      have hsymbols := eq_encNat_append_of_decNat_eq_some hleft
      rcases gatePrefix_phase state (binaryKind isAnd)
          (encNat left ++ middle) output rows inputCount gateIndex with
        ⟨s₁, h₁⟩
      by_cases hvalid : left < gateIndex
      · obtain ⟨slack, hleftEq⟩ := Nat.exists_eq_add_of_lt hvalid
        rcases boundedOperand_phase s₁ (binaryLeftReturn isAnd) (by
            cases isAnd <;> decide) left slack inputCount 0 0 middle output
            (afterRowPrefixRows (binaryKind isAnd)
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
          ⟨s₂, h₂⟩
        rcases malformedOperand_run s₂ (binaryRightReturn isAnd) middle
            output
            (afterBoundRows (binaryLeftReturn isAnd)
              (operandRows (binaryLeftReturn isAnd) left
                (afterRowPrefixRows (binaryKind isAnd)
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))))
            inputCount gateIndex 0 0 0 hright with ⟨rejectSteps, hreject⟩
        refine ⟨(2 * gateIndex + 3) + (3 * left + 4) + rejectSteps, ?_⟩
        have h₁' := h₁
        have h₂' := h₂
        cases isAnd <;>
          simp [binaryKind, binaryLeftReturn, binaryRightReturn, rawGateTag,
            afterRowPrefixLabel, afterRowPrefixGateCount, afterBoundLabel,
            afterBoundGateCount, operandOutputIndex, withBound, hsymbols,
            hleftEq] at h₁' h₂' hreject ⊢ <;>
          exact step_comp _ _ (step_comp _ _ h₁' h₂') hreject
      · have hle : gateIndex ≤ left := Nat.not_lt.mp hvalid
        obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
        rcases invalidOperand_run s₁ (binaryLeftReturn isAnd) (by
            cases isAnd <;> decide) gateIndex extra inputCount 0 0 middle output
            (afterRowPrefixRows (binaryKind isAnd)
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
          ⟨rejectSteps, hreject⟩
        refine ⟨2 * gateIndex + 3 + rejectSteps, ?_⟩
        have h₁' := h₁
        cases isAnd <;>
          simp [binaryKind, binaryLeftReturn, rawGateTag,
            afterRowPrefixLabel, afterRowPrefixGateCount, hsymbols, hleftEq]
            at h₁' hreject ⊢ <;>
          exact step_comp _ _ h₁' hreject

/-- A non-output gate tag whose structural gate decoder fails is rejected by
the exact parser run. -/
theorem gateDecode_run (state : State) (symbol : CircuitSym)
    (symbols : List CircuitSym) (inputCount gateIndex : Nat)
    (output rows : List NormalizedCircuitSym)
    (houtput : symbol ≠ .outputMark)
    (hdecode : decodeCircuitGate (symbol :: symbols) = none) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .gates) state (symbol :: symbols) output rows
          inputCount gateIndex 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  cases symbol with
  | inputMark =>
      have hnat : decNat symbols = none := by
        apply Option.eq_none_iff_forall_ne_some.mpr
        rintro ⟨n, rest⟩ hsome
        simp [decodeCircuitGate, hsome] at hdecode
      rcases gatePrefix_phase state .input symbols output rows inputCount
          gateIndex with ⟨s₁, h₁⟩
      rcases malformedOperand_run s₁ .inputGate symbols output
          (afterRowPrefixRows .input
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
          inputCount gateIndex 0 0 0 hnat with ⟨rejectSteps, hreject⟩
      exact ⟨2 * gateIndex + 3 + rejectSteps,
        step_comp _ _ (by simpa [rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount] using h₁) hreject⟩
  | constFalseMark => simp [decodeCircuitGate] at hdecode
  | constTrueMark => simp [decodeCircuitGate] at hdecode
  | notMark =>
      have hnat : decNat symbols = none := by
        apply Option.eq_none_iff_forall_ne_some.mpr
        rintro ⟨n, rest⟩ hsome
        simp [decodeCircuitGate, hsome] at hdecode
      rcases gatePrefix_phase state .not symbols output rows inputCount gateIndex
        with ⟨s₁, h₁⟩
      rcases malformedOperand_run s₁ .notGate symbols output
          (afterRowPrefixRows .not
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
          inputCount gateIndex 0 0 0 hnat with ⟨rejectSteps, hreject⟩
      exact ⟨2 * gateIndex + 3 + rejectSteps,
        step_comp _ _ (by simpa [rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount] using h₁) hreject⟩
  | andMark =>
      simpa [binaryKind, rawGateTag] using
        binaryGateDecode_run state true symbols inputCount gateIndex output rows
          hdecode
  | orMark =>
      simpa [binaryKind, rawGateTag] using
        binaryGateDecode_run state false symbols inputCount gateIndex output rows
          hdecode
  | outputMark => exact False.elim (houtput rfl)
  | argMark =>
      apply rejectAfterCleanupStep
        { state with inputBuffer := some .argMark } symbols output rows inputCount
          gateIndex 0 0 0
      exact gates_bad_step state .argMark (Or.inl rfl) symbols output
        rows inputCount gateIndex 0 0 0
  | endMark =>
      apply rejectAfterCleanupStep
        { state with inputBuffer := some .endMark } symbols output rows inputCount
          gateIndex 0 0 0
      exact gates_bad_step state .endMark (Or.inr rfl) symbols output
        rows inputCount gateIndex 0 0 0

/-- A gate stream whose structural decoder fails (without artificial fuel
exhaustion) is rejected. -/
theorem gateStreamDecodeNone_run (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputCount gateIndex : Nat)
    (output rows : List NormalizedCircuitSym)
    (hfuel : symbols.length ≤ fuel)
    (hdecode : decodeCircuitGates fuel symbols = none) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .gates) state symbols output rows
          inputCount gateIndex 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  induction fuel generalizing state symbols gateIndex rows with
  | zero =>
      have hempty : symbols = [] := by
        cases symbols <;> simp_all
      subst symbols
      apply rejectAfterCleanupStep
        { state with inputBuffer := none } [] output rows inputCount gateIndex
          0 0 0
      exact gates_empty_step state output rows inputCount gateIndex 0 0 0
  | succ fuel ih =>
      cases symbols with
      | nil =>
          apply rejectAfterCleanupStep
            { state with inputBuffer := none } [] output rows inputCount gateIndex
              0 0 0
          exact gates_empty_step state output rows inputCount gateIndex 0 0 0
      | cons symbol symbols =>
          by_cases hout : symbol = .outputMark
          · subst symbol
            have hnat : decNat symbols = none := by
              apply Option.eq_none_iff_forall_ne_some.mpr
              rintro ⟨n, rest⟩ hsome
              simp [decodeCircuitGates, hsome] at hdecode
            have htag := gates_output_step state symbols output rows inputCount
              gateIndex 0 0 0
            rcases malformedOperand_run
                { state with inputBuffer := some .outputMark } .outputGate
                symbols output rows inputCount gateIndex 0 0 0 hnat with
              ⟨rejectSteps, hreject⟩
            exact ⟨1 + rejectSteps, step_comp _ _ (by
              change step (cfg (some .gates) state
                (.outputMark :: symbols) output rows inputCount gateIndex
                0 0 0) = _
              exact htag) hreject⟩
          · cases hgate : decodeCircuitGate (symbol :: symbols) with
            | none =>
                exact gateDecode_run state symbol symbols inputCount gateIndex
                  output rows hout hgate
            | some decoded =>
                rcases decoded with ⟨gate, rest⟩
                have hrestDecode : decodeCircuitGates fuel rest = none := by
                  cases symbol <;> simp_all [decodeCircuitGates]
                  all_goals
                    exact Option.eq_none_iff_forall_ne_some.mpr (by
                      rintro ⟨gates, outputIndex, trailing⟩ hsome
                      exact hdecode gates outputIndex trailing hsome)
                have hsymbols :=
                  eq_encodeCircuitGate_append_of_decodeCircuitGate_eq_some hgate
                have hgateLength : 1 ≤ (encodeCircuitGate gate).length := by
                  cases gate with
                  | input i => simp [encodeCircuitGate]
                  | const value => cases value <;> simp [encodeCircuitGate]
                  | not source => simp [encodeCircuitGate]
                  | and left right => simp [encodeCircuitGate]
                  | or left right => simp [encodeCircuitGate]
                have hrestFuel : rest.length ≤ fuel := by
                  have hlength := congrArg List.length hsymbols
                  simp only [List.length_cons, List.length_append] at hlength hfuel
                  omega
                rw [hsymbols]
                by_cases hvalid : gate.ValidAt inputCount gateIndex
                · rcases gate_phase state gate gateIndex inputCount hvalid rest
                      output rows with ⟨s₁, hrun⟩
                  rcases ih s₁ rest (gateIndex + 1)
                      ((encodeNormalizedGateRow gateIndex gate).reverse ++ rows)
                      hrestFuel hrestDecode with ⟨rejectSteps, hreject⟩
                  exact ⟨gateSteps gateIndex gate + rejectSteps,
                    step_comp _ _ hrun hreject⟩
                · exact invalidGate_run state gate gateIndex inputCount hvalid
                    rest output rows

/-- A canonical gate family with at least one invalid row rejects at its first
invalid row.  Valid rows before it are normalized normally, so this theorem is
also the induction bridge needed by whole-circuit rejection. -/
theorem gateFamily_reject_of_not_valid (state : State)
    (gates : List CircuitGate) (gateIndex inputCount : Nat)
    (hinvalid : ¬ ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + i))
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .gates) state
          (gates.flatMap encodeCircuitGate ++ input) output rows
          inputCount gateIndex 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  induction gates generalizing state gateIndex rows with
  | nil =>
      exfalso
      apply hinvalid
      intro i hi
      simp at hi
  | cons gate gates ih =>
      by_cases hhead : gate.ValidAt inputCount gateIndex
      · have htail : ¬ ∀ i (hi : i < gates.length),
            (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + 1 + i) := by
          intro hvalid
          apply hinvalid
          intro i hi
          cases i with
          | zero => simpa using hhead
          | succ i =>
              have hi' : i < gates.length := by simpa using hi
              have h := hvalid i hi'
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
        rcases gate_phase state gate gateIndex inputCount hhead
            (gates.flatMap encodeCircuitGate ++ input) output rows with
          ⟨s₁, h₁⟩
        rcases ih (state := s₁) (gateIndex := gateIndex + 1)
            (rows := (encodeNormalizedGateRow gateIndex gate).reverse ++ rows)
            htail with
          ⟨rejectSteps, hreject⟩
        refine ⟨gateSteps gateIndex gate + rejectSteps, ?_⟩
        have h₁' := h₁
        simp [List.append_assoc] at h₁' hreject ⊢
        exact step_comp _ _ h₁' hreject
      · have hgate : ¬ gate.ValidAt inputCount (gateIndex + 0) := by
          simpa using hhead
        simpa [List.append_assoc] using
          invalidGate_run state gate gateIndex inputCount hgate
            (gates.flatMap encodeCircuitGate ++ input) output rows

/-- A canonical output field that names no gate rejects after full parsing and
the mandatory trailing-input check. -/
theorem invalidOutputIndex_run (state : State)
    (gateCount extra inputCount : Nat)
    (output rows : List NormalizedCircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some (.parseOperand .outputGate)) state
          (encNat (gateCount + extra)) output rows
          inputCount gateCount 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  rcases operand_phase state .outputGate (gateCount + extra) 0 [] output rows
      inputCount gateCount 0 0 with ⟨s₁, h₁⟩
  have h₁' : transition^[gateCount + extra + 1]
      (some (cfg (some (.parseOperand .outputGate)) state
        (encNat (gateCount + extra)) output rows inputCount gateCount 0 0 0)) =
      some (cfg (some .checkTrailing) s₁ [] output rows inputCount gateCount
        (gateCount + extra) 0 (gateCount + extra)) := by
    simpa [afterOperandLabel, operandRows, operandOutputIndex] using h₁
  have h₂ : transition^[1]
      (some (cfg (some .checkTrailing) s₁ [] output rows inputCount gateCount
        (gateCount + extra) 0 (gateCount + extra))) =
      some (cfg (some (.compareOperand .outputGate))
        { s₁ with inputBuffer := none } [] output rows inputCount gateCount
        (gateCount + extra) 0 (gateCount + extra)) := by
    change step (cfg (some .checkTrailing) s₁ [] output rows inputCount
      gateCount (gateCount + extra) 0 (gateCount + extra)) = _
    exact check_trailing_empty_step s₁ output rows inputCount gateCount
      (gateCount + extra) 0 (gateCount + extra)
  rcases firstInvalidGate_reject { s₁ with inputBuffer := none }
      .outputGate gateCount extra inputCount 0 (gateCount + extra) [] output rows
    with ⟨rejectSteps, hreject⟩
  exact ⟨(gateCount + extra + 1) + 1 + rejectSteps,
    step_comp _ _ (step_comp _ _ h₁' h₂) hreject⟩

/-- Exact rejecting run on a canonical circuit encoding that fails the circuit
well-formedness predicate. -/
theorem canonical_invalid_run (c : Circuit) (hinvalid : ¬ c.WellFormed) :
    ∃ steps,
      transition^[steps]
        (some (_root_.Turing.initList machine (encodeCircuit c))) =
      some (_root_.Turing.haltList machine [.invalidMark]) := by
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
  by_cases hgates : ∀ i (hi : i < c.gates.length),
      (c.gates.get ⟨i, hi⟩).ValidAt c.inputCount (0 + i)
  · have houtput : ¬ c.output < c.gates.length := by
      intro hlt
      exact hinvalid ⟨hlt, by simpa using hgates⟩
    have hle : c.gates.length ≤ c.output := Nat.not_lt.mp houtput
    obtain ⟨extra, houtputEq⟩ := Nat.exists_eq_add_of_le hle
    rcases gateFamily_phase s₁ c.gates 0 c.inputCount hgates
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
          { s₂ with inputBuffer := some .outputMark } (encNat c.output) []
          (encodeNormalizedGateRowsFrom 0 c.gates).reverse
          c.inputCount c.gates.length 0 0 0) := by
      change step (cfg (some .gates) s₂ (.outputMark :: encNat c.output) []
        (encodeNormalizedGateRowsFrom 0 c.gates).reverse
        c.inputCount c.gates.length 0 0 0) = _
      exact gates_output_step s₂ (encNat c.output) []
        (encodeNormalizedGateRowsFrom 0 c.gates).reverse c.inputCount
        c.gates.length 0 0 0
    rcases invalidOutputIndex_run
        { s₂ with inputBuffer := some .outputMark } c.gates.length extra
        c.inputCount [] (encodeNormalizedGateRowsFrom 0 c.gates).reverse with
      ⟨rejectSteps, hreject⟩
    refine ⟨(c.inputCount + 1) + gateFamilyStepsFrom 0 c.gates + 1 +
      rejectSteps, ?_⟩
    rw [hinit]
    have h₁₂ := step_comp _ _ h₁' h₂'
    have h₁₂' := h₁₂
    rw [houtputEq] at h₁₂'
    have h₃' := h₃
    simp only [houtputEq] at h₃'
    have h₁₃ := step_comp _ _ h₁₂' h₃'
    have hfull := step_comp _ _ h₁₃ hreject
    simpa [houtputEq, Nat.add_assoc] using hfull
  · rcases gateFamily_reject_of_not_valid s₁ c.gates 0 c.inputCount
        hgates (.outputMark :: encNat c.output) [] [] with
      ⟨rejectSteps, hreject⟩
    refine ⟨(c.inputCount + 1) + rejectSteps, ?_⟩
    rw [hinit]
    exact step_comp _ _ h₁' hreject

/-- Any symbol after a completely parsed output field is rejected before the
output bound check. -/
theorem trailingGarbage_run (state : State) (head : CircuitSym)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .checkTrailing) state (head :: input) output rows
          inputCount gateCount operand saved outputIndex)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  apply rejectAfterCleanupStep
    { state with inputBuffer := some head } input output rows inputCount gateCount
      operand saved outputIndex
  exact check_trailing_nonempty_step state head input output rows inputCount
    gateCount operand saved outputIndex

/-- A structurally decoded gate stream with unconsumed trailing symbols is
rejected at the output boundary (or earlier at its first invalid gate). -/
theorem gateStreamTrailing_run (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputCount gateIndex : Nat)
    (output rows : List NormalizedCircuitSym) (gates : List CircuitGate)
    (outputIndex : Nat) (trailing : List CircuitSym)
    (hdecode : decodeCircuitGates fuel symbols =
      some (gates, outputIndex, trailing))
    (htrailing : trailing ≠ []) :
    ∃ steps,
      transition^[steps]
        (some (cfg (some .gates) state symbols output rows
          inputCount gateIndex 0 0 0)) =
        some (_root_.Turing.haltList machine [.invalidMark]) := by
  have hsymbols :=
    eq_encodeCircuitGates_append_of_decodeCircuitGates_eq_some hdecode
  rw [hsymbols]
  by_cases hgates : ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + i)
  · rcases gateFamily_phase state gates gateIndex inputCount hgates
        (.outputMark :: encNat outputIndex ++ trailing) output rows with
      ⟨s₁, h₁⟩
    have h₂ : transition^[1]
        (some (cfg (some .gates) s₁
          (.outputMark :: encNat outputIndex ++ trailing) output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0)) =
        some (cfg (some (.parseOperand .outputGate))
          { s₁ with inputBuffer := some .outputMark }
          (encNat outputIndex ++ trailing) output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0) := by
      change step (cfg (some .gates) s₁
        (.outputMark :: encNat outputIndex ++ trailing) output
        ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
        inputCount (gateIndex + gates.length) 0 0 0) = _
      exact gates_output_step s₁ (encNat outputIndex ++ trailing) output
        ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
        inputCount (gateIndex + gates.length) 0 0 0
    rcases operand_phase { s₁ with inputBuffer := some .outputMark }
        .outputGate outputIndex 0 trailing output
        ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
        inputCount (gateIndex + gates.length) 0 0 with ⟨s₃, h₃⟩
    have h₃' : transition^[outputIndex + 1]
        (some (cfg (some (.parseOperand .outputGate))
          { s₁ with inputBuffer := some .outputMark }
          (encNat outputIndex ++ trailing) output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) 0 0 0)) =
        some (cfg (some .checkTrailing) s₃ trailing output
          ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
          inputCount (gateIndex + gates.length) outputIndex 0 outputIndex) := by
      simpa [afterOperandLabel, operandRows, operandOutputIndex] using h₃
    cases trailing with
    | nil => contradiction
    | cons head tail =>
        rcases trailingGarbage_run s₃ head tail output
            ((encodeNormalizedGateRowsFrom gateIndex gates).reverse ++ rows)
            inputCount (gateIndex + gates.length) outputIndex 0 outputIndex with
          ⟨rejectSteps, hreject⟩
        refine ⟨gateFamilyStepsFrom gateIndex gates + 1 +
          (outputIndex + 1) + rejectSteps, ?_⟩
        have h₁' := h₁
        simp [List.append_assoc] at h₁' ⊢
        exact step_comp _ _ (step_comp _ _ (step_comp _ _ h₁' h₂) h₃')
          hreject
  · simpa [List.append_assoc] using
      gateFamily_reject_of_not_valid state gates gateIndex inputCount hgates
        (.outputMark :: encNat outputIndex ++ trailing) output rows

/-- Every input rejected by the public circuit decoder reaches the canonical
invalid record. -/
theorem malformed_run (input : List CircuitSym)
    (hdecode : decodeCircuit input = none) :
    ∃ steps,
      transition^[steps]
        (some (_root_.Turing.initList machine input)) =
      some (_root_.Turing.haltList machine [.invalidMark]) := by
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
      exact malformedInputCount_run initialState input [] [] 0 0 0 0 0 hnat
  | some decodedNat =>
      rcases decodedNat with ⟨inputCount, rest⟩
      have hinput := eq_encNat_append_of_decNat_eq_some hnat
      rcases inputCount_phase initialState inputCount 0 rest [] [] 0 0 0 0 with
        ⟨s₁, h₁⟩
      have h₁' : transition^[inputCount + 1]
          (some (cfg (some .inputCount) initialState input [] [] 0 0 0 0 0)) =
          some (cfg (some .gates) s₁ rest [] [] inputCount 0 0 0 0) := by
        simpa [hinput] using h₁
      cases hgates : decodeCircuitGates rest.length rest with
      | none =>
          rcases gateStreamDecodeNone_run s₁ rest.length rest inputCount 0
              [] [] (by omega) hgates with ⟨rejectSteps, hreject⟩
          refine ⟨(inputCount + 1) + rejectSteps, ?_⟩
          rw [hinit]
          exact step_comp _ _ h₁' hreject
      | some decodedGates =>
          rcases decodedGates with ⟨gates, outputIndex, trailing⟩
          have htrailing : trailing ≠ [] := by
            intro hempty
            subst trailing
            simp [decodeCircuit, hnat, hgates] at hdecode
          rcases gateStreamTrailing_run s₁ rest.length rest inputCount 0
              [] [] gates outputIndex trailing hgates htrailing with
            ⟨rejectSteps, hreject⟩
          refine ⟨(inputCount + 1) + rejectSteps, ?_⟩
          rw [hinit]
          exact step_comp _ _ h₁' hreject

/-- Unbounded exact correctness of the guarded normalizer on every raw input.
The runtime layer separately upgrades this total semantic theorem to one
uniform polynomial bound. -/
theorem normalizer_run (input : List CircuitSym) :
    ∃ steps,
      transition^[steps]
        (some (_root_.Turing.initList machine input)) =
      some (_root_.Turing.haltList machine (normalizeGeneralCircuit input)) := by
  cases hdecode : decodeCircuit input with
  | none =>
      simpa [normalizeGeneralCircuit, hdecode] using malformed_run input hdecode
  | some c =>
      have hcanonical := encodeCircuit_of_decodeCircuit_eq_some hdecode
      subst input
      by_cases hwellFormed : c.WellFormed
      · simpa [normalizeGeneralCircuit, decodeCircuit_encodeCircuit,
          hwellFormed] using canonical_run c hwellFormed
      · simpa [normalizeGeneralCircuit, decodeCircuit_encodeCircuit,
          hwellFormed] using canonical_invalid_run c hwellFormed

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
