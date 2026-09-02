import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.BoundedReject

/-!
# Guarded circuit normalizer: malformed and invalid route bounds

Local parser bounds are kept separate from total semantics.  Later sections
combine these linear/quadratic route estimates under the public sextic budget.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

/-- Linear storage envelope for a malformed unary field and its eventual
cleanup.  The coefficient eight pays for the two staged copies made by an
output operand tick. -/
def malformedFieldBound (input : List CircuitSym)
    (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) : Nat :=
  8 * input.length + output.length + rows.length + inputCount + gateCount +
    operand + saved + outputIndex + 32

/-- A malformed first unary field rejects within the shared linear storage
envelope. -/
theorem malformedInputCount_rejectsIn (state : State)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hdecode : decNat input = none) :
    RejectsIn
      (cfg (some .inputCount) state input output rows inputCount gateCount
        operand saved outputIndex)
      (malformedFieldBound input output rows inputCount gateCount operand saved
        outputIndex) := by
  induction input generalizing state inputCount with
  | nil =>
      have hreject := rejectsInAfterCleanupStep
        { state with inputBuffer := none } [] output rows inputCount gateCount
        operand saved outputIndex
        (input_count_empty_step state output rows inputCount gateCount operand
          saved outputIndex)
      exact RejectsIn.mono hreject (by
        simp [clearAndEmitInvalidSteps, malformedFieldBound]
        omega)
  | cons symbol input ih =>
      cases symbol with
      | argMark =>
          simp only [decNat] at hdecode
          have htail : decNat input = none := by
            cases h : decNat input <;> simp_all
          have hreject := ih { state with inputBuffer := some .argMark }
            (inputCount + 1) htail
          have hfull := RejectsIn.before_step
            (input_count_arg_step state input output rows inputCount gateCount
              operand saved outputIndex) hreject
          exact RejectsIn.mono hfull (by
            simp [malformedFieldBound]
            omega)
      | endMark => simp [decNat] at hdecode
      | inputMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .inputMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .inputMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | constFalseMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .constFalseMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .constFalseMark (by decide) (by decide)
              input output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | constTrueMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .constTrueMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .constTrueMark (by decide) (by decide)
              input output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | notMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .notMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .notMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | andMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .andMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .andMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | orMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .orMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .orMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | outputMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .outputMark } input output rows
            inputCount gateCount operand saved outputIndex
            (input_count_bad_step state .outputMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)

/-- Every malformed gate/output operand rejects within the same linear
storage envelope. -/
theorem malformedOperand_rejectsIn (state : State) (ret : Return)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat)
    (hdecode : decNat input = none) :
    RejectsIn
      (cfg (some (.parseOperand ret)) state input output rows inputCount
        gateCount operand saved outputIndex)
      (malformedFieldBound input output rows inputCount gateCount operand saved
        outputIndex) := by
  induction input generalizing state operand rows outputIndex with
  | nil =>
      have hreject := rejectsInAfterCleanupStep
        { state with inputBuffer := none } [] output rows inputCount gateCount
        operand saved outputIndex
        (operand_empty_step state ret output rows inputCount gateCount operand
          saved outputIndex)
      exact RejectsIn.mono hreject (by
        simp [clearAndEmitInvalidSteps, malformedFieldBound]
        omega)
  | cons symbol input ih =>
      cases symbol with
      | argMark =>
          simp only [decNat] at hdecode
          have htail : decNat input = none := by
            cases h : decNat input <;> simp_all
          let nextRows := operandTickRows ret rows
          let nextOutputIndex := operandTickOutputIndex ret outputIndex
          have hreject := ih
            (state := { state with inputBuffer := some .argMark })
            (operand := operand + 1) (rows := nextRows)
            (outputIndex := nextOutputIndex) htail
          have hfirst := operand_arg_step state ret input output rows inputCount
            gateCount operand saved outputIndex
          have hfirst' :
              step (cfg (some (.parseOperand ret)) state (.argMark :: input)
                output rows inputCount gateCount operand saved outputIndex) =
              some (cfg (some (.parseOperand ret))
                { state with inputBuffer := some .argMark } input output nextRows
                inputCount gateCount (operand + 1) saved nextOutputIndex) := by
            cases ret <;>
              simpa [nextRows, nextOutputIndex, operandTickRows,
                operandTickOutputIndex] using hfirst
          have hfull := RejectsIn.before_step hfirst' hreject
          exact RejectsIn.mono hfull (by
            cases ret <;> simp [malformedFieldBound, nextRows, nextOutputIndex,
              operandTickRows, operandTickOutputIndex] <;> omega)
      | endMark => simp [decNat] at hdecode
      | inputMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .inputMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .inputMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | constFalseMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .constFalseMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .constFalseMark (by decide) (by decide)
              input output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | constTrueMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .constTrueMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .constTrueMark (by decide) (by decide)
              input output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | notMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .notMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .notMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | andMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .andMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .andMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | orMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .orMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .orMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)
      | outputMark =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := some .outputMark } input output rows
            inputCount gateCount operand saved outputIndex
            (operand_bad_step state ret .outputMark (by decide) (by decide) input
              output rows inputCount gateCount operand saved outputIndex)
          exact RejectsIn.mono hreject (by
            simp [clearAndEmitInvalidSteps, malformedFieldBound]
            omega)

/-- Exact budget of the shared failed strict-bound comparison. -/
def firstInvalidRejectBound (ret : Return)
    (bound extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) : Nat :=
  clearAndEmitInvalidSteps input output rows
      (withBound ret 0 inputCount gateCount).1
      (withBound ret 0 inputCount gateCount).2 extra.pred bound outputIndex +
    1 + bound

/-- A parsed operand at least its selected bound rejects within the named
comparison-and-cleanup budget. -/
theorem firstInvalidGate_rejectsIn (state : State) (ret : Return)
    (bound extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    RejectsIn
      (cfg (some (.compareOperand ret)) state input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        (bound + extra) 0 outputIndex)
      (firstInvalidRejectBound ret bound extra inputCount gateCount outputIndex
        input output rows) := by
  rcases compareBoundPrefix_phase state ret bound extra 0 inputCount gateCount
      outputIndex input output rows with ⟨s₁, h₁⟩
  have h₁' : (flip Option.bind step)^[bound]
      (some (cfg (some (.compareOperand ret)) state input output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        (bound + extra) 0 outputIndex)) =
      some (cfg (some (.compareOperand ret)) s₁ input output rows
        (withBound ret 0 inputCount gateCount).1
        (withBound ret 0 inputCount gateCount).2
        extra bound outputIndex) := by
    simpa using h₁
  have hstep := boundZero_reject_step s₁ ret extra inputCount gateCount bound
    outputIndex input output rows
  have hcleanup := rejectsInAfterCleanupStep
    { s₁ with counterPresent := false } input output rows
    (withBound ret 0 inputCount gateCount).1
    (withBound ret 0 inputCount gateCount).2 extra.pred bound outputIndex hstep
  have hfull := RejectsIn.before_steps bound h₁' hcleanup
  simpa [firstInvalidRejectBound, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hfull

/-- Budget for parsing one canonical but out-of-range operand and rejecting it. -/
def invalidOperandRejectBound (ret : Return)
    (bound extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) : Nat :=
  firstInvalidRejectBound ret bound extra inputCount gateCount
      (operandOutputIndex ret (bound + extra) outputIndex) input output
      (operandRows ret (bound + extra) rows) +
    (bound + extra + 1)

theorem invalidOperand_rejectsIn (state : State) (ret : Return)
    (hret : ret ≠ .outputGate) (bound extra inputCount gateCount outputIndex : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym) :
    RejectsIn
      (cfg (some (.parseOperand ret)) state
        (encNat (bound + extra) ++ input) output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2 0 0 outputIndex)
      (invalidOperandRejectBound ret bound extra inputCount gateCount outputIndex
        input output rows) := by
  rcases operand_phase state ret (bound + extra) 0 input output rows
      (withBound ret bound inputCount gateCount).1
      (withBound ret bound inputCount gateCount).2 0 outputIndex with
    ⟨s₁, hparse⟩
  have hparse' : (flip Option.bind step)^[bound + extra + 1]
      (some (cfg (some (.parseOperand ret)) state
        (encNat (bound + extra) ++ input) output rows
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2 0 0 outputIndex)) =
      some (cfg (some (.compareOperand ret)) s₁ input output
        (operandRows ret (bound + extra) rows)
        (withBound ret bound inputCount gateCount).1
        (withBound ret bound inputCount gateCount).2
        (bound + extra) 0
        (operandOutputIndex ret (bound + extra) outputIndex)) := by
    have hlabel : afterOperandLabel ret = .compareOperand ret := by
      cases ret <;> simp_all [afterOperandLabel]
    simpa [hlabel] using hparse
  have hreject := firstInvalidGate_rejectsIn s₁ ret bound extra inputCount
    gateCount (operandOutputIndex ret (bound + extra) outputIndex) input output
    (operandRows ret (bound + extra) rows)
  simpa [invalidOperandRejectBound] using
    RejectsIn.before_steps (bound + extra + 1) hparse' hreject

/-- Tail garbage is rejected in one transition plus exact cleanup. -/
theorem trailingGarbage_rejectsIn (state : State) (head : CircuitSym)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateCount operand saved outputIndex : Nat) :
    RejectsIn
      (cfg (some .checkTrailing) state (head :: input) output rows inputCount
        gateCount operand saved outputIndex)
      (clearAndEmitInvalidSteps input output rows inputCount gateCount operand
        saved outputIndex + 1) := by
  exact rejectsInAfterCleanupStep { state with inputBuffer := some head } input
    output rows inputCount gateCount operand saved outputIndex
    (check_trailing_nonempty_step state head input output rows inputCount
      gateCount operand saved outputIndex)

/-- Generous local envelope for rejecting one canonical invalid gate. -/
def gateLocalRejectBound (capacity : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateIndex : Nat) : Nat :=
  4096 * (capacity + input.length + output.length + rows.length + inputCount +
    gateIndex + 1) ^ 2 + 4096

theorem linear_le_gateLocal (capacity : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateIndex cost : Nat)
    (hcost : cost ≤ 64 * (capacity + input.length + output.length +
      rows.length + inputCount + gateIndex + 1)) :
    cost ≤ gateLocalRejectBound capacity input output rows inputCount
      gateIndex := by
  exact hcost.trans (by
    simp only [gateLocalRejectBound]
    nlinarith)

/-- A canonical gate violating its range/dependency condition rejects within a
quadratic envelope in the available raw capacity and live storage. -/
theorem invalidGate_rejectsIn (state : State) (gate : CircuitGate)
    (gateIndex inputCount capacity : Nat)
    (hinvalid : ¬ gate.ValidAt inputCount gateIndex)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (hcapacity : (encodeCircuitGate gate ++ input).length ≤ capacity) :
    RejectsIn
      (cfg (some .gates) state (encodeCircuitGate gate ++ input) output rows
        inputCount gateIndex 0 0 0)
      (gateLocalRejectBound capacity input output rows inputCount gateIndex) := by
  cases gate with
  | input inputIndex =>
      simp only [CircuitGate.ValidAt] at hinvalid
      have hle : inputCount ≤ inputIndex := Nat.not_lt.mp hinvalid
      obtain ⟨extra, hindex⟩ := Nat.exists_eq_add_of_le hle
      rcases gatePrefix_phase state .input (encNat inputIndex ++ input) output
          rows inputCount gateIndex with ⟨s₁, hprefix⟩
      have hreject := invalidOperand_rejectsIn s₁ .inputGate (by decide)
        inputCount extra 0 gateIndex 0 input output
        (afterRowPrefixRows .input
          (.fieldEnd ::
            (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
      have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
        (by simpa [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount, hindex] using hprefix) hreject
      have hfull' : RejectsIn
          (cfg (some .gates) state
            (encodeCircuitGate (.input inputIndex) ++ input) output rows
            inputCount gateIndex 0 0 0)
          (invalidOperandRejectBound .inputGate inputCount extra 0 gateIndex 0
            input output
            (afterRowPrefixRows .input
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
            (2 * gateIndex + 3)) := by
        simpa [encodeCircuitGate, hindex] using hfull
      exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
        rows inputCount gateIndex _ (by
        simp [invalidOperandRejectBound,
          firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
          operandOutputIndex, afterRowPrefixRows, withBound, encodeCircuitGate,
          encNat, hindex] at hcapacity ⊢
        omega))
  | const value => simp [CircuitGate.ValidAt] at hinvalid
  | not source =>
      simp only [CircuitGate.ValidAt] at hinvalid
      have hle : gateIndex ≤ source := Nat.not_lt.mp hinvalid
      obtain ⟨extra, hsource⟩ := Nat.exists_eq_add_of_le hle
      rcases gatePrefix_phase state .not (encNat source ++ input) output rows
          inputCount gateIndex with ⟨s₁, hprefix⟩
      have hreject := invalidOperand_rejectsIn s₁ .notGate (by decide)
        gateIndex extra inputCount 0 0 input output
        (afterRowPrefixRows .not
          (.fieldEnd ::
            (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
      have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
        (by simpa [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
          afterRowPrefixGateCount, withBound, hsource] using hprefix) hreject
      have hfull' : RejectsIn
          (cfg (some .gates) state (encodeCircuitGate (.not source) ++ input)
            output rows inputCount gateIndex 0 0 0)
          (invalidOperandRejectBound .notGate gateIndex extra inputCount 0 0
            input output
            (afterRowPrefixRows .not
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
            (2 * gateIndex + 3)) := by
        simpa [encodeCircuitGate, hsource] using hfull
      exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
        rows inputCount gateIndex _ (by
        simp [invalidOperandRejectBound,
          firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
          operandOutputIndex, afterRowPrefixRows, withBound, encodeCircuitGate,
          encNat, hsource] at hcapacity ⊢
        omega))
  | and left right =>
      simp only [CircuitGate.ValidAt, not_and_or] at hinvalid
      rcases gatePrefix_phase state .and
          (encNat left ++ encNat right ++ input) output rows inputCount gateIndex
        with ⟨s₁, hprefix⟩
      rcases hinvalid with hleft | hright
      · have hle : gateIndex ≤ left := Nat.not_lt.mp hleft
        obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
        have hreject := invalidOperand_rejectsIn s₁ .andLeft (by decide)
          gateIndex extra inputCount 0 0 (encNat right ++ input) output
          (afterRowPrefixRows .and
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
          (by simpa [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
            afterRowPrefixGateCount, withBound, hleftEq, List.append_assoc]
            using hprefix)
          hreject
        have hfull' : RejectsIn
            (cfg (some .gates) state
              (encodeCircuitGate (.and left right) ++ input) output rows
              inputCount gateIndex 0 0 0)
            (invalidOperandRejectBound .andLeft gateIndex extra inputCount 0 0
              (encNat right ++ input) output
              (afterRowPrefixRows .and
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
              (2 * gateIndex + 3)) := by
          simpa [encodeCircuitGate, hleftEq, List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
          rows inputCount gateIndex _ (by
          simp [invalidOperandRejectBound,
            firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
            operandOutputIndex, afterRowPrefixRows, withBound,
            encodeCircuitGate, encNat, hleftEq] at hcapacity ⊢
          omega))
      · by_cases hleftValid : left < gateIndex
        · obtain ⟨leftSlack, hleftEq⟩ := Nat.exists_eq_add_of_lt hleftValid
          have hle : gateIndex ≤ right := Nat.not_lt.mp hright
          obtain ⟨rightExtra, hrightEq⟩ := Nat.exists_eq_add_of_le hle
          rcases boundedOperand_phase s₁ .andLeft (by decide) left leftSlack
              inputCount 0 0 (encNat right ++ input) output
              (afterRowPrefixRows .and
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
            ⟨s₂, hleftRun⟩
          have hreject := invalidOperand_rejectsIn s₂ .andRight (by decide)
            gateIndex rightExtra inputCount 0 0 input output
            (afterBoundRows .andLeft
              (operandRows .andLeft left
                (afterRowPrefixRows .and
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))))
          have hbound : left + leftSlack + 1 = gateIndex := hleftEq.symm
          have hprefix' := hprefix
          simp [rawGateTag, afterRowPrefixLabel, afterRowPrefixGateCount,
            List.append_assoc] at hprefix'
          have hleftRun' : (flip Option.bind step)^[3 * left + 4]
              (some (cfg (some (.parseOperand .andLeft)) s₁
                (encNat left ++ (encNat right ++ input)) output
                (afterRowPrefixRows .and
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
                inputCount gateIndex 0 0 0)) =
              some (cfg (some (.parseOperand .andRight)) s₂
                (encNat right ++ input) output
                (afterBoundRows .andLeft
                  (operandRows .andLeft left
                    (afterRowPrefixRows .and
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))
                inputCount gateIndex 0 0 0) := by
            simpa [afterBoundLabel, afterBoundGateCount, operandOutputIndex,
              withBound, hbound] using hleftRun
          have hreject' : RejectsIn
              (cfg (some (.parseOperand .andRight)) s₂
                (encNat right ++ input) output
                (afterBoundRows .andLeft
                  (operandRows .andLeft left
                    (afterRowPrefixRows .and
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))
                inputCount gateIndex 0 0 0)
              (invalidOperandRejectBound .andRight gateIndex rightExtra
                inputCount 0 0 input output
                (afterBoundRows .andLeft
                  (operandRows .andLeft left
                    (afterRowPrefixRows .and
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))) := by
            simpa [hrightEq, withBound] using hreject
          have hfull := RejectsIn.before_steps
            ((2 * gateIndex + 3) + (3 * left + 4))
            (step_comp _ _ hprefix' hleftRun') hreject'
          have hfull' : RejectsIn
              (cfg (some .gates) state
                (encodeCircuitGate (.and left right) ++ input) output rows
                inputCount gateIndex 0 0 0)
              (invalidOperandRejectBound .andRight gateIndex rightExtra
                inputCount 0 0 input output
                (afterBoundRows .andLeft
                  (operandRows .andLeft left
                    (afterRowPrefixRows .and
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows))))) +
                ((2 * gateIndex + 3) + (3 * left + 4))) := by
            simpa [encodeCircuitGate, hrightEq, List.append_assoc] using hfull
          exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
            rows inputCount gateIndex _ (by
            simp [invalidOperandRejectBound,
              firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
              operandOutputIndex, afterRowPrefixRows, afterBoundRows, withBound,
              encodeCircuitGate, encNat, hleftEq, hrightEq]
              at hcapacity ⊢
            omega))
        · have hle : gateIndex ≤ left := Nat.not_lt.mp hleftValid
          obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
          have hreject := invalidOperand_rejectsIn s₁ .andLeft (by decide)
            gateIndex extra inputCount 0 0 (encNat right ++ input) output
            (afterRowPrefixRows .and
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
          have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
            (by simpa [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
              afterRowPrefixGateCount, withBound, hleftEq, List.append_assoc]
              using hprefix)
            hreject
          have hfull' : RejectsIn
              (cfg (some .gates) state
                (encodeCircuitGate (.and left right) ++ input) output rows
                inputCount gateIndex 0 0 0)
              (invalidOperandRejectBound .andLeft gateIndex extra inputCount 0 0
                (encNat right ++ input) output
                (afterRowPrefixRows .and
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
                (2 * gateIndex + 3)) := by
            simpa [encodeCircuitGate, hleftEq, List.append_assoc] using hfull
          exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
            rows inputCount gateIndex _ (by
            simp [invalidOperandRejectBound,
              firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
              operandOutputIndex, afterRowPrefixRows, withBound,
              encodeCircuitGate, encNat, hleftEq] at hcapacity ⊢
            omega))
  | or left right =>
      simp only [CircuitGate.ValidAt, not_and_or] at hinvalid
      rcases gatePrefix_phase state .or
          (encNat left ++ encNat right ++ input) output rows inputCount gateIndex
        with ⟨s₁, hprefix⟩
      rcases hinvalid with hleft | hright
      · have hle : gateIndex ≤ left := Nat.not_lt.mp hleft
        obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
        have hreject := invalidOperand_rejectsIn s₁ .orLeft (by decide)
          gateIndex extra inputCount 0 0 (encNat right ++ input) output
          (afterRowPrefixRows .or
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
          (by simpa [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
            afterRowPrefixGateCount, withBound, hleftEq, List.append_assoc]
            using hprefix)
          hreject
        have hfull' : RejectsIn
            (cfg (some .gates) state
              (encodeCircuitGate (.or left right) ++ input) output rows
              inputCount gateIndex 0 0 0)
            (invalidOperandRejectBound .orLeft gateIndex extra inputCount 0 0
              (encNat right ++ input) output
              (afterRowPrefixRows .or
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
              (2 * gateIndex + 3)) := by
          simpa [encodeCircuitGate, hleftEq, List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
          rows inputCount gateIndex _ (by
          simp [invalidOperandRejectBound,
            firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
            operandOutputIndex, afterRowPrefixRows, withBound,
            encodeCircuitGate, encNat, hleftEq] at hcapacity ⊢
          omega))
      · by_cases hleftValid : left < gateIndex
        · obtain ⟨leftSlack, hleftEq⟩ := Nat.exists_eq_add_of_lt hleftValid
          have hle : gateIndex ≤ right := Nat.not_lt.mp hright
          obtain ⟨rightExtra, hrightEq⟩ := Nat.exists_eq_add_of_le hle
          rcases boundedOperand_phase s₁ .orLeft (by decide) left leftSlack
              inputCount 0 0 (encNat right ++ input) output
              (afterRowPrefixRows .or
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
            ⟨s₂, hleftRun⟩
          have hreject := invalidOperand_rejectsIn s₂ .orRight (by decide)
            gateIndex rightExtra inputCount 0 0 input output
            (afterBoundRows .orLeft
              (operandRows .orLeft left
                (afterRowPrefixRows .or
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))))
          have hbound : left + leftSlack + 1 = gateIndex := hleftEq.symm
          have hprefix' := hprefix
          simp [rawGateTag, afterRowPrefixLabel, afterRowPrefixGateCount,
            List.append_assoc] at hprefix'
          have hleftRun' : (flip Option.bind step)^[3 * left + 4]
              (some (cfg (some (.parseOperand .orLeft)) s₁
                (encNat left ++ (encNat right ++ input)) output
                (afterRowPrefixRows .or
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
                inputCount gateIndex 0 0 0)) =
              some (cfg (some (.parseOperand .orRight)) s₂
                (encNat right ++ input) output
                (afterBoundRows .orLeft
                  (operandRows .orLeft left
                    (afterRowPrefixRows .or
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))
                inputCount gateIndex 0 0 0) := by
            simpa [afterBoundLabel, afterBoundGateCount, operandOutputIndex,
              withBound, hbound] using hleftRun
          have hreject' : RejectsIn
              (cfg (some (.parseOperand .orRight)) s₂
                (encNat right ++ input) output
                (afterBoundRows .orLeft
                  (operandRows .orLeft left
                    (afterRowPrefixRows .or
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))
                inputCount gateIndex 0 0 0)
              (invalidOperandRejectBound .orRight gateIndex rightExtra
                inputCount 0 0 input output
                (afterBoundRows .orLeft
                  (operandRows .orLeft left
                    (afterRowPrefixRows .or
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))) := by
            simpa [hrightEq, withBound] using hreject
          have hfull := RejectsIn.before_steps
            ((2 * gateIndex + 3) + (3 * left + 4))
            (step_comp _ _ hprefix' hleftRun') hreject'
          have hfull' : RejectsIn
              (cfg (some .gates) state
                (encodeCircuitGate (.or left right) ++ input) output rows
                inputCount gateIndex 0 0 0)
              (invalidOperandRejectBound .orRight gateIndex rightExtra
                inputCount 0 0 input output
                (afterBoundRows .orLeft
                  (operandRows .orLeft left
                    (afterRowPrefixRows .or
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows))))) +
                ((2 * gateIndex + 3) + (3 * left + 4))) := by
            simpa [encodeCircuitGate, hrightEq, List.append_assoc] using hfull
          exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
            rows inputCount gateIndex _ (by
            simp [invalidOperandRejectBound,
              firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
              operandOutputIndex, afterRowPrefixRows, afterBoundRows, withBound,
              encodeCircuitGate, encNat, hleftEq, hrightEq]
              at hcapacity ⊢
            omega))
        · have hle : gateIndex ≤ left := Nat.not_lt.mp hleftValid
          obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
          have hreject := invalidOperand_rejectsIn s₁ .orLeft (by decide)
            gateIndex extra inputCount 0 0 (encNat right ++ input) output
            (afterRowPrefixRows .or
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
          have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
            (by simpa [encodeCircuitGate, rawGateTag, afterRowPrefixLabel,
              afterRowPrefixGateCount, withBound, hleftEq, List.append_assoc]
              using hprefix)
            hreject
          have hfull' : RejectsIn
              (cfg (some .gates) state
                (encodeCircuitGate (.or left right) ++ input) output rows
                inputCount gateIndex 0 0 0)
              (invalidOperandRejectBound .orLeft gateIndex extra inputCount 0 0
                (encNat right ++ input) output
                (afterRowPrefixRows .or
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
                (2 * gateIndex + 3)) := by
            simpa [encodeCircuitGate, hleftEq, List.append_assoc] using hfull
          exact RejectsIn.mono hfull' (linear_le_gateLocal capacity input output
            rows inputCount gateIndex _ (by
            simp [invalidOperandRejectBound,
              firstInvalidRejectBound, clearAndEmitInvalidSteps, operandRows,
              operandOutputIndex, afterRowPrefixRows, withBound,
              encodeCircuitGate, encNat, hleftEq] at hcapacity ⊢
            omega))

@[simp] private theorem afterRowPrefixLabel_binary (isAnd : Bool) :
    afterRowPrefixLabel (binaryKind isAnd) =
      .parseOperand (binaryLeftReturn isAnd) := by
  cases isAnd <;> rfl

@[simp] private theorem afterRowPrefixGateCount_binary (isAnd : Bool)
    (gateIndex : Nat) :
    afterRowPrefixGateCount (binaryKind isAnd) gateIndex = gateIndex := by
  cases isAnd <;> rfl

@[simp] private theorem afterBoundLabel_binaryLeft (isAnd : Bool) :
    afterBoundLabel (binaryLeftReturn isAnd) =
      .parseOperand (binaryRightReturn isAnd) := by
  cases isAnd <;> rfl

@[simp] private theorem afterBoundGateCount_binaryLeft (isAnd : Bool)
    (gateIndex : Nat) :
    afterBoundGateCount (binaryLeftReturn isAnd) gateIndex = gateIndex := by
  cases isAnd <;> rfl

@[simp] private theorem withBound_binaryLeft (isAnd : Bool)
    (bound inputCount gateCount : Nat) :
    withBound (binaryLeftReturn isAnd) bound inputCount gateCount =
      (inputCount, bound) := by
  cases isAnd <;> rfl

@[simp] private theorem withBound_binaryRight (isAnd : Bool)
    (bound inputCount gateCount : Nat) :
    withBound (binaryRightReturn isAnd) bound inputCount gateCount =
      (inputCount, bound) := by
  cases isAnd <;> rfl

@[simp] private theorem afterBoundRows_binaryLeft (isAnd : Bool)
    (rows : List NormalizedCircuitSym) :
    afterBoundRows (binaryLeftReturn isAnd) rows = rows := by
  cases isAnd <;> rfl

@[simp] private theorem operandRows_binaryLeft (isAnd : Bool) (count : Nat)
    (rows : List NormalizedCircuitSym) :
    operandRows (binaryLeftReturn isAnd) count rows =
      .fieldEnd :: (List.replicate count .tick ++ rows) := by
  cases isAnd <;> rfl

@[simp] private theorem operandOutputIndex_binaryLeft (isAnd : Bool)
    (count outputIndex : Nat) :
    operandOutputIndex (binaryLeftReturn isAnd) count outputIndex =
      outputIndex := by
  cases isAnd <;> rfl

@[simp] private theorem afterRowPrefixRows_binary_length (isAnd : Bool)
    (rows : List NormalizedCircuitSym) :
    (afterRowPrefixRows (binaryKind isAnd) rows).length = rows.length + 1 := by
  cases isAnd <;> simp [binaryKind, afterRowPrefixRows]

private theorem binaryGateDecode_rejectsIn (state : State) (isAnd : Bool)
    (symbols : List CircuitSym) (inputCount gateIndex capacity : Nat)
    (output rows : List NormalizedCircuitSym)
    (hcapacity : (rawGateTag (binaryKind isAnd) :: symbols).length ≤ capacity)
    (hdecode : decodeCircuitGate
      (rawGateTag (binaryKind isAnd) :: symbols) = none) :
    RejectsIn
      (cfg (some .gates) state
        (rawGateTag (binaryKind isAnd) :: symbols) output rows
        inputCount gateIndex 0 0 0)
      (gateLocalRejectBound capacity symbols output rows inputCount gateIndex) := by
  cases hleft : decNat symbols with
  | none =>
      rcases gatePrefix_phase state (binaryKind isAnd) symbols output rows
          inputCount gateIndex with ⟨s₁, hprefix⟩
      have hreject := malformedOperand_rejectsIn s₁
        (binaryLeftReturn isAnd) symbols output
        (afterRowPrefixRows (binaryKind isAnd)
          (.fieldEnd ::
            (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        inputCount gateIndex 0 0 0 hleft
      have hprefix' : (flip Option.bind step)^[2 * gateIndex + 3]
          (some (cfg (some .gates) state
            (rawGateTag (binaryKind isAnd) :: symbols) output rows
            inputCount gateIndex 0 0 0)) =
          some (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₁
            symbols output
            (afterRowPrefixRows (binaryKind isAnd)
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
            inputCount gateIndex 0 0 0) := by
        simpa using hprefix
      have hfull := RejectsIn.before_steps (2 * gateIndex + 3) hprefix' hreject
      exact RejectsIn.mono hfull (linear_le_gateLocal capacity symbols output
        rows inputCount gateIndex _ (by
          simp [malformedFieldBound] at hcapacity ⊢
          omega))
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
        ⟨s₁, hprefix⟩
      by_cases hvalid : left < gateIndex
      · obtain ⟨slack, hleftEq⟩ := Nat.exists_eq_add_of_lt hvalid
        have hbound : left + slack + 1 = gateIndex := hleftEq.symm
        rcases boundedOperand_phase s₁ (binaryLeftReturn isAnd) (by
            cases isAnd <;> decide) left slack inputCount 0 0 middle output
            (afterRowPrefixRows (binaryKind isAnd)
              (.fieldEnd ::
                (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) with
          ⟨s₂, hleftRun⟩
        have hreject := malformedOperand_rejectsIn s₂
          (binaryRightReturn isAnd) middle output
          (afterBoundRows (binaryLeftReturn isAnd)
            (operandRows (binaryLeftReturn isAnd) left
              (afterRowPrefixRows (binaryKind isAnd)
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))))
          inputCount gateIndex 0 0 0 hright
        have hprefix' : (flip Option.bind step)^[2 * gateIndex + 3]
            (some (cfg (some .gates) state
              (rawGateTag (binaryKind isAnd) :: encNat left ++ middle)
              output rows inputCount gateIndex 0 0 0)) =
            some (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₁
              (encNat left ++ middle) output
              (afterRowPrefixRows (binaryKind isAnd)
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
              inputCount gateIndex 0 0 0) := by
          simpa using hprefix
        have hleftRun' : (flip Option.bind step)^[3 * left + 4]
            (some (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₁
              (encNat left ++ middle) output
              (afterRowPrefixRows (binaryKind isAnd)
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
              inputCount gateIndex 0 0 0)) =
            some (cfg (some (.parseOperand (binaryRightReturn isAnd))) s₂
              middle output
              (afterBoundRows (binaryLeftReturn isAnd)
                (operandRows (binaryLeftReturn isAnd) left
                  (afterRowPrefixRows (binaryKind isAnd)
                    (.fieldEnd ::
                      (List.replicate gateIndex .tick ++
                        .gateRowMark :: rows)))))
              inputCount gateIndex 0 0 0) := by
          simpa [hbound] using hleftRun
        have hfull := RejectsIn.before_steps
          ((2 * gateIndex + 3) + (3 * left + 4))
          (step_comp _ _ hprefix' hleftRun') hreject
        have hfull' : RejectsIn
            (cfg (some .gates) state
              (rawGateTag (binaryKind isAnd) :: symbols) output rows
              inputCount gateIndex 0 0 0)
            (malformedFieldBound middle output
                (afterBoundRows (binaryLeftReturn isAnd)
                  (operandRows (binaryLeftReturn isAnd) left
                    (afterRowPrefixRows (binaryKind isAnd)
                      (.fieldEnd ::
                        (List.replicate gateIndex .tick ++
                          .gateRowMark :: rows)))))
                inputCount gateIndex 0 0 0 +
              ((2 * gateIndex + 3) + (3 * left + 4))) := by
          simpa [hsymbols, List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (linear_le_gateLocal capacity symbols output
          rows inputCount gateIndex _ (by
            simp [malformedFieldBound, hsymbols, encNat] at hcapacity ⊢
            omega))
      · have hle : gateIndex ≤ left := Nat.not_lt.mp hvalid
        obtain ⟨extra, hleftEq⟩ := Nat.exists_eq_add_of_le hle
        have hreject := invalidOperand_rejectsIn s₁
          (binaryLeftReturn isAnd) (by cases isAnd <;> decide)
          gateIndex extra inputCount 0 0 middle output
          (afterRowPrefixRows (binaryKind isAnd)
            (.fieldEnd ::
              (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        have hprefix' : (flip Option.bind step)^[2 * gateIndex + 3]
            (some (cfg (some .gates) state
              (rawGateTag (binaryKind isAnd) :: encNat left ++ middle)
              output rows inputCount gateIndex 0 0 0)) =
            some (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₁
              (encNat (gateIndex + extra) ++ middle) output
              (afterRowPrefixRows (binaryKind isAnd)
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
              inputCount gateIndex 0 0 0) := by
          simpa [hleftEq] using hprefix
        have hreject' : RejectsIn
            (cfg (some (.parseOperand (binaryLeftReturn isAnd))) s₁
              (encNat (gateIndex + extra) ++ middle) output
              (afterRowPrefixRows (binaryKind isAnd)
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
              inputCount gateIndex 0 0 0)
            (invalidOperandRejectBound (binaryLeftReturn isAnd) gateIndex extra
              inputCount 0 0 middle output
              (afterRowPrefixRows (binaryKind isAnd)
                (.fieldEnd ::
                  (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))) := by
          simpa using hreject
        have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
          hprefix' hreject'
        have hfull' : RejectsIn
            (cfg (some .gates) state
              (rawGateTag (binaryKind isAnd) :: symbols) output rows
              inputCount gateIndex 0 0 0)
            (invalidOperandRejectBound (binaryLeftReturn isAnd) gateIndex extra
                inputCount 0 0 middle output
                (afterRowPrefixRows (binaryKind isAnd)
                  (.fieldEnd ::
                    (List.replicate gateIndex .tick ++ .gateRowMark :: rows))) +
              (2 * gateIndex + 3)) := by
          simpa [hsymbols, List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (linear_le_gateLocal capacity symbols output
          rows inputCount gateIndex _ (by
            simp [invalidOperandRejectBound, firstInvalidRejectBound,
              clearAndEmitInvalidSteps, hsymbols, hleftEq, encNat]
              at hcapacity ⊢
            omega))

/-- A non-output gate whose structural decoder fails rejects within the local
quadratic gate envelope. -/
theorem gateDecode_rejectsIn (state : State) (symbol : CircuitSym)
    (symbols : List CircuitSym) (inputCount gateIndex capacity : Nat)
    (output rows : List NormalizedCircuitSym)
    (hcapacity : (symbol :: symbols).length ≤ capacity)
    (houtput : symbol ≠ .outputMark)
    (hdecode : decodeCircuitGate (symbol :: symbols) = none) :
    RejectsIn
      (cfg (some .gates) state (symbol :: symbols) output rows
        inputCount gateIndex 0 0 0)
      (gateLocalRejectBound capacity symbols output rows inputCount gateIndex) := by
  cases symbol with
  | inputMark =>
      have hnat : decNat symbols = none := by
        apply Option.eq_none_iff_forall_ne_some.mpr
        rintro ⟨n, rest⟩ hsome
        simp [decodeCircuitGate, hsome] at hdecode
      rcases gatePrefix_phase state .input symbols output rows inputCount
          gateIndex with ⟨s₁, hprefix⟩
      have hreject := malformedOperand_rejectsIn s₁ .inputGate symbols output
        (afterRowPrefixRows .input
          (.fieldEnd ::
            (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        inputCount gateIndex 0 0 0 hnat
      have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
        (by simpa [rawGateTag, afterRowPrefixLabel, afterRowPrefixGateCount]
          using hprefix) hreject
      exact RejectsIn.mono hfull (linear_le_gateLocal capacity symbols output
        rows inputCount gateIndex _ (by
          simp [malformedFieldBound, afterRowPrefixRows] at hcapacity ⊢
          omega))
  | constFalseMark => simp [decodeCircuitGate] at hdecode
  | constTrueMark => simp [decodeCircuitGate] at hdecode
  | notMark =>
      have hnat : decNat symbols = none := by
        apply Option.eq_none_iff_forall_ne_some.mpr
        rintro ⟨n, rest⟩ hsome
        simp [decodeCircuitGate, hsome] at hdecode
      rcases gatePrefix_phase state .not symbols output rows inputCount
          gateIndex with ⟨s₁, hprefix⟩
      have hreject := malformedOperand_rejectsIn s₁ .notGate symbols output
        (afterRowPrefixRows .not
          (.fieldEnd ::
            (List.replicate gateIndex .tick ++ .gateRowMark :: rows)))
        inputCount gateIndex 0 0 0 hnat
      have hfull := RejectsIn.before_steps (2 * gateIndex + 3)
        (by simpa [rawGateTag, afterRowPrefixLabel, afterRowPrefixGateCount]
          using hprefix) hreject
      exact RejectsIn.mono hfull (linear_le_gateLocal capacity symbols output
        rows inputCount gateIndex _ (by
          simp [malformedFieldBound, afterRowPrefixRows] at hcapacity ⊢
          omega))
  | andMark =>
      simpa [binaryKind, rawGateTag] using
        binaryGateDecode_rejectsIn state true symbols inputCount gateIndex
          capacity output rows hcapacity hdecode
  | orMark =>
      simpa [binaryKind, rawGateTag] using
        binaryGateDecode_rejectsIn state false symbols inputCount gateIndex
          capacity output rows hcapacity hdecode
  | outputMark => exact False.elim (houtput rfl)
  | argMark =>
      have hreject := rejectsInAfterCleanupStep
        { state with inputBuffer := some .argMark } symbols output rows inputCount
        gateIndex 0 0 0
        (gates_bad_step state .argMark (Or.inl rfl) symbols output rows
          inputCount gateIndex 0 0 0)
      exact RejectsIn.mono hreject (linear_le_gateLocal capacity symbols output
        rows inputCount gateIndex _ (by
          simp [clearAndEmitInvalidSteps] at hcapacity ⊢
          omega))
  | endMark =>
      have hreject := rejectsInAfterCleanupStep
        { state with inputBuffer := some .endMark } symbols output rows inputCount
        gateIndex 0 0 0
        (gates_bad_step state .endMark (Or.inr rfl) symbols output rows
          inputCount gateIndex 0 0 0)
      exact RejectsIn.mono hreject (linear_le_gateLocal capacity symbols output
        rows inputCount gateIndex _ (by
          simp [clearAndEmitInvalidSteps] at hcapacity ⊢
          omega))

/-- Fixed magnitude for all one-gate work inside a stream of bounded raw
capacity.  `baseStorage` is the output/row storage present before the stream. -/
def streamMagnitude (capacity baseStorage : Nat) : Nat :=
  baseStorage + 8 * (capacity + 1) ^ 2 + 1

def streamUnitBound (capacity baseStorage : Nat) : Nat :=
  4096 * (streamMagnitude capacity baseStorage) ^ 2 + 4096

/-- A fuel-indexed envelope for a malformed remaining gate stream. -/
def gateStreamRejectBound (capacity baseStorage fuel : Nat) : Nat :=
  (fuel + 1) * streamUnitBound capacity baseStorage

theorem gateLocal_le_streamUnit (capacity baseStorage : Nat)
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (inputCount gateIndex : Nat)
    (hinput : input.length ≤ capacity)
    (hinputCount : inputCount ≤ capacity)
    (hgateIndex : gateIndex ≤ capacity)
    (hstorage : output.length + rows.length ≤
      baseStorage + gateIndex * (2 * capacity + 3)) :
    gateLocalRejectBound capacity input output rows inputCount gateIndex ≤
      streamUnitBound capacity baseStorage := by
  have hproduct : gateIndex * (2 * capacity + 3) ≤
      capacity * (2 * capacity + 3) :=
    Nat.mul_le_mul_right (2 * capacity + 3) hgateIndex
  have hbase : capacity + input.length + output.length + rows.length +
      inputCount + gateIndex + 1 ≤ streamMagnitude capacity baseStorage := by
    simp only [streamMagnitude]
    nlinarith
  simp only [gateLocalRejectBound, streamUnitBound]
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hbase 2)) 4096

theorem gateSteps_le_streamUnit (capacity baseStorage gateIndex : Nat)
    (gate : CircuitGate)
    (hgate : (encodeCircuitGate gate).length ≤ capacity)
    (hindex : gateIndex ≤ capacity) :
    gateSteps gateIndex gate ≤ streamUnitBound capacity baseStorage := by
  have hsteps := gateSteps_le_encoding gateIndex gate
  have hlinear : gateSteps gateIndex gate ≤
      64 * streamMagnitude capacity baseStorage := by
    apply hsteps.trans
    simp [streamMagnitude]
    nlinarith
  exact hlinear.trans (by
    simp [streamUnitBound]
    nlinarith)

/-- A structurally malformed remaining gate stream rejects within a uniform
fuel-times-unit bound.  The row-storage invariant records exactly the indexed
rows accumulated by already-consumed gates. -/
theorem gateStreamDecodeNone_rejectsIn (state : State) (fuel : Nat)
    (symbols : List CircuitSym) (inputCount gateIndex : Nat)
    (output rows : List NormalizedCircuitSym) (capacity baseStorage : Nat)
    (hfuel : symbols.length ≤ fuel)
    (hcapacity : symbols.length ≤ capacity)
    (hinputCount : inputCount ≤ capacity)
    (hindexFuel : gateIndex + fuel ≤ capacity)
    (hstorage : output.length + rows.length ≤
      baseStorage + gateIndex * (2 * capacity + 3))
    (hdecode : decodeCircuitGates fuel symbols = none) :
    RejectsIn
      (cfg (some .gates) state symbols output rows inputCount gateIndex 0 0 0)
      (gateStreamRejectBound capacity baseStorage fuel) := by
  induction fuel generalizing state symbols gateIndex rows with
  | zero =>
      have hempty : symbols = [] := by
        cases symbols <;> simp_all
      subst symbols
      have hreject := rejectsInAfterCleanupStep
        { state with inputBuffer := none } [] output rows inputCount gateIndex
        0 0 0 (gates_empty_step state output rows inputCount gateIndex 0 0 0)
      have hlocal : RejectsIn
          (cfg (some .gates) state [] output rows inputCount gateIndex 0 0 0)
          (gateLocalRejectBound capacity [] output rows inputCount gateIndex) :=
        RejectsIn.mono hreject (linear_le_gateLocal capacity [] output rows
          inputCount gateIndex _ (by
            simp [clearAndEmitInvalidSteps]
            omega))
      have hunit := gateLocal_le_streamUnit capacity baseStorage [] output rows
        inputCount gateIndex (by simp) hinputCount (by omega) hstorage
      exact RejectsIn.mono hlocal (by
        simpa [gateStreamRejectBound] using hunit)
  | succ fuel ih =>
      cases symbols with
      | nil =>
          have hreject := rejectsInAfterCleanupStep
            { state with inputBuffer := none } [] output rows inputCount gateIndex
            0 0 0 (gates_empty_step state output rows inputCount gateIndex 0 0 0)
          have hlocal : RejectsIn
              (cfg (some .gates) state [] output rows inputCount gateIndex 0 0 0)
              (gateLocalRejectBound capacity [] output rows inputCount gateIndex) :=
            RejectsIn.mono hreject (linear_le_gateLocal capacity [] output rows
              inputCount gateIndex _ (by
                simp [clearAndEmitInvalidSteps]
                omega))
          have hunit := gateLocal_le_streamUnit capacity baseStorage [] output
            rows inputCount gateIndex (by simp) hinputCount (by omega) hstorage
          exact RejectsIn.mono hlocal (by
            simp [gateStreamRejectBound]
            exact hunit.trans (Nat.le_mul_of_pos_left _ (by omega)))
      | cons symbol symbols =>
          by_cases hout : symbol = .outputMark
          · subst symbol
            have hnat : decNat symbols = none := by
              apply Option.eq_none_iff_forall_ne_some.mpr
              rintro ⟨n, rest⟩ hsome
              simp [decodeCircuitGates, hsome] at hdecode
            have hreject := malformedOperand_rejectsIn
              { state with inputBuffer := some .outputMark } .outputGate symbols
              output rows inputCount gateIndex 0 0 0 hnat
            have htag := gates_output_step state symbols output rows inputCount
              gateIndex 0 0 0
            have hfull := RejectsIn.before_step htag hreject
            have hlocal : RejectsIn
                (cfg (some .gates) state (.outputMark :: symbols) output rows
                  inputCount gateIndex 0 0 0)
                (gateLocalRejectBound capacity symbols output rows inputCount
                  gateIndex) :=
              RejectsIn.mono hfull (linear_le_gateLocal capacity symbols output
                rows inputCount gateIndex _ (by
                  simp [malformedFieldBound]
                  omega))
            have hsymbolsCapacity : symbols.length ≤ capacity :=
              (Nat.le_succ symbols.length).trans (by simpa using hcapacity)
            have hunit := gateLocal_le_streamUnit capacity baseStorage symbols
              output rows inputCount gateIndex hsymbolsCapacity hinputCount
              (by omega) hstorage
            exact RejectsIn.mono hlocal (by
              calc
                gateLocalRejectBound capacity symbols output rows inputCount
                    gateIndex ≤ streamUnitBound capacity baseStorage := hunit
                _ ≤ gateStreamRejectBound capacity baseStorage (fuel + 1) := by
                  simp [gateStreamRejectBound]
                  exact Nat.le_mul_of_pos_left _ (by omega))
          · cases hgate : decodeCircuitGate (symbol :: symbols) with
            | none =>
                have hlocal := gateDecode_rejectsIn state symbol symbols
                  inputCount gateIndex capacity output rows hcapacity hout hgate
                have hsymbolsCapacity : symbols.length ≤ capacity :=
                  (Nat.le_succ symbols.length).trans (by simpa using hcapacity)
                have hunit := gateLocal_le_streamUnit capacity baseStorage
                  symbols output rows inputCount gateIndex hsymbolsCapacity
                  hinputCount (by omega) hstorage
                exact RejectsIn.mono hlocal (by
                  calc
                    gateLocalRejectBound capacity symbols output rows inputCount
                        gateIndex ≤ streamUnitBound capacity baseStorage := hunit
                    _ ≤ gateStreamRejectBound capacity baseStorage
                        (fuel + 1) := by
                      simp [gateStreamRejectBound]
                      exact Nat.le_mul_of_pos_left _ (by omega))
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
                have hrestCapacity : rest.length ≤ capacity := by
                  have hrestLe : rest.length ≤ (symbol :: symbols).length := by
                    rw [hsymbols]
                    simp
                  exact hrestLe.trans hcapacity
                have hgateCapacity : (encodeCircuitGate gate).length ≤
                    capacity := by
                  have hgateLe : (encodeCircuitGate gate).length ≤
                      (symbol :: symbols).length := by
                    rw [hsymbols]
                    simp
                  exact hgateLe.trans hcapacity
                have hcombinedCapacity :
                    (encodeCircuitGate gate ++ rest).length ≤ capacity := by
                  rw [← hsymbols]
                  exact hcapacity
                rw [hsymbols]
                by_cases hvalid : gate.ValidAt inputCount gateIndex
                · rcases gate_phase state gate gateIndex inputCount hvalid rest
                      output rows with ⟨s₁, hrun⟩
                  have hnextStorage : output.length +
                      ((encodeNormalizedGateRow gateIndex gate).reverse ++
                        rows).length ≤
                      baseStorage + (gateIndex + 1) * (2 * capacity + 3) := by
                    rw [List.length_append, List.length_reverse,
                      encodeNormalizedGateRow_length]
                    nlinarith
                  have htail := ih s₁ rest (gateIndex + 1)
                    ((encodeNormalizedGateRow gateIndex gate).reverse ++ rows)
                    hrestFuel hrestCapacity (by omega) hnextStorage hrestDecode
                  have hfull := RejectsIn.before_steps
                    (gateSteps gateIndex gate) hrun htail
                  have hstepBound := gateSteps_le_streamUnit capacity baseStorage
                    gateIndex gate hgateCapacity (by omega)
                  exact RejectsIn.mono hfull (by
                    simp only [gateStreamRejectBound]
                    nlinarith)
                · have hlocal := invalidGate_rejectsIn state gate gateIndex
                      inputCount capacity hvalid rest output rows
                      hcombinedCapacity
                  have hunit := gateLocal_le_streamUnit capacity baseStorage rest
                    output rows inputCount gateIndex hrestCapacity hinputCount
                    (by omega) hstorage
                  exact RejectsIn.mono hlocal (by
                    calc
                      gateLocalRejectBound capacity rest output rows inputCount
                          gateIndex ≤ streamUnitBound capacity baseStorage := hunit
                      _ ≤ gateStreamRejectBound capacity baseStorage
                          (fuel + 1) := by
                        simp [gateStreamRejectBound]
                        exact Nat.le_mul_of_pos_left _ (by omega))

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
