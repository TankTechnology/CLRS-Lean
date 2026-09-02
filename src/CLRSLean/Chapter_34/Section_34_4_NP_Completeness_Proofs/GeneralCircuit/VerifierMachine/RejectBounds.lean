import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.BoundedReject

/-!
# Concrete verifier: local rejection bounds

This module gives explicit linear budgets for the cleanup, unary parsing, and
failed lookup routes of the general-circuit verifier.  These local bounds are
the quantitative base cases for the later malformed-circuit envelope.

Main results:

- Definition `cleanup_rejectsIn`: exact cleanup runtime.
- Definition `input_count_rejectsIn`: bounded invalid-header rejection.
- Definitions `input_count_rejectsIn_of_decNat_none` and
  `parse_nat_rejectsIn_of_decNat_none`: malformed unary parsing bounds.
- Definitions `certificate_lookup_rejectsIn` and `gate_lookup_rejectsIn`:
  bounded failed predecessor lookups.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- Cleanup reaches the requested canonical Boolean halt in its exact phase cost. -/
def cleanup_in_time (state : State) (answer : Bool)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    EvalsToInTime step
      (cfg (some (.clearInput answer)) state input [] certificate values scratch
        gateCount index saved)
      (some (haltList machine [answer]))
      (cleanupSteps input certificate values scratch gateCount index saved) :=
  { steps := cleanupSteps input certificate values scratch gateCount index saved
    evals_in_steps :=
      cleanup_phase state answer input certificate values scratch gateCount index saved
    steps_le_m := Nat.le_refl _ }

/-- Rejection cleanup reaches the canonical false halt in its exact phase cost. -/
theorem cleanup_rejectsIn (state : State)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) :
    RejectsIn
      (cfg (some (.clearInput false)) state input [] certificate values scratch
        gateCount index saved)
      (cleanupSteps input certificate values scratch gateCount index saved) :=
  ⟨cleanup_in_time state false input certificate values scratch gateCount index saved⟩

/-- Linear envelope for invalid declared-input-count routes. -/
def inputCountRejectBound (inputCount certificateCount : Nat)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (index saved : Nat) : Nat :=
  inputCount + certificateCount + input.length + certificate.length +
    values.length + scratch.length + index + saved + 10

/-- Header checking rejects within a linear budget whenever the certificate
count differs from the declared arity or the certificate alphabet is invalid. -/
theorem input_count_rejectsIn (state : State) (inputCount certificateCount : Nat)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (index saved : Nat)
    (hbad : certificateCount ≠ inputCount ∨ state.validAssignment = false) :
    RejectsIn (cfg (some .inputCount) state
      (List.map some (encNat inputCount) ++ input)
      [] certificate values scratch certificateCount index saved)
      (inputCountRejectBound inputCount certificateCount input certificate values
        scratch index saved) := by
  rcases Nat.lt_trichotomy certificateCount inputCount with hshort | heq | hlong
  · obtain ⟨remaining, hinputCount⟩ :
        ∃ remaining, inputCount = certificateCount + remaining + 1 := by
      exact ⟨inputCount - certificateCount - 1, by omega⟩
    rcases input_count_args_phase state certificateCount 0
        (List.replicate (remaining + 1) (some .argMark) ++
          some .endMark :: input) certificate values scratch index saved with
      ⟨afterArgs, _, hargs⟩
    have hstream : List.map some (encNat inputCount) ++ input =
        List.replicate certificateCount (some .argMark) ++
          (List.replicate (remaining + 1) (some .argMark) ++
            some .endMark :: input) := by
      simp only [encNat, List.map_append, List.map_replicate, List.map_cons,
        List.map_nil]
      rw [hinputCount, show certificateCount + remaining + 1 =
        certificateCount + (remaining + 1) by omega,
        List.replicate_add certificateCount (remaining + 1)
          (some CircuitSym.argMark : Option CircuitSym)]
      simp [List.replicate_add, List.append_assoc]
    have hargs' : transition^[certificateCount]
        (some (cfg (some .inputCount) state
          (List.map some (encNat inputCount) ++ input)
          [] certificate values scratch certificateCount index saved)) =
        some (cfg (some .inputCount) afterArgs
          (List.replicate (remaining + 1) (some .argMark) ++
            some .endMark :: input)
          [] certificate values scratch 0 index saved) := by
      rw [hstream]
      simpa only [Nat.zero_add] using hargs
    have hreject := rejectsIn_after_cleanup_step _ _
      (List.replicate remaining (some .argMark) ++ some .endMark :: input)
      certificate values scratch 0 index saved
      (by
        simpa [List.replicate_succ] using
          input_count_arg_underflow_step afterArgs
            (List.replicate remaining (some .argMark) ++ some .endMark :: input)
            [] certificate values scratch index saved)
    have hfull := RejectsIn.before_steps certificateCount hargs' hreject
    exact RejectsIn.mono hfull (by
      simp [cleanupSteps, inputCountRejectBound]
      omega)
  · subst certificateCount
    rcases hbad with hne | hinvalid
    · exact False.elim (hne rfl)
    · rcases input_count_args_phase state inputCount 0
          (some .endMark :: input) certificate values scratch index saved with
        ⟨afterArgs, hvalid, hargs⟩
      have hinvalid' : afterArgs.validAssignment = false := by
        rw [hvalid]
        exact hinvalid
      have hargs' : transition^[inputCount]
          (some (cfg (some .inputCount) state
            (List.map some (encNat inputCount) ++ input)
            [] certificate values scratch inputCount index saved)) =
          some (cfg (some .inputCount) afterArgs (some .endMark :: input)
            [] certificate values scratch 0 index saved) := by
        simpa [encNat, List.map_append, List.append_assoc] using hargs
      have hreject := rejectsIn_after_cleanup_step _ _ input certificate values scratch
        0 index saved
        (input_count_end_invalid_step afterArgs input [] certificate values scratch
          index saved hinvalid')
      have hfull := RejectsIn.before_steps inputCount hargs' hreject
      exact RejectsIn.mono hfull (by
        simp [cleanupSteps, inputCountRejectBound]
        omega)
  · obtain ⟨extra, hcertificateCount⟩ :
        ∃ extra, certificateCount = inputCount + extra + 1 := by
      exact ⟨certificateCount - inputCount - 1, by omega⟩
    rcases input_count_args_phase state inputCount (extra + 1)
        (some .endMark :: input) certificate values scratch index saved with
      ⟨afterArgs, _, hargs⟩
    have hargs' : transition^[inputCount]
        (some (cfg (some .inputCount) state
          (List.map some (encNat inputCount) ++ input)
          [] certificate values scratch certificateCount index saved)) =
        some (cfg (some .inputCount) afterArgs (some .endMark :: input)
          [] certificate values scratch (extra + 1) index saved) := by
      simpa [encNat, hcertificateCount, List.map_append, List.append_assoc,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hargs
    have hreject := rejectsIn_after_cleanup_step _ _ input certificate values scratch
      extra index saved
      (input_count_end_nonempty_step afterArgs input [] certificate values scratch
        extra index saved)
    have hfull := RejectsIn.before_steps inputCount hargs' hreject
    exact RejectsIn.mono hfull (by
      simp [cleanupSteps, inputCountRejectBound]
      omega)

/-- Linear budget for malformed circuit-input-count unary streams. -/
def inputCountMalformedBound (symbols : List CircuitSym)
    (certificate values scratch : List Bool) (gateCount index saved : Nat) : Nat :=
  symbols.length + certificate.length + values.length + scratch.length +
    gateCount + index + saved + 10

/-- The circuit input-count parser rejects every malformed unary number within
the explicit linear budget. -/
theorem input_count_rejectsIn_of_decNat_none (state : State)
    (symbols : List CircuitSym) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) (hdecode : decNat symbols = none) :
    RejectsIn (cfg (some .inputCount) state (List.map some symbols)
      [] certificate values scratch gateCount index saved)
      (inputCountMalformedBound symbols certificate values scratch gateCount index saved) := by
  induction symbols generalizing state gateCount with
  | nil =>
      have hreject := rejectsIn_after_cleanup_step _ _ [] certificate values scratch
        gateCount index saved
        (input_count_eof_reject_step state [] certificate values scratch
          gateCount index saved)
      exact RejectsIn.mono hreject (by
        simp [cleanupSteps, inputCountMalformedBound])
  | cons symbol symbols ih =>
      by_cases harg : symbol = .argMark
      · subst symbol
        simp only [decNat, Option.map_eq_none_iff] at hdecode
        cases gateCount with
        | zero =>
            have hreject := rejectsIn_after_cleanup_step _ _ (List.map some symbols)
              certificate values scratch 0 index saved
              (input_count_arg_underflow_step state (List.map some symbols)
                [] certificate values scratch index saved)
            exact RejectsIn.mono hreject (by
              simp [cleanupSteps, inputCountMalformedBound])
        | succ gateCount =>
            let nextState : State :=
              { state with inputBuffer := some (some .argMark), counterPresent := true }
            have hfirst := input_count_arg_step state (List.map some symbols)
              [] certificate values scratch gateCount index saved
            have htail := ih nextState gateCount hdecode
            have hfull := RejectsIn.before_step (by simpa [nextState] using hfirst) htail
            exact RejectsIn.mono hfull (by
              simp [inputCountMalformedBound]
              omega)
      · by_cases hend : symbol = .endMark
        · subst symbol
          simp [decNat] at hdecode
        ·
          have hreject := rejectsIn_after_cleanup_step _ _ (List.map some symbols)
            certificate values scratch gateCount index saved
            (input_count_bad_symbol_reject_step state symbol harg hend
              (List.map some symbols) [] certificate values scratch gateCount index saved)
          exact RejectsIn.mono hreject (by
            simp [cleanupSteps, inputCountMalformedBound])

/-- Linear budget for malformed continuation unary streams.  The doubled
symbol coefficient pays for the parser's growing index stack. -/
def parseNatMalformedBound (symbols : List CircuitSym)
    (certificate values scratch : List Bool) (gateCount index saved : Nat) : Nat :=
  2 * symbols.length + certificate.length + values.length + scratch.length +
    gateCount + index + saved + 10

/-- Every continuation unary parser rejects malformed input within the
explicit linear budget. -/
theorem parse_nat_rejectsIn_of_decNat_none (state : State) (ret : Return)
    (symbols : List CircuitSym) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) (hdecode : decNat symbols = none) :
    RejectsIn (cfg (some (.parseNat ret)) state (List.map some symbols)
      [] certificate values scratch gateCount index saved)
      (parseNatMalformedBound symbols certificate values scratch gateCount index saved) := by
  induction symbols generalizing state index with
  | nil =>
      have hreject := rejectsIn_after_cleanup_step _ _ [] certificate values scratch
        gateCount index saved
        (parse_nat_eof_reject_step state ret [] certificate values scratch
          gateCount index saved)
      exact RejectsIn.mono hreject (by
        simp [cleanupSteps, parseNatMalformedBound])
  | cons symbol symbols ih =>
      by_cases harg : symbol = .argMark
      · subst symbol
        simp only [decNat, Option.map_eq_none_iff] at hdecode
        let nextState : State := { state with inputBuffer := some (some .argMark) }
        have hfirst := parse_nat_arg_step state ret (List.map some symbols)
          [] certificate values scratch gateCount index saved
        have htail := ih nextState (index + 1) hdecode
        have hfull := RejectsIn.before_step (by simpa [nextState] using hfirst) htail
        exact RejectsIn.mono hfull (by
          simp [parseNatMalformedBound]
          omega)
      · by_cases hend : symbol = .endMark
        · subst symbol
          simp [decNat] at hdecode
        ·
          have hreject := rejectsIn_after_cleanup_step _ _ (List.map some symbols)
            certificate values scratch gateCount index saved
            (parse_nat_bad_symbol_reject_step state ret symbol harg hend
              (List.map some symbols) [] certificate values scratch
              gateCount index saved)
          exact RejectsIn.mono hreject (by
            simp [cleanupSteps, parseNatMalformedBound]
            omega)

/-- Linear budget for a failed certificate lookup. -/
def certificateLookupRejectBound (certificate : List Bool) (index : Nat)
    (input : List (Option CircuitSym)) (values scratch : List Bool)
    (gateCount saved : Nat) : Nat :=
  2 * certificate.length + index + input.length + values.length +
    scratch.length + gateCount + saved + 10

/-- An absent certificate position is rejected within the explicit lookup
budget. -/
theorem certificate_lookup_rejectsIn (state : State) (certificate : List Bool)
    (index : Nat) (input : List (Option CircuitSym)) (values scratch : List Bool)
    (gateCount saved : Nat) (hout : certificate.length ≤ index) :
    RejectsIn (cfg (some .certificateLookup) state input [] certificate values scratch
      gateCount index saved)
      (certificateLookupRejectBound certificate index input values scratch gateCount saved) := by
  induction certificate generalizing state index scratch saved with
  | nil =>
      cases index with
      | zero =>
          have hreject := rejectsIn_after_cleanup_step _ _ input [] values scratch gateCount 0 saved
            (certificate_lookup_target_underflow_step state input [] values scratch
              gateCount saved)
          exact RejectsIn.mono hreject (by
            simp [cleanupSteps, certificateLookupRejectBound])
      | succ index =>
          have hreject := rejectsIn_after_cleanup_step _ _ input [] values scratch gateCount index saved
            (certificate_lookup_prefix_underflow_step state input [] values scratch
              gateCount index saved)
          exact RejectsIn.mono hreject (by
            simp [cleanupSteps, certificateLookupRejectBound]
            omega)
  | cons bit certificate ih =>
      cases index with
      | zero => simp at hout
      | succ index =>
          let nextState : State :=
            { state with boolBuffer := some bit, counterPresent := true }
          have hfirst := certificate_lookup_prefix_step state bit input [] certificate
            values scratch gateCount index saved
          have htail := ih nextState index (bit :: scratch) (saved + 1) (by simpa using hout)
          have hfull := RejectsIn.before_step hfirst htail
          exact RejectsIn.mono hfull (by
            simp [certificateLookupRejectBound]
            omega)

/-- Linear budget for a failed predecessor lookup in the gate-value stack. -/
def gateLookupRejectBound (gateCount source : Nat)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (saved : Nat) : Nat :=
  gateCount + source + input.length + certificate.length + values.length +
    scratch.length + saved + 11

/-- A predecessor source outside the computed gate prefix is rejected within
the explicit lookup budget. -/
theorem gate_lookup_rejectsIn (state : State) (ret : Return)
    (gateCount source : Nat) (input : List (Option CircuitSym))
    (certificate values scratch : List Bool) (saved : Nat)
    (hout : gateCount ≤ source) :
    RejectsIn (cfg (some (.gateSubtract ret)) state input [] certificate values scratch
      gateCount source saved)
      (gateLookupRejectBound gateCount source input certificate values scratch saved) := by
  induction gateCount generalizing state source saved with
  | zero =>
      cases source with
      | zero =>
          let nextState : State := { state with counterPresent := false }
          have hfirst := gate_subtract_done_step state ret input [] certificate values
            scratch 0 saved
          have hreject := rejectsIn_after_cleanup_step _ _ input certificate values scratch 0 0 saved
            (gate_transfer_first_underflow_step nextState ret input [] certificate
              values scratch saved)
          have hfull := RejectsIn.before_step hfirst hreject
          exact RejectsIn.mono hfull (by
            simp [cleanupSteps, gateLookupRejectBound])
      | succ source =>
          have hreject := rejectsIn_after_cleanup_step _ _ input certificate values scratch
            0 source saved
            (gate_subtract_underflow_step state ret input [] certificate values scratch
              source saved)
          exact RejectsIn.mono hreject (by
            simp [cleanupSteps, gateLookupRejectBound]
            omega)
  | succ gateCount ih =>
      cases source with
      | zero => simp at hout
      | succ source =>
          let nextState : State := { state with counterPresent := true }
          have hfirst := gate_subtract_step state ret input [] certificate values scratch
            gateCount source saved
          have htail := ih nextState source (saved + 1) (by omega)
          have hfull := RejectsIn.before_step hfirst htail
          exact RejectsIn.mono hfull (by
            simp [gateLookupRejectBound]
            omega)

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
