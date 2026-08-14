import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.RejectSteps

/-!
# Concrete verifier: reusable rejecting phases
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition
open _root_.Turing

private abbrev transition := flip Option.bind step

/-- A configuration reaches the canonical one-symbol rejection halt. -/
def Rejects (start : machine.Cfg) : Prop :=
  ∃ steps, transition^[steps] (some start) = some (haltList machine [false])

/-- Any one-step transition into the common cleanup path rejects. -/
theorem rejects_after_cleanup_step (start : machine.Cfg) (state : State)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (gateCount index saved : Nat)
    (hstep : step start = some (cfg (some (.clearInput false)) state input []
      certificate values scratch gateCount index saved)) :
    Rejects start := by
  refine ⟨cleanupSteps input certificate values scratch gateCount index saved + 1, ?_⟩
  exact step_then _ hstep
    (cleanup_phase state false input certificate values scratch gateCount index saved)

/-- Rejection is closed under a preceding concrete step. -/
theorem Rejects.before_step {start next : machine.Cfg}
    (hstep : step start = some next) (hreject : Rejects next) : Rejects start := by
  rcases hreject with ⟨steps, hrun⟩
  exact ⟨steps + 1, step_then steps hstep hrun⟩

/-- Rejection is closed under an exact preceding phase. -/
theorem Rejects.before_steps {start next : machine.Cfg} (phaseSteps : Nat)
    (hrun : transition^[phaseSteps] (some start) = some next)
    (hreject : Rejects next) : Rejects start := by
  rcases hreject with ⟨rejectSteps, hreject⟩
  exact ⟨rejectSteps + phaseSteps,
    step_comp phaseSteps rejectSteps hrun hreject⟩

/-- Consume a specified run of input-arity markers while preserving the
certificate-validity flag. -/
theorem input_count_args_phase (state : State) (count remaining : Nat)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (index saved : Nat) :
    ∃ finalState,
      finalState.validAssignment = state.validAssignment ∧
      transition^[count]
        (some (cfg (some .inputCount) state
          (List.replicate count (some .argMark) ++ input)
          [] certificate values scratch (remaining + count) index saved)) =
        some (cfg (some .inputCount) finalState input [] certificate values scratch
          remaining index saved) := by
  induction count generalizing state remaining with
  | zero => exact ⟨state, rfl, by simp⟩
  | succ count ih =>
      let nextState : State :=
        { state with inputBuffer := some (some .argMark), counterPresent := true }
      rcases ih nextState remaining with ⟨finalState, hvalid, hrun⟩
      refine ⟨finalState, by simpa [nextState] using hvalid, ?_⟩
      have hfirst := input_count_arg_step state
        (List.replicate count (some .argMark) ++ input) [] certificate values scratch
        (remaining + count) index saved
      have hfull := step_then count hfirst hrun
      simpa [nextState, List.replicate_succ, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hfull

/-- Header checking rejects exactly when the certificate count differs from
the declared arity or the scanned certificate contained a non-Boolean symbol. -/
theorem input_count_reject (state : State) (inputCount certificateCount : Nat)
    (input : List (Option CircuitSym)) (certificate values scratch : List Bool)
    (index saved : Nat)
    (hbad : certificateCount ≠ inputCount ∨ state.validAssignment = false) :
    Rejects (cfg (some .inputCount) state
      (List.map some (encNat inputCount) ++ input)
      [] certificate values scratch certificateCount index saved) := by
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
    apply Rejects.before_steps certificateCount hargs'
    exact rejects_after_cleanup_step _ _
      (List.replicate remaining (some .argMark) ++ some .endMark :: input)
      certificate values scratch 0 index saved
      (by
        simpa [List.replicate_succ] using
          input_count_arg_underflow_step afterArgs
            (List.replicate remaining (some .argMark) ++ some .endMark :: input)
            [] certificate values scratch index saved)
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
      apply Rejects.before_steps inputCount hargs'
      exact rejects_after_cleanup_step _ _ input certificate values scratch
        0 index saved
        (input_count_end_invalid_step afterArgs input [] certificate values scratch
          index saved hinvalid')
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
    apply Rejects.before_steps inputCount hargs'
    exact rejects_after_cleanup_step _ _ input certificate values scratch
      extra index saved
      (input_count_end_nonempty_step afterArgs input [] certificate values scratch
        extra index saved)

/-- The circuit input-count parser rejects every malformed unary number. -/
theorem input_count_reject_of_decNat_none (state : State)
    (symbols : List CircuitSym) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) (hdecode : decNat symbols = none) :
    Rejects (cfg (some .inputCount) state (List.map some symbols)
      [] certificate values scratch gateCount index saved) := by
  induction symbols generalizing state gateCount with
  | nil =>
      exact rejects_after_cleanup_step _ _ [] certificate values scratch
        gateCount index saved
        (input_count_eof_reject_step state [] certificate values scratch
          gateCount index saved)
  | cons symbol symbols ih =>
      by_cases harg : symbol = .argMark
      · subst symbol
        simp only [decNat, Option.map_eq_none_iff] at hdecode
        cases gateCount with
        | zero =>
            exact rejects_after_cleanup_step _ _ (List.map some symbols)
              certificate values scratch 0 index saved
              (input_count_arg_underflow_step state (List.map some symbols)
                [] certificate values scratch index saved)
        | succ gateCount =>
            let nextState : State :=
              { state with inputBuffer := some (some .argMark), counterPresent := true }
            have hfirst := input_count_arg_step state (List.map some symbols)
              [] certificate values scratch gateCount index saved
            apply Rejects.before_step (by simpa [nextState] using hfirst)
            exact ih nextState gateCount hdecode
      · by_cases hend : symbol = .endMark
        · subst symbol
          simp [decNat] at hdecode
        · exact rejects_after_cleanup_step _ _ (List.map some symbols)
            certificate values scratch gateCount index saved
            (input_count_bad_symbol_reject_step state symbol harg hend
              (List.map some symbols) [] certificate values scratch gateCount index saved)

/-- Every continuation unary parser rejects malformed unary input. -/
theorem parse_nat_reject_of_decNat_none (state : State) (ret : Return)
    (symbols : List CircuitSym) (certificate values scratch : List Bool)
    (gateCount index saved : Nat) (hdecode : decNat symbols = none) :
    Rejects (cfg (some (.parseNat ret)) state (List.map some symbols)
      [] certificate values scratch gateCount index saved) := by
  induction symbols generalizing state index with
  | nil =>
      exact rejects_after_cleanup_step _ _ [] certificate values scratch
        gateCount index saved
        (parse_nat_eof_reject_step state ret [] certificate values scratch
          gateCount index saved)
  | cons symbol symbols ih =>
      by_cases harg : symbol = .argMark
      · subst symbol
        simp only [decNat, Option.map_eq_none_iff] at hdecode
        let nextState : State := { state with inputBuffer := some (some .argMark) }
        have hfirst := parse_nat_arg_step state ret (List.map some symbols)
          [] certificate values scratch gateCount index saved
        apply Rejects.before_step (by simpa [nextState] using hfirst)
        exact ih nextState (index + 1) hdecode
      · by_cases hend : symbol = .endMark
        · subst symbol
          simp [decNat] at hdecode
        · exact rejects_after_cleanup_step _ _ (List.map some symbols)
            certificate values scratch gateCount index saved
            (parse_nat_bad_symbol_reject_step state ret symbol harg hend
              (List.map some symbols) [] certificate values scratch
              gateCount index saved)

/-- An indexed certificate lookup rejects whenever the requested position is
not present. -/
theorem certificate_lookup_reject (state : State) (certificate : List Bool)
    (index : Nat) (input : List (Option CircuitSym)) (values scratch : List Bool)
    (gateCount saved : Nat) (hout : certificate.length ≤ index) :
    Rejects (cfg (some .certificateLookup) state input [] certificate values scratch
      gateCount index saved) := by
  induction certificate generalizing state index scratch saved with
  | nil =>
      cases index with
      | zero =>
          exact rejects_after_cleanup_step _ _ input [] values scratch gateCount 0 saved
            (certificate_lookup_target_underflow_step state input [] values scratch
              gateCount saved)
      | succ index =>
          exact rejects_after_cleanup_step _ _ input [] values scratch gateCount index saved
            (certificate_lookup_prefix_underflow_step state input [] values scratch
              gateCount index saved)
  | cons bit certificate ih =>
      cases index with
      | zero => simp at hout
      | succ index =>
          let nextState : State :=
            { state with boolBuffer := some bit, counterPresent := true }
          have hfirst := certificate_lookup_prefix_step state bit input [] certificate
            values scratch gateCount index saved
          apply Rejects.before_step hfirst
          apply ih nextState index (bit :: scratch) (saved + 1)
          simpa using hout

/-- A predecessor lookup rejects whenever its source is at least the current
gate count.  This theorem covers both exhausting the counter too early and
the exact-boundary transfer from an empty value prefix. -/
theorem gate_lookup_reject (state : State) (ret : Return)
    (gateCount source : Nat) (input : List (Option CircuitSym))
    (certificate values scratch : List Bool) (saved : Nat)
    (hout : gateCount ≤ source) :
    Rejects (cfg (some (.gateSubtract ret)) state input [] certificate values scratch
      gateCount source saved) := by
  induction gateCount generalizing state source saved with
  | zero =>
      cases source with
      | zero =>
          let nextState : State := { state with counterPresent := false }
          have hfirst := gate_subtract_done_step state ret input [] certificate values
            scratch 0 saved
          apply Rejects.before_step hfirst
          exact rejects_after_cleanup_step _ _ input certificate values scratch 0 0 saved
            (gate_transfer_first_underflow_step nextState ret input [] certificate
              values scratch saved)
      | succ source =>
          exact rejects_after_cleanup_step _ _ input certificate values scratch
            0 source saved
            (gate_subtract_underflow_step state ret input [] certificate values scratch
              source saved)
  | succ gateCount ih =>
      cases source with
      | zero => simp at hout
      | succ source =>
          let nextState : State := { state with counterPresent := true }
          have hfirst := gate_subtract_step state ret input [] certificate values scratch
            gateCount source saved
          apply Rejects.before_step hfirst
          exact ih nextState source (saved + 1) (by omega)

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
