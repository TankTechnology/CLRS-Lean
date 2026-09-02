import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.CertificatePhases

/-!
# Concrete verifier: restoring indexed lookups
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-! ## Certificate lookup -/

/-- Move exactly the requested certificate prefix to scratch. -/
theorem certificate_prefix_phase (state : State) (pre tail : List Bool)
    (input : List (Option CircuitSym)) (output values scratch : List Bool)
    (gateCount saved : Nat) :
    ∃ finalState,
      transition^[pre.length]
        (some (cfg (some .certificateLookup) state input output (pre ++ tail)
          values scratch gateCount pre.length saved)) =
        some (cfg (some .certificateLookup) finalState input output tail values
          (pre.reverse ++ scratch) gateCount 0 (saved + pre.length)) := by
  induction pre generalizing state scratch saved with
  | nil => exact ⟨state, by simp⟩
  | cons bit rest ih =>
      let nextState : State := { state with boolBuffer := some bit, counterPresent := true }
      rcases ih nextState (bit :: scratch) (saved + 1) with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := certificate_lookup_prefix_step state bit input output
        (rest ++ tail) values scratch gateCount rest.length saved
      have hcomposed := step_then rest.length hfirst hrun
      simpa [nextState, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hcomposed

/-- Restore every Boolean moved to scratch, preserving its original order. -/
theorem certificate_restore_phase (state : State) (value : Bool) (moved : List Bool)
    (input : List (Option CircuitSym)) (output certificate values : List Bool)
    (gateCount index : Nat) :
    ∃ finalState,
      transition^[moved.length]
        (some (cfg (some (.certificateRestore value)) state input output certificate values
          moved gateCount index moved.length)) =
        some (cfg (some (.certificateRestore value)) finalState input output
          (moved.reverse ++ certificate) values [] gateCount index 0) := by
  induction moved generalizing state certificate with
  | nil => exact ⟨state, by simp⟩
  | cons bit rest ih =>
      let nextState : State := { state with boolBuffer := some bit, counterPresent := true }
      rcases ih nextState (bit :: certificate) with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := certificate_restore_step state value bit input output certificate
        values rest gateCount index rest.length
      have hcomposed := step_then rest.length hfirst hrun
      simpa [nextState, List.reverse_cons, List.append_assoc] using hcomposed

/-- A successful certificate lookup is non-destructive and appends the selected
bit as the next computed gate value. -/
theorem certificate_lookup_phase (state : State) (pre suffix : List Bool)
    (bit : Bool) (input : List (Option CircuitSym)) (output values : List Bool)
    (gateCount : Nat) :
    ∃ finalState,
      transition^[2 * pre.length + 3]
        (some (cfg (some .certificateLookup) state input output
          (pre ++ bit :: suffix) values [] gateCount pre.length 0)) =
        some (cfg (some .gates) finalState input output
          (pre ++ bit :: suffix) (bit :: values) [] (gateCount + 1) 0 0) := by
  rcases certificate_prefix_phase state pre (bit :: suffix) input output values []
      gateCount 0 with ⟨afterPrefix, hprefix⟩
  have hprefix' :
      transition^[pre.length]
        (some (cfg (some .certificateLookup) state input output
          (pre ++ bit :: suffix) values [] gateCount pre.length 0)) =
        some (cfg (some .certificateLookup) afterPrefix input output (bit :: suffix)
          values pre.reverse gateCount 0 pre.length) := by
    simpa using hprefix
  let afterTarget : State :=
    { afterPrefix with boolBuffer := some bit, counterPresent := false }
  have htarget :
      transition^[1]
        (some (cfg (some .certificateLookup) afterPrefix input output (bit :: suffix)
          values pre.reverse gateCount 0 pre.length)) =
        some (cfg (some (.certificateRestore bit)) afterTarget input output suffix
          values (bit :: pre.reverse) gateCount 0 (pre.length + 1)) := by
    change step (cfg (some .certificateLookup) afterPrefix input output (bit :: suffix)
      values pre.reverse gateCount 0 pre.length) = _
    exact certificate_lookup_target_step afterPrefix bit input output suffix values
      pre.reverse gateCount pre.length
  rcases certificate_restore_phase afterTarget bit (bit :: pre.reverse) input output
      suffix values gateCount 0 with ⟨afterRestore, hrestore⟩
  have hrestore' :
      transition^[pre.length + 1]
        (some (cfg (some (.certificateRestore bit)) afterTarget input output suffix
          values (bit :: pre.reverse) gateCount 0 (pre.length + 1))) =
        some (cfg (some (.certificateRestore bit)) afterRestore input output
          ((bit :: pre.reverse).reverse ++ suffix) values [] gateCount 0 0) := by
    simpa using hrestore
  have hdone :
      transition^[1]
        (some (cfg (some (.certificateRestore bit)) afterRestore input output
          ((bit :: pre.reverse).reverse ++ suffix) values [] gateCount 0 0)) =
        some (cfg (some .gates) { afterRestore with counterPresent := false }
          input output ((bit :: pre.reverse).reverse ++ suffix)
          (bit :: values) [] (gateCount + 1) 0 0) := by
    change step (cfg (some (.certificateRestore bit)) afterRestore input output
      ((bit :: pre.reverse).reverse ++ suffix) values [] gateCount 0 0) = _
    exact certificate_restore_done_step afterRestore bit input output
      ((bit :: pre.reverse).reverse ++ suffix) values [] gateCount 0
  have h₁₂ := step_comp pre.length 1 hprefix' htarget
  have h₁₂₃ := step_comp (1 + pre.length) (pre.length + 1) h₁₂ hrestore'
  have hfull := step_comp ((pre.length + 1) + (1 + pre.length)) 1 h₁₂₃ hdone
  refine ⟨{ afterRestore with counterPresent := false }, ?_⟩
  have hsteps : 2 * pre.length + 3 =
      1 + ((pre.length + 1) + (1 + pre.length)) := by omega
  rw [hsteps]
  convert hfull using 1 <;> simp [List.reverse_cons, List.append_assoc]

/-! ## Previously computed gate-value lookup -/

/-- Subtract the source index from the gate count while saving it for the
final restoration. -/
theorem gate_subtract_phase (state : State) (ret : Return) (source remaining : Nat)
    (input : List (Option CircuitSym)) (output certificate values scratch : List Bool)
    (saved : Nat) :
    ∃ finalState,
      transition^[source]
        (some (cfg (some (.gateSubtract ret)) state input output certificate values
          scratch (remaining + source) source saved)) =
        some (cfg (some (.gateSubtract ret)) finalState input output certificate values
          scratch remaining 0 (saved + source)) := by
  induction source generalizing state saved with
  | zero => exact ⟨state, by simp⟩
  | succ source ih =>
      let nextState : State := { state with counterPresent := true }
      rcases ih nextState (saved + 1) with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := gate_subtract_step state ret input output certificate values scratch
        (remaining + source) source saved
      have hcomposed := step_then source hfirst hrun
      simpa [nextState, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hcomposed

/-- Continue transferring a nonempty block of gate values; the final moved
value is the selected predecessor. -/
theorem gate_transfer_continue_phase (state : State) (ret : Return)
    (candidate : Bool) (front : List Bool) (target : Bool) (tail scratch : List Bool)
    (input : List (Option CircuitSym)) (output certificate : List Bool)
    (index saved : Nat) :
    ∃ finalState,
      transition^[front.length + 2]
        (some (cfg (some (.gateTransfer ret candidate)) state input output certificate
          (front ++ target :: tail) scratch (front.length + 1) index saved)) =
        some (cfg (some (.gateRestore ret target)) finalState input output certificate tail
          ((front ++ [target]).reverse ++ scratch) 0
          (index + front.length + 1) saved) := by
  induction front generalizing state candidate scratch index with
  | nil =>
      let afterMove : State :=
        { state with boolBuffer := some target, counterPresent := true }
      have hmove := gate_transfer_step state ret candidate target input output certificate
        tail scratch 0 index saved
      have hdone := gate_transfer_done_step afterMove ret target input output certificate
        tail (target :: scratch) (index + 1) saved
      refine ⟨{ afterMove with counterPresent := false }, ?_⟩
      have hfull := step_then 1 hmove (by
        change step (cfg (some (.gateTransfer ret target)) afterMove input output
          certificate tail (target :: scratch) 0 (index + 1) saved) = _
        exact hdone)
      simpa [afterMove, Nat.add_assoc] using hfull
  | cons bit rest ih =>
      let nextState : State :=
        { state with boolBuffer := some bit, counterPresent := true }
      rcases ih nextState bit (bit :: scratch) (index + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := gate_transfer_step state ret candidate bit input output certificate
        (rest ++ target :: tail) scratch (rest.length + 1) index saved
      have hcomposed := step_then (rest.length + 2) hfirst hrun
      simpa [nextState, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hcomposed

/-- Transfer the requested nonempty newest-first block, starting from the
dedicated first-transfer label. -/
theorem gate_transfer_first_phase (state : State) (ret : Return)
    (front : List Bool) (target : Bool) (tail : List Bool)
    (input : List (Option CircuitSym)) (output certificate : List Bool)
    (saved : Nat) :
    ∃ finalState,
      transition^[front.length + 2]
        (some (cfg (some (.gateTransferFirst ret)) state input output certificate
          (front ++ target :: tail) [] (front.length + 1) 0 saved)) =
        some (cfg (some (.gateRestore ret target)) finalState input output certificate tail
          (front ++ [target]).reverse 0 (front.length + 1) saved) := by
  cases front with
  | nil =>
      let afterMove : State :=
        { state with boolBuffer := some target, counterPresent := true }
      have hmove := gate_transfer_first_step state ret target input output certificate
        tail [] 0 0 saved
      have hdone := gate_transfer_done_step afterMove ret target input output certificate
        tail [target] 1 saved
      refine ⟨{ afterMove with counterPresent := false }, ?_⟩
      have hfull := step_then 1 hmove (by
        change step (cfg (some (.gateTransfer ret target)) afterMove input output
          certificate tail [target] 0 1 saved) = _
        exact hdone)
      simpa [afterMove] using hfull
  | cons bit rest =>
      let afterMove : State :=
        { state with boolBuffer := some bit, counterPresent := true }
      have hfirst := gate_transfer_first_step state ret bit input output certificate
        (rest ++ target :: tail) [] (rest.length + 1) 0 saved
      rcases gate_transfer_continue_phase afterMove ret bit rest target tail [bit]
          input output certificate 1 saved with ⟨finalState, hrest⟩
      refine ⟨finalState, ?_⟩
      have hfull := step_then (rest.length + 2) hfirst hrest
      simpa [afterMove, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfull

/-- Restore a moved gate-value block and its gate-count contribution. -/
theorem gate_restore_values_phase (state : State) (ret : Return) (value : Bool)
    (moved values : List Bool) (input : List (Option CircuitSym))
    (output certificate : List Bool) (gateCount saved : Nat) :
    ∃ finalState,
      transition^[moved.length]
        (some (cfg (some (.gateRestore ret value)) state input output certificate values
          moved gateCount moved.length saved)) =
        some (cfg (some (.gateRestore ret value)) finalState input output certificate
          (moved.reverse ++ values) [] (gateCount + moved.length) 0 saved) := by
  induction moved generalizing state values gateCount with
  | nil => exact ⟨state, by simp⟩
  | cons bit rest ih =>
      let nextState : State :=
        { state with boolBuffer := some bit, counterPresent := true }
      rcases ih nextState (bit :: values) (gateCount + 1) with
        ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := gate_restore_step state ret value bit input output certificate values
        rest gateCount rest.length saved
      have hfull := step_then rest.length hfirst hrun
      simpa [nextState, List.reverse_cons, List.append_assoc, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hfull

/-- Restore the source index into the gate-count counter. -/
theorem gate_restore_saved_phase (state : State) (ret : Return) (value : Bool)
    (source gateCount : Nat) (input : List (Option CircuitSym))
    (output certificate values scratch : List Bool) :
    ∃ finalState,
      transition^[source]
        (some (cfg (some (.gateRestoreSaved ret value)) state input output certificate
          values scratch gateCount 0 source)) =
        some (cfg (some (.gateRestoreSaved ret value)) finalState input output certificate
          values scratch (gateCount + source) 0 0) := by
  induction source generalizing state gateCount with
  | zero => exact ⟨state, by simp⟩
  | succ source ih =>
      let nextState : State := { state with counterPresent := true }
      rcases ih nextState (gateCount + 1) with ⟨finalState, hrun⟩
      refine ⟨finalState, ?_⟩
      have hfirst := gate_restore_saved_step state ret value input output certificate
        values scratch gateCount 0 source
      have hfull := step_then source hfirst hrun
      simpa [nextState, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

/-- Core predecessor lookup: all stacks and counters are restored, with the
selected value retained only in the finite return label. -/
theorem gate_lookup_core_phase (state : State) (ret : Return)
    (front older : List Bool) (target : Bool)
    (input : List (Option CircuitSym)) (output certificate : List Bool) :
    ∃ finalState,
      transition^[2 * older.length + 2 * front.length + 5]
        (some (cfg (some (.gateSubtract ret)) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some (.gateRestoreSaved ret target)) finalState input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) 0 0) := by
  rcases gate_subtract_phase state ret older.length (front.length + 1)
      input output certificate (front ++ target :: older) [] 0 with
    ⟨afterSubtract, hsubtract⟩
  have hsubtract' :
      transition^[older.length]
        (some (cfg (some (.gateSubtract ret)) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some (.gateSubtract ret)) afterSubtract input output certificate
          (front ++ target :: older) [] (front.length + 1) 0 older.length) := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsubtract
  let afterSubtractDone : State := { afterSubtract with counterPresent := false }
  have hsubtractDone :
      transition^[1]
        (some (cfg (some (.gateSubtract ret)) afterSubtract input output certificate
          (front ++ target :: older) [] (front.length + 1) 0 older.length)) =
        some (cfg (some (.gateTransferFirst ret)) afterSubtractDone input output certificate
          (front ++ target :: older) [] (front.length + 1) 0 older.length) := by
    change step (cfg (some (.gateSubtract ret)) afterSubtract input output certificate
      (front ++ target :: older) [] (front.length + 1) 0 older.length) = _
    exact gate_subtract_done_step afterSubtract ret input output certificate
      (front ++ target :: older) [] (front.length + 1) older.length
  rcases gate_transfer_first_phase afterSubtractDone ret front target older input output
      certificate older.length with ⟨afterTransfer, htransfer⟩
  rcases gate_restore_values_phase afterTransfer ret target
      (front ++ [target]).reverse older input output certificate 0 older.length with
    ⟨afterValues, hvalues⟩
  have hvalues' :
      transition^[front.length + 1]
        (some (cfg (some (.gateRestore ret target)) afterTransfer input output certificate
          older (front ++ [target]).reverse 0 (front.length + 1) older.length)) =
        some (cfg (some (.gateRestore ret target)) afterValues input output certificate
          (front ++ target :: older) [] (front.length + 1) 0 older.length) := by
    simpa [List.append_assoc] using hvalues
  let afterValuesDone : State := { afterValues with counterPresent := false }
  have hvaluesDone :
      transition^[1]
        (some (cfg (some (.gateRestore ret target)) afterValues input output certificate
          (front ++ target :: older) [] (front.length + 1) 0 older.length)) =
        some (cfg (some (.gateRestoreSaved ret target)) afterValuesDone input output certificate
          (front ++ target :: older) [] (front.length + 1) 0 older.length) := by
    change step (cfg (some (.gateRestore ret target)) afterValues input output certificate
      (front ++ target :: older) [] (front.length + 1) 0 older.length) = _
    exact gate_restore_done_step afterValues ret target input output certificate
      (front ++ target :: older) [] (front.length + 1) older.length
  rcases gate_restore_saved_phase afterValuesDone ret target older.length
      (front.length + 1) input output certificate (front ++ target :: older) [] with
    ⟨finalState, hsaved⟩
  have h₁ := step_comp older.length 1 hsubtract' hsubtractDone
  have h₂ := step_comp (1 + older.length) (front.length + 2) h₁ htransfer
  have h₃ := step_comp ((front.length + 2) + (1 + older.length))
    (front.length + 1) h₂ hvalues'
  have h₄ := step_comp ((front.length + 1) +
    ((front.length + 2) + (1 + older.length))) 1 h₃ hvaluesDone
  have hfull := step_comp (1 + ((front.length + 1) +
    ((front.length + 2) + (1 + older.length)))) older.length h₄ hsaved
  refine ⟨finalState, ?_⟩
  have hsteps : 2 * older.length + 2 * front.length + 5 =
      older.length + (1 + ((front.length + 1) +
        ((front.length + 2) + (1 + older.length)))) := by omega
  rw [hsteps]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfull

private def lookupSteps (front older : List Bool) : Nat :=
  2 * older.length + 2 * front.length + 6

private theorem lookupSteps_eq (front older : List Bool) :
    lookupSteps front older = 1 + (2 * older.length + 2 * front.length + 5) := by
  simp [lookupSteps]
  omega

theorem gate_lookup_not_phase (state : State) (front older : List Bool)
    (target : Bool) (input : List (Option CircuitSym))
    (output certificate : List Bool) :
    ∃ finalState,
      transition^[lookupSteps front older]
        (some (cfg (some (.gateSubtract .notGate)) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some .gates) finalState input output certificate
          ((!target) :: (front ++ target :: older)) []
          (front.length + older.length + 2) 0 0) := by
  rcases gate_lookup_core_phase state .notGate front older target input output certificate with
    ⟨afterCore, hcore⟩
  have hdone : transition^[1]
      (some (cfg (some (.gateRestoreSaved .notGate target)) afterCore input output
        certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0)) =
      some (cfg (some .gates) { afterCore with counterPresent := false }
        input output certificate ((!target) :: (front ++ target :: older)) []
        (front.length + older.length + 2) 0 0) := by
    change step (cfg (some (.gateRestoreSaved .notGate target)) afterCore input output
      certificate (front ++ target :: older) []
      (front.length + older.length + 1) 0 0) = _
    exact gate_restore_saved_not_done_step afterCore target input output certificate
      (front ++ target :: older) [] (front.length + older.length + 1) 0
  refine ⟨{ afterCore with counterPresent := false }, ?_⟩
  have hfull := step_comp (2 * older.length + 2 * front.length + 5) 1 hcore hdone
  rw [lookupSteps_eq]
  exact hfull

theorem gate_lookup_and_left_phase (state : State) (front older : List Bool)
    (target : Bool) (input : List (Option CircuitSym))
    (output certificate : List Bool) :
    ∃ finalState,
      transition^[lookupSteps front older]
        (some (cfg (some (.gateSubtract .andLeft)) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some (.parseNat (.andRight target))) finalState input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) 0 0) := by
  rcases gate_lookup_core_phase state .andLeft front older target input output certificate with
    ⟨afterCore, hcore⟩
  have hdone : transition^[1]
      (some (cfg (some (.gateRestoreSaved .andLeft target)) afterCore input output
        certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0)) =
      some (cfg (some (.parseNat (.andRight target)))
        { afterCore with counterPresent := false } input output certificate
        (front ++ target :: older) []
        (front.length + older.length + 1) 0 0) := by
    change step (cfg (some (.gateRestoreSaved .andLeft target)) afterCore input output
      certificate (front ++ target :: older) []
      (front.length + older.length + 1) 0 0) = _
    exact gate_restore_saved_and_left_done_step afterCore target input output certificate
      (front ++ target :: older) [] (front.length + older.length + 1) 0
  refine ⟨{ afterCore with counterPresent := false }, ?_⟩
  have hfull := step_comp (2 * older.length + 2 * front.length + 5) 1 hcore hdone
  rw [lookupSteps_eq]
  exact hfull

theorem gate_lookup_and_right_phase (state : State) (left : Bool)
    (front older : List Bool) (target : Bool)
    (input : List (Option CircuitSym)) (output certificate : List Bool) :
    ∃ finalState,
      transition^[lookupSteps front older]
        (some (cfg (some (.gateSubtract (.andRight left))) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some .gates) finalState input output certificate
          ((left && target) :: (front ++ target :: older)) []
          (front.length + older.length + 2) 0 0) := by
  rcases gate_lookup_core_phase state (.andRight left) front older target input output certificate with
    ⟨afterCore, hcore⟩
  have hdone : transition^[1]
      (some (cfg (some (.gateRestoreSaved (.andRight left) target)) afterCore input output
        certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0)) =
      some (cfg (some .gates) { afterCore with counterPresent := false }
        input output certificate ((left && target) :: (front ++ target :: older)) []
        (front.length + older.length + 2) 0 0) := by
    change step (cfg (some (.gateRestoreSaved (.andRight left) target)) afterCore input output
      certificate (front ++ target :: older) []
      (front.length + older.length + 1) 0 0) = _
    exact gate_restore_saved_and_right_done_step afterCore left target input output certificate
      (front ++ target :: older) [] (front.length + older.length + 1) 0
  refine ⟨{ afterCore with counterPresent := false }, ?_⟩
  have hfull := step_comp (2 * older.length + 2 * front.length + 5) 1 hcore hdone
  rw [lookupSteps_eq]
  exact hfull

theorem gate_lookup_or_left_phase (state : State) (front older : List Bool)
    (target : Bool) (input : List (Option CircuitSym))
    (output certificate : List Bool) :
    ∃ finalState,
      transition^[lookupSteps front older]
        (some (cfg (some (.gateSubtract .orLeft)) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some (.parseNat (.orRight target))) finalState input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) 0 0) := by
  rcases gate_lookup_core_phase state .orLeft front older target input output certificate with
    ⟨afterCore, hcore⟩
  have hdone : transition^[1]
      (some (cfg (some (.gateRestoreSaved .orLeft target)) afterCore input output
        certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0)) =
      some (cfg (some (.parseNat (.orRight target)))
        { afterCore with counterPresent := false } input output certificate
        (front ++ target :: older) []
        (front.length + older.length + 1) 0 0) := by
    change step (cfg (some (.gateRestoreSaved .orLeft target)) afterCore input output
      certificate (front ++ target :: older) []
      (front.length + older.length + 1) 0 0) = _
    exact gate_restore_saved_or_left_done_step afterCore target input output certificate
      (front ++ target :: older) [] (front.length + older.length + 1) 0
  refine ⟨{ afterCore with counterPresent := false }, ?_⟩
  have hfull := step_comp (2 * older.length + 2 * front.length + 5) 1 hcore hdone
  rw [lookupSteps_eq]
  exact hfull

theorem gate_lookup_or_right_phase (state : State) (left : Bool)
    (front older : List Bool) (target : Bool)
    (input : List (Option CircuitSym)) (output certificate : List Bool) :
    ∃ finalState,
      transition^[lookupSteps front older]
        (some (cfg (some (.gateSubtract (.orRight left))) state input output certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some .gates) finalState input output certificate
          ((left || target) :: (front ++ target :: older)) []
          (front.length + older.length + 2) 0 0) := by
  rcases gate_lookup_core_phase state (.orRight left) front older target input output certificate with
    ⟨afterCore, hcore⟩
  have hdone : transition^[1]
      (some (cfg (some (.gateRestoreSaved (.orRight left) target)) afterCore input output
        certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0)) =
      some (cfg (some .gates) { afterCore with counterPresent := false }
        input output certificate ((left || target) :: (front ++ target :: older)) []
        (front.length + older.length + 2) 0 0) := by
    change step (cfg (some (.gateRestoreSaved (.orRight left) target)) afterCore input output
      certificate (front ++ target :: older) []
      (front.length + older.length + 1) 0 0) = _
    exact gate_restore_saved_or_right_done_step afterCore left target input output certificate
      (front ++ target :: older) [] (front.length + older.length + 1) 0
  refine ⟨{ afterCore with counterPresent := false }, ?_⟩
  have hfull := step_comp (2 * older.length + 2 * front.length + 5) 1 hcore hdone
  rw [lookupSteps_eq]
  exact hfull

theorem gate_lookup_output_phase (state : State) (front older : List Bool)
    (target : Bool) (certificate : List Bool) :
    ∃ finalState,
      transition^[lookupSteps front older]
        (some (cfg (some (.gateSubtract .outputGate)) state [] [] certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) older.length 0)) =
        some (cfg (some (.clearInput target)) finalState [] [] certificate
          (front ++ target :: older) []
          (front.length + older.length + 1) 0 0) := by
  rcases gate_lookup_core_phase state .outputGate front older target [] [] certificate with
    ⟨afterCore, hcore⟩
  have hdone : transition^[1]
      (some (cfg (some (.gateRestoreSaved .outputGate target)) afterCore [] []
        certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0)) =
      some (cfg (some (.clearInput target)) { afterCore with counterPresent := false }
        [] [] certificate (front ++ target :: older) []
        (front.length + older.length + 1) 0 0) := by
    change step (cfg (some (.gateRestoreSaved .outputGate target)) afterCore [] []
      certificate (front ++ target :: older) []
      (front.length + older.length + 1) 0 0) = _
    exact gate_restore_saved_output_done_step afterCore target certificate
      (front ++ target :: older) [] (front.length + older.length + 1) 0
  refine ⟨{ afterCore with counterPresent := false }, ?_⟩
  have hfull := step_comp (2 * older.length + 2 * front.length + 5) 1 hcore hdone
  rw [lookupSteps_eq]
  exact hfull

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
