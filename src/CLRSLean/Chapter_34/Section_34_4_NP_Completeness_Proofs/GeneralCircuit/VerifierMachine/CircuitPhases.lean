import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.VerifierMachine.Cleanup

/-!
# Concrete verifier: well-formed circuit evaluation phases

This file connects the restoring stack lookups to `CircuitGate.evalWith`.
Unlike executable fuel tests, the phase theorems below quantify over every
well-formed gate and retain exact transition counts.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitVerifier

open Computability StateTransition

private abbrev transition := flip Option.bind step

/-- Array and list defaulted lookup agree through `Array.toList`. -/
theorem array_toList_getD (values : Array Bool) (i : Nat) :
    values.toList.getD i false = values.getD i false := by
  by_cases hi : i < values.size
  · simp [List.getD, Array.getD, hi, Array.getElem_toList]
  · simp [List.getD, Array.getD, hi]

/-- Split a list at an in-bounds defaulted lookup. -/
theorem split_getD (bits : List Bool) (i : Nat) (hi : i < bits.length) :
    ∃ suffix, bits = bits.take i ++ bits.getD i false :: suffix ∧
      (bits.take i).length = i := by
  refine ⟨bits.drop (i + 1), ?_, List.length_take_of_le (Nat.le_of_lt hi)⟩
  rw [← List.take_append_drop i bits, List.drop_eq_getElem_cons hi]
  simp [List.getD, hi]

/-- A chronological value list, reversed for the stack, can be split so that
the requested chronological index has exactly `i` older values below it. -/
theorem reverse_split_getD (values : List Bool) (i : Nat)
    (hi : i < values.length) :
    ∃ front older,
      values.reverse = front ++ values.getD i false :: older ∧
      front.length + older.length + 1 = values.length ∧
      older.length = i := by
  let pos := values.length - 1 - i
  have hpos : pos < values.reverse.length := by
    simp only [List.length_reverse]
    omega
  have hvalue : values.reverse[pos] = values.getD i false := by
    calc
      values.reverse[pos] = values[values.length - 1 - pos] := by
        simpa using List.getElem_reverse hpos
      _ = values[i] := by congr 1 <;> omega
      _ = values.getD i false := (List.getD_eq_getElem values false hi).symm
  refine ⟨values.reverse.take pos, values.reverse.drop (pos + 1), ?_, ?_, ?_⟩
  · calc
      values.reverse = values.reverse.take pos ++ values.reverse.drop pos :=
        (List.take_append_drop pos values.reverse).symm
      _ = values.reverse.take pos ++
          values.reverse[pos] :: values.reverse.drop (pos + 1) := by
        rw [List.drop_eq_getElem_cons hpos]
      _ = values.reverse.take pos ++
          values.getD i false :: values.reverse.drop (pos + 1) := by
        rw [hvalue]
  · simp only [List.length_take, List.length_reverse, List.length_drop]
    omega
  · simp only [List.length_drop, List.length_reverse, pos]
    omega

/-- Exact successful cost of one well-formed encoded gate. -/
def gateSteps (gateCount : Nat) : CircuitGate → Nat
  | .input i => 1 + (i + 1) + (2 * i + 3)
  | .const _ => 1
  | .not source => 1 + (source + 1) + (2 * gateCount + 4)
  | .and left right | .or left right =>
      1 + (left + 1) + (2 * gateCount + 4) +
        (right + 1) + (2 * gateCount + 4)

/-- The machine executes one well-formed gate exactly according to
`CircuitGate.evalWith`, preserving the certificate and all earlier values. -/
theorem gate_phase (state : State) (gate : CircuitGate)
    (inputBits : List Bool) (values : Array Bool)
    (rest : List (Option CircuitSym))
    (hvalid : gate.ValidAt inputBits.length values.size) :
    ∃ finalState,
      transition^[gateSteps values.size gate]
        (some (cfg (some .gates) state
          (List.map some (encodeCircuitGate gate) ++ rest)
          [] inputBits values.toList.reverse [] values.size 0 0)) =
        some (cfg (some .gates) finalState rest [] inputBits
          (values.push (gate.evalWith (fun i => inputBits.getD i false) values)).toList.reverse
          [] (values.size + 1) 0 0) := by
  cases gate with
  | input i =>
      rcases split_getD inputBits i hvalid with ⟨suffix, hbits, hpre⟩
      have htag : transition^[1]
          (some (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.input i)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.parseNat .inputGate))
            { state with inputBuffer := some (some .inputMark) }
            (List.map some (encNat i) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0) := by
        change step (cfg (some .gates) state
          (List.map some (encodeCircuitGate (.input i)) ++ rest)
          [] inputBits values.toList.reverse [] values.size 0 0) = _
        simpa [encodeCircuitGate] using
          gates_input_step state (List.map some (encNat i) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .inputMark) }
          .inputGate i 0 rest [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterParse, hparse⟩
      have hparse' : transition^[i + 1]
          (some (cfg (some (.parseNat .inputGate))
            { state with inputBuffer := some (some .inputMark) }
            (List.map some (encNat i) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some .certificateLookup) afterParse rest [] inputBits
            values.toList.reverse [] values.size i 0) := by
        simpa [parsedLabel] using hparse
      rcases certificate_lookup_phase afterParse (inputBits.take i) suffix
          (inputBits.getD i false) rest [] values.toList.reverse values.size with
        ⟨afterLookup, hlookup⟩
      have hlookup' : transition^[2 * i + 3]
          (some (cfg (some .certificateLookup) afterParse rest [] inputBits
            values.toList.reverse [] values.size i 0)) =
          some (cfg (some .gates) afterLookup rest [] inputBits
            (inputBits.getD i false :: values.toList.reverse) []
            (values.size + 1) 0 0) := by
        rw [hpre, ← hbits] at hlookup
        exact hlookup
      have h₁₂ := step_comp 1 (i + 1) htag hparse'
      have hfull := step_comp ((i + 1) + 1) (2 * i + 3) h₁₂ hlookup'
      refine ⟨afterLookup, ?_⟩
      have hsteps : gateSteps values.size (.input i) =
          (2 * i + 3) + ((i + 1) + 1) := by
        simp only [gateSteps]
        omega
      rw [hsteps]
      simpa only [CircuitGate.evalWith, Array.toList_push, List.reverse_append,
        List.reverse_singleton, List.singleton_append] using hfull
  | const value =>
      refine ⟨{ state with inputBuffer := some (some
        (if value then .constTrueMark else .constFalseMark)) }, ?_⟩
      change step (cfg (some .gates) state
        (List.map some (encodeCircuitGate (.const value)) ++ rest)
        [] inputBits values.toList.reverse [] values.size 0 0) = _
      cases value with
      | false =>
          simpa [gateSteps, encodeCircuitGate, CircuitGate.evalWith,
            Array.toList_push, List.reverse_append] using
            gates_const_step state false rest [] inputBits values.toList.reverse []
              values.size 0 0
      | true =>
          simpa [gateSteps, encodeCircuitGate, CircuitGate.evalWith,
            Array.toList_push, List.reverse_append] using
            gates_const_step state true rest [] inputBits values.toList.reverse []
              values.size 0 0
  | not source =>
      rcases reverse_split_getD values.toList source hvalid with
        ⟨front, older, hsplit, hlength, holder⟩
      have hcount : front.length + older.length + 1 = values.size := by
        simpa using hlength
      have htag : transition^[1]
          (some (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.not source)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.parseNat .notGate))
            { state with inputBuffer := some (some .notMark) }
            (List.map some (encNat source) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0) := by
        change step (cfg (some .gates) state
          (List.map some (encodeCircuitGate (.not source)) ++ rest)
          [] inputBits values.toList.reverse [] values.size 0 0) = _
        simpa [encodeCircuitGate] using
          gates_not_step state (List.map some (encNat source) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .notMark) }
          .notGate source 0 rest [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterParse, hparse⟩
      have hparse' : transition^[source + 1]
          (some (cfg (some (.parseNat .notGate))
            { state with inputBuffer := some (some .notMark) }
            (List.map some (encNat source) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.gateSubtract .notGate)) afterParse rest [] inputBits
            values.toList.reverse [] values.size source 0) := by
        simpa [parsedLabel] using hparse
      rcases gate_lookup_not_phase afterParse front older
          (values.toList.getD source false) rest [] inputBits with
        ⟨afterLookup, hlookup⟩
      change transition^[2 * older.length + 2 * front.length + 6] _ = _ at hlookup
      have hlookup' : transition^[2 * values.size + 4]
          (some (cfg (some (.gateSubtract .notGate)) afterParse rest [] inputBits
            values.toList.reverse [] values.size source 0)) =
          some (cfg (some .gates) afterLookup rest [] inputBits
            ((!values.toList.getD source false) :: values.toList.reverse) []
            (values.size + 1) 0 0) := by
        have hcost : 2 * values.size + 4 =
            2 * older.length + 2 * front.length + 6 := by omega
        rw [hcost, hsplit, ← hcount]
        simpa only [holder] using hlookup
      have h₁₂ := step_comp 1 (source + 1) htag hparse'
      have hfull := step_comp ((source + 1) + 1) (2 * values.size + 4) h₁₂ hlookup'
      refine ⟨afterLookup, ?_⟩
      have hsteps : gateSteps values.size (.not source) =
          (2 * values.size + 4) + ((source + 1) + 1) := by
        simp only [gateSteps]
        omega
      rw [hsteps]
      simpa only [CircuitGate.evalWith, array_toList_getD,
        Array.toList_push, List.reverse_append, List.reverse_singleton,
        List.singleton_append] using hfull
  | and left right =>
      rcases reverse_split_getD values.toList left hvalid.1 with
        ⟨leftFront, leftOlder, hleftSplit, hleftLength, hleftOlder⟩
      rcases reverse_split_getD values.toList right hvalid.2 with
        ⟨rightFront, rightOlder, hrightSplit, hrightLength, hrightOlder⟩
      have hleftCount : leftFront.length + leftOlder.length + 1 = values.size := by
        simpa using hleftLength
      have hrightCount : rightFront.length + rightOlder.length + 1 = values.size := by
        simpa using hrightLength
      let rightInput := List.map some (encNat right) ++ rest
      have htag : transition^[1]
          (some (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.and left right)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.parseNat .andLeft))
            { state with inputBuffer := some (some .andMark) }
            (List.map some (encNat left) ++ rightInput)
            [] inputBits values.toList.reverse [] values.size 0 0) := by
        change step (cfg (some .gates) state
          (List.map some (encodeCircuitGate (.and left right)) ++ rest)
          [] inputBits values.toList.reverse [] values.size 0 0) = _
        simpa [encodeCircuitGate, rightInput, List.map_append, List.append_assoc] using
          gates_and_step state (List.map some (encNat left) ++ rightInput)
            [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .andMark) }
          .andLeft left 0 rightInput [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterLeftParse, hleftParse⟩
      have hleftParse' : transition^[left + 1]
          (some (cfg (some (.parseNat .andLeft))
            { state with inputBuffer := some (some .andMark) }
            (List.map some (encNat left) ++ rightInput)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.gateSubtract .andLeft)) afterLeftParse rightInput
            [] inputBits values.toList.reverse [] values.size left 0) := by
        simpa [parsedLabel] using hleftParse
      rcases gate_lookup_and_left_phase afterLeftParse leftFront leftOlder
          (values.toList.getD left false) rightInput [] inputBits with
        ⟨afterLeftLookup, hleftLookup⟩
      change transition^[2 * leftOlder.length + 2 * leftFront.length + 6]
        _ = _ at hleftLookup
      have hleftLookup' : transition^[2 * values.size + 4]
          (some (cfg (some (.gateSubtract .andLeft)) afterLeftParse rightInput
            [] inputBits values.toList.reverse [] values.size left 0)) =
          some (cfg (some (.parseNat
              (.andRight (values.toList.getD left false))))
            afterLeftLookup rightInput [] inputBits values.toList.reverse []
            values.size 0 0) := by
        have hcost : 2 * values.size + 4 =
            2 * leftOlder.length + 2 * leftFront.length + 6 := by omega
        rw [hcost, hleftSplit, ← hleftCount]
        simpa only [hleftOlder] using hleftLookup
      rcases parse_nat_phase afterLeftLookup
          (.andRight (values.toList.getD left false)) right 0 rest [] inputBits
          values.toList.reverse [] values.size 0 with
        ⟨afterRightParse, hrightParse⟩
      have hrightParse' : transition^[right + 1]
          (some (cfg (some (.parseNat
              (.andRight (values.toList.getD left false))))
            afterLeftLookup rightInput [] inputBits values.toList.reverse []
            values.size 0 0)) =
          some (cfg (some (.gateSubtract
              (.andRight (values.toList.getD left false))))
            afterRightParse rest [] inputBits values.toList.reverse []
            values.size right 0) := by
        simpa [parsedLabel, rightInput] using hrightParse
      rcases gate_lookup_and_right_phase afterRightParse
          (values.toList.getD left false) rightFront rightOlder
          (values.toList.getD right false) rest [] inputBits with
        ⟨afterRightLookup, hrightLookup⟩
      change transition^[2 * rightOlder.length + 2 * rightFront.length + 6]
        _ = _ at hrightLookup
      have hrightLookup' : transition^[2 * values.size + 4]
          (some (cfg (some (.gateSubtract
              (.andRight (values.toList.getD left false))))
            afterRightParse rest [] inputBits values.toList.reverse []
            values.size right 0)) =
          some (cfg (some .gates) afterRightLookup rest [] inputBits
            ((values.toList.getD left false && values.toList.getD right false) ::
              values.toList.reverse) [] (values.size + 1) 0 0) := by
        have hcost : 2 * values.size + 4 =
            2 * rightOlder.length + 2 * rightFront.length + 6 := by omega
        rw [hcost, hrightSplit, ← hrightCount]
        simpa only [hrightOlder] using hrightLookup
      have h₁ := step_comp 1 (left + 1) htag hleftParse'
      have h₂ := step_comp ((left + 1) + 1) (2 * values.size + 4)
        h₁ hleftLookup'
      have h₃ := step_comp ((2 * values.size + 4) + ((left + 1) + 1))
        (right + 1) h₂ hrightParse'
      have hfull := step_comp
        ((right + 1) + ((2 * values.size + 4) + ((left + 1) + 1)))
        (2 * values.size + 4) h₃ hrightLookup'
      refine ⟨afterRightLookup, ?_⟩
      have hsteps : gateSteps values.size (.and left right) =
          (2 * values.size + 4) +
            ((right + 1) + ((2 * values.size + 4) + ((left + 1) + 1))) := by
        simp only [gateSteps]
        omega
      rw [hsteps]
      simpa only [CircuitGate.evalWith, array_toList_getD,
        Array.toList_push, List.reverse_append, List.reverse_singleton,
        List.singleton_append] using hfull
  | or left right =>
      rcases reverse_split_getD values.toList left hvalid.1 with
        ⟨leftFront, leftOlder, hleftSplit, hleftLength, hleftOlder⟩
      rcases reverse_split_getD values.toList right hvalid.2 with
        ⟨rightFront, rightOlder, hrightSplit, hrightLength, hrightOlder⟩
      have hleftCount : leftFront.length + leftOlder.length + 1 = values.size := by
        simpa using hleftLength
      have hrightCount : rightFront.length + rightOlder.length + 1 = values.size := by
        simpa using hrightLength
      let rightInput := List.map some (encNat right) ++ rest
      have htag : transition^[1]
          (some (cfg (some .gates) state
            (List.map some (encodeCircuitGate (.or left right)) ++ rest)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.parseNat .orLeft))
            { state with inputBuffer := some (some .orMark) }
            (List.map some (encNat left) ++ rightInput)
            [] inputBits values.toList.reverse [] values.size 0 0) := by
        change step (cfg (some .gates) state
          (List.map some (encodeCircuitGate (.or left right)) ++ rest)
          [] inputBits values.toList.reverse [] values.size 0 0) = _
        simpa [encodeCircuitGate, rightInput, List.map_append, List.append_assoc] using
          gates_or_step state (List.map some (encNat left) ++ rightInput)
            [] inputBits values.toList.reverse [] values.size 0 0
      rcases parse_nat_phase
          { state with inputBuffer := some (some .orMark) }
          .orLeft left 0 rightInput [] inputBits values.toList.reverse [] values.size 0 with
        ⟨afterLeftParse, hleftParse⟩
      have hleftParse' : transition^[left + 1]
          (some (cfg (some (.parseNat .orLeft))
            { state with inputBuffer := some (some .orMark) }
            (List.map some (encNat left) ++ rightInput)
            [] inputBits values.toList.reverse [] values.size 0 0)) =
          some (cfg (some (.gateSubtract .orLeft)) afterLeftParse rightInput
            [] inputBits values.toList.reverse [] values.size left 0) := by
        simpa [parsedLabel] using hleftParse
      rcases gate_lookup_or_left_phase afterLeftParse leftFront leftOlder
          (values.toList.getD left false) rightInput [] inputBits with
        ⟨afterLeftLookup, hleftLookup⟩
      change transition^[2 * leftOlder.length + 2 * leftFront.length + 6]
        _ = _ at hleftLookup
      have hleftLookup' : transition^[2 * values.size + 4]
          (some (cfg (some (.gateSubtract .orLeft)) afterLeftParse rightInput
            [] inputBits values.toList.reverse [] values.size left 0)) =
          some (cfg (some (.parseNat
              (.orRight (values.toList.getD left false))))
            afterLeftLookup rightInput [] inputBits values.toList.reverse []
            values.size 0 0) := by
        have hcost : 2 * values.size + 4 =
            2 * leftOlder.length + 2 * leftFront.length + 6 := by omega
        rw [hcost, hleftSplit, ← hleftCount]
        simpa only [hleftOlder] using hleftLookup
      rcases parse_nat_phase afterLeftLookup
          (.orRight (values.toList.getD left false)) right 0 rest [] inputBits
          values.toList.reverse [] values.size 0 with
        ⟨afterRightParse, hrightParse⟩
      have hrightParse' : transition^[right + 1]
          (some (cfg (some (.parseNat
              (.orRight (values.toList.getD left false))))
            afterLeftLookup rightInput [] inputBits values.toList.reverse []
            values.size 0 0)) =
          some (cfg (some (.gateSubtract
              (.orRight (values.toList.getD left false))))
            afterRightParse rest [] inputBits values.toList.reverse []
            values.size right 0) := by
        simpa [parsedLabel, rightInput] using hrightParse
      rcases gate_lookup_or_right_phase afterRightParse
          (values.toList.getD left false) rightFront rightOlder
          (values.toList.getD right false) rest [] inputBits with
        ⟨afterRightLookup, hrightLookup⟩
      change transition^[2 * rightOlder.length + 2 * rightFront.length + 6]
        _ = _ at hrightLookup
      have hrightLookup' : transition^[2 * values.size + 4]
          (some (cfg (some (.gateSubtract
              (.orRight (values.toList.getD left false))))
            afterRightParse rest [] inputBits values.toList.reverse []
            values.size right 0)) =
          some (cfg (some .gates) afterRightLookup rest [] inputBits
            ((values.toList.getD left false || values.toList.getD right false) ::
              values.toList.reverse) [] (values.size + 1) 0 0) := by
        have hcost : 2 * values.size + 4 =
            2 * rightOlder.length + 2 * rightFront.length + 6 := by omega
        rw [hcost, hrightSplit, ← hrightCount]
        simpa only [hrightOlder] using hrightLookup
      have h₁ := step_comp 1 (left + 1) htag hleftParse'
      have h₂ := step_comp ((left + 1) + 1) (2 * values.size + 4)
        h₁ hleftLookup'
      have h₃ := step_comp ((2 * values.size + 4) + ((left + 1) + 1))
        (right + 1) h₂ hrightParse'
      have hfull := step_comp
        ((right + 1) + ((2 * values.size + 4) + ((left + 1) + 1)))
        (2 * values.size + 4) h₃ hrightLookup'
      refine ⟨afterRightLookup, ?_⟩
      have hsteps : gateSteps values.size (.or left right) =
          (2 * values.size + 4) +
            ((right + 1) + ((2 * values.size + 4) + ((left + 1) + 1))) := by
        simp only [gateSteps]
        omega
      rw [hsteps]
      simpa only [CircuitGate.evalWith, array_toList_getD,
        Array.toList_push, List.reverse_append, List.reverse_singleton,
        List.singleton_append] using hfull

/-- Accumulator produced by evaluating an ordered gate segment. -/
def evalGateList (inputBits : List Bool) (initial : Array Bool)
    (gates : List CircuitGate) : Array Bool :=
  gates.foldl
    (fun values gate =>
      values.push (gate.evalWith (fun i => inputBits.getD i false) values))
    initial

@[simp] theorem evalGateList_size (inputBits : List Bool) (initial : Array Bool)
    (gates : List CircuitGate) :
    (evalGateList inputBits initial gates).size = initial.size + gates.length := by
  induction gates generalizing initial with
  | nil => simp [evalGateList]
  | cons gate gates ih =>
      simp only [evalGateList, List.foldl_cons]
      rw [show gates.foldl
          (fun values next =>
            values.push (next.evalWith (fun i => inputBits.getD i false) values))
          (initial.push (gate.evalWith (fun i => inputBits.getD i false) initial)) =
        evalGateList inputBits
          (initial.push (gate.evalWith (fun i => inputBits.getD i false) initial)) gates by
            rfl,
        ih, Array.size_push]
      simp
      omega

/-- Exact successful cost of an ordered gate segment. -/
def gateListSteps : Nat → List CircuitGate → Nat
  | _, [] => 0
  | gateCount, gate :: gates =>
      gateSteps gateCount gate + gateListSteps (gateCount + 1) gates

/-- Execute a gate segment whose references are valid relative to the supplied
initial accumulator. -/
theorem gate_list_phase (state : State) (gates : List CircuitGate)
    (inputBits : List Bool) (values : Array Bool)
    (rest : List (Option CircuitSym))
    (hvalid : ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputBits.length (values.size + i)) :
    ∃ finalState,
      transition^[gateListSteps values.size gates]
        (some (cfg (some .gates) state
          (List.map some (gates.flatMap encodeCircuitGate) ++ rest)
          [] inputBits values.toList.reverse [] values.size 0 0)) =
        some (cfg (some .gates) finalState rest [] inputBits
          (evalGateList inputBits values gates).toList.reverse []
          (values.size + gates.length) 0 0) := by
  induction gates generalizing state values with
  | nil =>
      exact ⟨state, by simp [gateListSteps, evalGateList]⟩
  | cons gate gates ih =>
      have hgate : gate.ValidAt inputBits.length values.size := by
        simpa using hvalid 0 (by simp)
      let nextValues :=
        values.push (gate.evalWith (fun i => inputBits.getD i false) values)
      have htail : ∀ i (hi : i < gates.length),
          (gates.get ⟨i, hi⟩).ValidAt inputBits.length (nextValues.size + i) := by
        intro i hi
        have hnext := hvalid (i + 1) (by simpa using hi)
        simpa [nextValues, Array.size_push, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hnext
      let tailInput := List.map some (gates.flatMap encodeCircuitGate) ++ rest
      rcases gate_phase state gate inputBits values tailInput hgate with
        ⟨afterGate, hgateRun⟩
      rcases ih afterGate nextValues htail with ⟨finalState, htailRun⟩
      have hfull := step_comp (gateSteps values.size gate)
        (gateListSteps nextValues.size gates) hgateRun (by
          simpa [tailInput, nextValues, Array.size_push] using htailRun)
      refine ⟨finalState, ?_⟩
      have hsteps : gateListSteps values.size (gate :: gates) =
          gateListSteps nextValues.size gates + gateSteps values.size gate := by
        simp [gateListSteps, nextValues, Array.size_push, Nat.add_comm]
      rw [hsteps]
      simpa [evalGateList, nextValues, tailInput, List.map_append,
        List.append_assoc, Array.size_push, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hfull

end CLRS.Chapter34.Turing.GeneralCircuitVerifier
