import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.GeneralCircuit.ToSAT.Machine.Normalizer.RejectBounds

/-!
# Guarded circuit normalizer: canonical rejection bounds

This file lifts the local one-gate estimates to a whole canonical gate family.
It deliberately stays separate from the raw-decoder bounds so that neither
proof has to be recompiled while the other is being developed.
-/

namespace CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer

open Computability StateTransition

/-- Uniform budget for reaching the first invalid gate in a canonical family. -/
def gateFamilyRejectBound (capacity baseStorage : Nat)
    (gates : List CircuitGate) : Nat :=
  (gates.length + 1) * streamUnitBound capacity baseStorage

/-- A canonical family containing an invalid gate rejects within a uniform
per-row budget.  The hypotheses expose the four monotone resources needed by
the induction: raw input, input arity, chronological index, and staged rows. -/
theorem gateFamily_rejectsIn_of_not_valid (state : State)
    (gates : List CircuitGate) (gateIndex inputCount : Nat)
    (hinvalid : ¬ ∀ i (hi : i < gates.length),
      (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + i))
    (input : List CircuitSym) (output rows : List NormalizedCircuitSym)
    (capacity baseStorage : Nat)
    (hcapacity : (gates.flatMap encodeCircuitGate ++ input).length ≤ capacity)
    (hinputCount : inputCount ≤ capacity)
    (hindex : gateIndex + gates.length ≤ capacity)
    (hstorage : output.length + rows.length ≤
      baseStorage + gateIndex * (2 * capacity + 3)) :
    RejectsIn
      (cfg (some .gates) state
        (gates.flatMap encodeCircuitGate ++ input) output rows
        inputCount gateIndex 0 0 0)
      (gateFamilyRejectBound capacity baseStorage gates) := by
  induction gates generalizing state gateIndex rows with
  | nil =>
      simp at hinvalid
  | cons gate gates ih =>
      have hgateCapacity : (encodeCircuitGate gate).length ≤ capacity := by
        have hle : (encodeCircuitGate gate).length ≤
            ((gate :: gates).flatMap encodeCircuitGate ++ input).length := by
          simp
        exact hle.trans hcapacity
      have htailCapacity :
          (gates.flatMap encodeCircuitGate ++ input).length ≤ capacity := by
        have hle : (gates.flatMap encodeCircuitGate ++ input).length ≤
            ((gate :: gates).flatMap encodeCircuitGate ++ input).length := by
          simp
        exact hle.trans hcapacity
      by_cases hgate : gate.ValidAt inputCount gateIndex
      · have htailInvalid : ¬ ∀ i (hi : i < gates.length),
            (gates.get ⟨i, hi⟩).ValidAt inputCount (gateIndex + 1 + i) := by
          intro htail
          apply hinvalid
          intro i hi
          cases i with
          | zero => simpa using hgate
          | succ i =>
              have hi' : i < gates.length := by simpa using hi
              have h := htail i hi'
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
        rcases gate_phase state gate gateIndex inputCount hgate
            (gates.flatMap encodeCircuitGate ++ input) output rows with
          ⟨afterGate, hrun⟩
        have hrow : (encodeNormalizedGateRow gateIndex gate).length ≤
            2 * capacity + 3 := by
          rw [encodeNormalizedGateRow_length]
          omega
        have hnextStorage : output.length +
            ((encodeNormalizedGateRow gateIndex gate).reverse ++ rows).length ≤
            baseStorage + (gateIndex + 1) * (2 * capacity + 3) := by
          rw [List.length_append, List.length_reverse,
            encodeNormalizedGateRow_length]
          nlinarith [hrow]
        have hnextIndex : gateIndex + 1 + gates.length ≤ capacity := by
          have hsimp : gateIndex + (gates.length + 1) ≤ capacity := by
            simpa using hindex
          omega
        have htail := ih (state := afterGate) (gateIndex := gateIndex + 1)
          (rows := (encodeNormalizedGateRow gateIndex gate).reverse ++ rows)
          htailInvalid htailCapacity hnextIndex hnextStorage
        have hfull := RejectsIn.before_steps
          (gateSteps gateIndex gate) hrun htail
        have hstep := gateSteps_le_streamUnit capacity baseStorage gateIndex gate
          hgateCapacity (by omega)
        have hfull' : RejectsIn
            (cfg (some .gates) state
              ((gate :: gates).flatMap encodeCircuitGate ++ input) output rows
              inputCount gateIndex 0 0 0)
            (gateFamilyRejectBound capacity baseStorage gates +
              gateSteps gateIndex gate) := by
          simpa [List.append_assoc] using hfull
        exact RejectsIn.mono hfull' (by
          simp only [gateFamilyRejectBound, List.length_cons]
          nlinarith)
      · have hlocal := invalidGate_rejectsIn state gate gateIndex inputCount
          capacity hgate (gates.flatMap encodeCircuitGate ++ input) output rows
          (by simpa [List.append_assoc] using hcapacity)
        have hremaining :
            (gates.flatMap encodeCircuitGate ++ input).length ≤ capacity :=
          htailCapacity
        have hunit := gateLocal_le_streamUnit capacity baseStorage
          (gates.flatMap encodeCircuitGate ++ input) output rows inputCount
          gateIndex hremaining hinputCount (by omega) hstorage
        have hlocal' : RejectsIn
            (cfg (some .gates) state
              ((gate :: gates).flatMap encodeCircuitGate ++ input) output rows
              inputCount gateIndex 0 0 0)
            (gateLocalRejectBound capacity
              (gates.flatMap encodeCircuitGate ++ input) output rows inputCount
              gateIndex) := by
          simpa [List.append_assoc] using hlocal
        exact RejectsIn.mono hlocal' (by
          calc
            gateLocalRejectBound capacity
                (gates.flatMap encodeCircuitGate ++ input) output rows inputCount
                gateIndex ≤ streamUnitBound capacity baseStorage := hunit
            _ ≤ gateFamilyRejectBound capacity baseStorage (gate :: gates) := by
              simp [gateFamilyRejectBound]
              exact Nat.le_mul_of_pos_left _ (by omega))

/-- Exact local budget for a canonical output index at least the gate count. -/
def invalidOutputRejectBound (gateCount extra inputCount : Nat)
    (output rows : List NormalizedCircuitSym) : Nat :=
  firstInvalidRejectBound .outputGate gateCount extra inputCount gateCount
      (gateCount + extra) [] output rows +
    (gateCount + extra + 1) + 1

/-- A canonical out-of-range output field rejects within its named local
budget. -/
theorem invalidOutputIndex_rejectsIn (state : State)
    (gateCount extra inputCount : Nat)
    (output rows : List NormalizedCircuitSym) :
    RejectsIn
      (cfg (some (.parseOperand .outputGate)) state
        (encNat (gateCount + extra)) output rows
        inputCount gateCount 0 0 0)
      (invalidOutputRejectBound gateCount extra inputCount output rows) := by
  rcases operand_phase state .outputGate (gateCount + extra) 0 [] output rows
      inputCount gateCount 0 0 with ⟨afterParse, hparse⟩
  have hparse' : (flip Option.bind step)^[gateCount + extra + 1]
      (some (cfg (some (.parseOperand .outputGate)) state
        (encNat (gateCount + extra)) output rows
        inputCount gateCount 0 0 0)) =
      some (cfg (some .checkTrailing) afterParse [] output rows inputCount
        gateCount (gateCount + extra) 0 (gateCount + extra)) := by
    simpa [afterOperandLabel, operandRows, operandOutputIndex] using hparse
  have htrailing : step
      (cfg (some .checkTrailing) afterParse [] output rows inputCount gateCount
        (gateCount + extra) 0 (gateCount + extra)) =
      some (cfg (some (.compareOperand .outputGate))
        { afterParse with inputBuffer := none } [] output rows inputCount
        gateCount (gateCount + extra) 0 (gateCount + extra)) := by
    exact check_trailing_empty_step afterParse output rows inputCount gateCount
      (gateCount + extra) 0 (gateCount + extra)
  have hreject := firstInvalidGate_rejectsIn
    { afterParse with inputBuffer := none } .outputGate gateCount extra
    inputCount gateCount (gateCount + extra) [] output rows
  have hchecked := RejectsIn.before_step htrailing hreject
  have hfull := RejectsIn.before_steps (gateCount + extra + 1) hparse' hchecked
  simpa [invalidOutputRejectBound, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hfull

/-- The local output-rejection budget fits the same unit used for a gate row. -/
theorem invalidOutputRejectBound_le_streamUnit
    (capacity baseStorage gateCount extra inputCount : Nat)
    (output rows : List NormalizedCircuitSym)
    (hfield : gateCount + extra + 2 ≤ capacity)
    (hinputCount : inputCount ≤ capacity)
    (hgateCount : gateCount ≤ capacity)
    (hstorage : output.length + rows.length ≤
      baseStorage + gateCount * (2 * capacity + 3)) :
    invalidOutputRejectBound gateCount extra inputCount output rows ≤
      streamUnitBound capacity baseStorage := by
  have hlinear : invalidOutputRejectBound gateCount extra inputCount output rows ≤
      64 * (capacity + ([] : List CircuitSym).length + output.length +
        rows.length + inputCount + gateCount + 1) := by
    simp [invalidOutputRejectBound, firstInvalidRejectBound,
      clearAndEmitInvalidSteps, withBound]
    omega
  have hlocal := linear_le_gateLocal capacity [] output rows inputCount
    gateCount _ hlinear
  exact hlocal.trans (gateLocal_le_streamUnit capacity baseStorage [] output rows
    inputCount gateCount (by simp) hinputCount hgateCount hstorage)

/-- Indexed normalized rows occupy at most one linear-capacity block per gate. -/
theorem normalizedRows_length_le_capacity (gateIndex : Nat)
    (gates : List CircuitGate) (capacity : Nat)
    (hindex : gateIndex + gates.length ≤ capacity)
    (hraw : (gates.flatMap encodeCircuitGate).length ≤ capacity) :
    (encodeNormalizedGateRowsFrom gateIndex gates).length ≤
      gates.length * (2 * capacity + 3) := by
  induction gates generalizing gateIndex with
  | nil => simp [encodeNormalizedGateRowsFrom]
  | cons gate gates ih =>
      have hgate : (encodeCircuitGate gate).length ≤ capacity := by
        have hle : (encodeCircuitGate gate).length ≤
            ((gate :: gates).flatMap encodeCircuitGate).length := by simp
        exact hle.trans hraw
      have htailRaw : (gates.flatMap encodeCircuitGate).length ≤ capacity := by
        have hle : (gates.flatMap encodeCircuitGate).length ≤
            ((gate :: gates).flatMap encodeCircuitGate).length := by simp
        exact hle.trans hraw
      have htailIndex : gateIndex + 1 + gates.length ≤ capacity := by
        have hsimp : gateIndex + (gates.length + 1) ≤ capacity := by
          simpa using hindex
        omega
      have htail := ih (gateIndex + 1) htailIndex htailRaw
      have hrow : (encodeNormalizedGateRow gateIndex gate).length ≤
          2 * capacity + 3 := by
        rw [encodeNormalizedGateRow_length]
        omega
      simp only [encodeNormalizedGateRowsFrom, List.length_append,
        List.length_cons]
      nlinarith

/-- Exact work on a valid gate family is at most one stream unit per row. -/
theorem gateFamilyStepsFrom_le_streamUnits (capacity baseStorage gateIndex : Nat)
    (gates : List CircuitGate)
    (hindex : gateIndex + gates.length ≤ capacity)
    (hraw : (gates.flatMap encodeCircuitGate).length ≤ capacity) :
    gateFamilyStepsFrom gateIndex gates ≤
      gates.length * streamUnitBound capacity baseStorage := by
  induction gates generalizing gateIndex with
  | nil => simp [gateFamilyStepsFrom]
  | cons gate gates ih =>
      have hgate : (encodeCircuitGate gate).length ≤ capacity := by
        have hle : (encodeCircuitGate gate).length ≤
            ((gate :: gates).flatMap encodeCircuitGate).length := by simp
        exact hle.trans hraw
      have htailRaw : (gates.flatMap encodeCircuitGate).length ≤ capacity := by
        have hle : (gates.flatMap encodeCircuitGate).length ≤
            ((gate :: gates).flatMap encodeCircuitGate).length := by simp
        exact hle.trans hraw
      have htailIndex : gateIndex + 1 + gates.length ≤ capacity := by
        have hsimp : gateIndex + (gates.length + 1) ≤ capacity := by
          simpa using hindex
        omega
      have hhead := gateSteps_le_streamUnit capacity baseStorage gateIndex gate
        hgate (by omega)
      have htail := ih (gateIndex + 1) htailIndex htailRaw
      simp only [gateFamilyStepsFrom, List.length_cons]
      nlinarith

/-- Shared canonical rejection budget, measured only through the raw circuit
encoding and the number of decoded rows. -/
def canonicalRejectBound (c : Circuit) : Nat :=
  (c.inputCount + 1) +
    (c.gates.length + 1) * streamUnitBound (encodeCircuit c).length 0 + 1

/-- Every canonical circuit violating `WellFormed` rejects within the shared
canonical budget. -/
theorem canonical_invalid_rejectsIn (c : Circuit) (hinvalid : ¬ c.WellFormed) :
    RejectsIn (_root_.Turing.initList machine (encodeCircuit c))
      (canonicalRejectBound c) := by
  let capacity := (encodeCircuit c).length
  rcases inputCount_phase initialState c.inputCount 0
      (c.gates.flatMap encodeCircuitGate ++ .outputMark :: encNat c.output)
      [] [] 0 0 0 0 with ⟨afterCount, hcount⟩
  have hcount' : (flip Option.bind step)^[c.inputCount + 1]
      (some (cfg (some .inputCount) initialState (encodeCircuit c)
        [] [] 0 0 0 0 0)) =
      some (cfg (some .gates) afterCount
        (c.gates.flatMap encodeCircuitGate ++ .outputMark :: encNat c.output)
        [] [] c.inputCount 0 0 0 0) := by
    simpa [encodeCircuit, List.append_assoc] using hcount
  have hinit : _root_.Turing.initList machine (encodeCircuit c) =
      cfg (some .inputCount) initialState (encodeCircuit c) [] [] 0 0 0 0 0 := by
    apply _root_.Turing.TM2Comp.Cfg_ext
    · rfl
    · rfl
    · funext stack
      cases stack <;>
        simp [cfg, machine, stackContents, _root_.Turing.initList]
  have hinputCount : c.inputCount ≤ capacity := by
    simp [capacity, encodeCircuit, encNat]
  have hgatesLength : c.gates.length ≤ capacity := by
    exact (gates_length_le_flat_encoding c.gates).trans (by
      simp [capacity, encodeCircuit, encNat]
      omega)
  have hbodyCapacity :
      (c.gates.flatMap encodeCircuitGate ++
        .outputMark :: encNat c.output).length ≤ capacity := by
    simp [capacity, encodeCircuit, encNat]
    omega
  have hrawCapacity :
      (c.gates.flatMap encodeCircuitGate).length ≤ capacity := by
    simp [capacity, encodeCircuit, encNat]
    omega
  by_cases hgates : ∀ i (hi : i < c.gates.length),
      (c.gates.get ⟨i, hi⟩).ValidAt c.inputCount (0 + i)
  · have houtput : ¬ c.output < c.gates.length := by
      intro hlt
      exact hinvalid ⟨hlt, by simpa using hgates⟩
    have hle : c.gates.length ≤ c.output := Nat.not_lt.mp houtput
    obtain ⟨extra, houtputEq⟩ := Nat.exists_eq_add_of_le hle
    rcases gateFamily_phase afterCount c.gates 0 c.inputCount hgates
        (.outputMark :: encNat c.output) [] [] with ⟨afterGates, hgaterun⟩
    have htag : step
        (cfg (some .gates) afterGates (.outputMark :: encNat c.output) []
          (encodeNormalizedGateRowsFrom 0 c.gates).reverse c.inputCount
          c.gates.length 0 0 0) =
        some (cfg (some (.parseOperand .outputGate))
          { afterGates with inputBuffer := some .outputMark }
          (encNat c.output) []
          (encodeNormalizedGateRowsFrom 0 c.gates).reverse c.inputCount
          c.gates.length 0 0 0) := by
      exact gates_output_step afterGates (encNat c.output) []
        (encodeNormalizedGateRowsFrom 0 c.gates).reverse c.inputCount
        c.gates.length 0 0 0
    have hrows : (encodeNormalizedGateRowsFrom 0 c.gates).length ≤
        c.gates.length * (2 * capacity + 3) :=
      normalizedRows_length_le_capacity 0 c.gates capacity (by omega)
        hrawCapacity
    have hfield : c.gates.length + extra + 2 ≤ capacity := by
      simp [capacity, encodeCircuit, encNat] at hbodyCapacity ⊢
      omega
    have houtputReject := invalidOutputIndex_rejectsIn
      { afterGates with inputBuffer := some .outputMark } c.gates.length extra
      c.inputCount [] (encodeNormalizedGateRowsFrom 0 c.gates).reverse
    have houtputUnit := invalidOutputRejectBound_le_streamUnit capacity 0
      c.gates.length extra c.inputCount []
      (encodeNormalizedGateRowsFrom 0 c.gates).reverse hfield hinputCount
      hgatesLength (by simpa using hrows)
    have houtputReject' := RejectsIn.mono houtputReject houtputUnit
    have houtputReject'' : RejectsIn
        (cfg (some (.parseOperand .outputGate))
          { afterGates with inputBuffer := some .outputMark }
          (encNat c.output) []
          (encodeNormalizedGateRowsFrom 0 c.gates).reverse c.inputCount
          c.gates.length 0 0 0)
        (streamUnitBound capacity 0) := by
      simpa [houtputEq] using houtputReject'
    have hafterTag := RejectsIn.before_step htag houtputReject''
    have hfamilySteps := gateFamilyStepsFrom_le_streamUnits capacity 0 0
      c.gates (by omega) hrawCapacity
    have hbody := RejectsIn.before_steps (gateFamilyStepsFrom 0 c.gates)
      (by simpa using hgaterun) hafterTag
    have hbody' : RejectsIn
        (cfg (some .gates) afterCount
          (c.gates.flatMap encodeCircuitGate ++
            .outputMark :: encNat c.output) [] [] c.inputCount 0 0 0 0)
        ((c.gates.length + 1) * streamUnitBound capacity 0 + 1) :=
      RejectsIn.mono hbody (by nlinarith)
    have hfull := RejectsIn.before_steps (c.inputCount + 1) hcount' hbody'
    rw [hinit]
    exact RejectsIn.mono hfull (by
      simp [canonicalRejectBound, capacity]
      omega)
  · have hbody := gateFamily_rejectsIn_of_not_valid afterCount c.gates 0
        c.inputCount hgates (.outputMark :: encNat c.output) [] [] capacity 0
        hbodyCapacity hinputCount (by omega) (by simp)
    have hfull := RejectsIn.before_steps (c.inputCount + 1) hcount' hbody
    rw [hinit]
    exact RejectsIn.mono hfull (by
      simp [canonicalRejectBound, gateFamilyRejectBound, capacity]
      omega)

/-- With no pre-existing staged storage, one stream unit is quartic in the raw
capacity. -/
theorem streamUnitBound_zero_le_quartic (n : Nat) :
    streamUnitBound n 0 ≤ 524288 * (n + 1) ^ 4 := by
  let a := n + 1
  have ha : 1 ≤ a := by simp [a]
  have hone : 1 ≤ a ^ 2 := by nlinarith
  have hmag : streamMagnitude n 0 ≤ 9 * a ^ 2 := by
    simp [streamMagnitude, a]
  have hsq := Nat.pow_le_pow_left hmag 2
  have hsq' : streamMagnitude n 0 ^ 2 ≤ 81 * a ^ 4 := by
    calc
      streamMagnitude n 0 ^ 2 ≤ (9 * a ^ 2) ^ 2 := hsq
      _ = 81 * a ^ 4 := by ring
  have hpow4 : 1 ≤ a ^ 4 := by nlinarith
  simp only [streamUnitBound]
  change 4096 * streamMagnitude n 0 ^ 2 + 4096 ≤ 524288 * a ^ 4
  nlinarith

/-- The canonical rejection budget is dominated by the public sextic bound. -/
theorem canonicalRejectBound_le (c : Circuit) :
    canonicalRejectBound c ≤ stepBound (encodeCircuit c).length := by
  let n := (encodeCircuit c).length
  let a := n + 1
  have ha : 1 ≤ a := by simp [a]
  have hinput : c.inputCount + 1 ≤ a := by
    simp [a, n, encodeCircuit, encNat]
  have hgates : c.gates.length + 1 ≤ a := by
    have hgl := gates_length_le_flat_encoding c.gates
    calc
      c.gates.length + 1 ≤
          (c.gates.flatMap encodeCircuitGate).length + 1 :=
        Nat.add_le_add_right hgl 1
      _ ≤ a := by
        simp [a, n, encodeCircuit, encNat]
        omega
  have hunit : streamUnitBound n 0 ≤ 524288 * a ^ 4 := by
    simpa [a] using streamUnitBound_zero_le_quartic n
  have hpow56 : a ^ 5 ≤ a ^ 6 :=
    pow_le_pow_right₀ ha (by omega)
  have hpow16 : a ≤ a ^ 6 := by
    simpa using (pow_le_pow_right₀ ha (show 1 ≤ 6 by omega))
  change canonicalRejectBound c ≤ stepBound n
  simp only [canonicalRejectBound, stepBound]
  change c.inputCount + 1 +
      (c.gates.length + 1) * streamUnitBound n 0 + 1 ≤
    1048576 * a ^ 6 + 1048576
  have hproduct : (c.gates.length + 1) * streamUnitBound n 0 ≤
      524288 * a ^ 5 := by
    calc
      (c.gates.length + 1) * streamUnitBound n 0 ≤
          a * (524288 * a ^ 4) := Nat.mul_le_mul hgates hunit
      _ = 524288 * a ^ 5 := by ring
  nlinarith

end CLRS.Chapter34.Turing.GeneralCircuitToSAT.Normalizer
