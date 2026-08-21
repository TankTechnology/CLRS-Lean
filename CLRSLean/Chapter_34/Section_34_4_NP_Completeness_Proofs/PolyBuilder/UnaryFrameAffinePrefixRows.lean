import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameAffinePrefixRowsSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Growing affine-prefix rows: polynomial-time interface
-/

noncomputable section

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Recursive execution bytes have the closed ordinal-indexed row form. -/
theorem unaryFrameAffinePrefixRowsStreamFrom_eq_ofFn
    (current : Nat) (payload : List UnaryFrameSym) (count : Nat) :
    unaryFrameAffinePrefixRowsStreamFrom current payload count =
      (List.ofFn fun row : Fin count =>
        payload ++ encodeUnaryFrame (List.ofFn fun index : Fin row.val =>
          current + index.val)).flatMap fun row => row ++ [.frameEnd] := by
  induction count generalizing current payload with
  | zero => rfl
  | succ count ih =>
      rw [unaryFrameAffinePrefixRowsStreamFrom, List.ofFn_succ,
        List.flatMap_cons, ih]
      congr 1
      · have hempty :
            (List.ofFn fun index : Fin (0 : Fin (count + 1)).val =>
              current + index.val) = [] := by simp
        rw [hempty]
        simp [encodeUnaryFrame]
      · apply congrArg (List.flatMap
            (fun row => row ++ [UnaryFrameSym.frameEnd]))
        apply List.ofFn_inj.mpr
        funext index
        simp only [Fin.val_succ]
        rw [List.ofFn_succ]
        simp only [encodeUnaryFrame, List.flatMap_cons, Fin.val_zero,
          Nat.add_zero, List.append_assoc]
        apply congrArg
          (fun tail => payload ++ (encodeUnaryFrameBlock current ++ tail))
        apply congrArg encodeUnaryFrame
        apply List.ofFn_inj.mpr
        funext position
        simp only [Fin.val_cast, Fin.val_succ]
        omega

/-- The recursive simulation target is exactly the public marked row
semantics. -/
theorem unaryFrameAffinePrefixRowsStream_eq_from
    (family : UnaryFrameAffinePrefixRows) :
    unaryFrameAffinePrefixRowsStream family =
      unaryFrameAffinePrefixRowsStreamFrom family.base [] family.count := by
  rw [unaryFrameAffinePrefixRowsStreamFrom_eq_ofFn]
  unfold unaryFrameAffinePrefixRowsStream
    unaryFrameAffinePrefixRowValues
  simp only [List.nil_append]
  have hrows :
      (List.ofFn fun row : Fin family.count =>
        encodeUnaryFrame (List.ofFn fun index : Fin row.val =>
          family.base + index.val)) =
      (List.ofFn fun row : Fin family.count =>
        List.ofFn fun index : Fin row.val =>
          family.base + index.val).map encodeUnaryFrame := by
    rw [List.map_ofFn]
    rfl
  rw [hrows, List.flatMap_map]

/-- Exact successful run for the public row stream. -/
def unaryFrameAffinePrefixRowsRev_run
    (family : UnaryFrameAffinePrefixRows) :
    StateTransition.EvalsToInTime
      (step unaryFrameAffinePrefixRowsRevProgram)
      (initialCfg unaryFrameAffinePrefixRowsRevProgram
        (encodeUnaryFrameAffinePrefixRows family))
      (some (haltCfg unaryFrameAffinePrefixRowsRevProgram
        (unaryFrameAffinePrefixRowsStream family).reverse))
      (unaryFrameAffinePrefixRowsRevSteps family) := by
  simpa [unaryFrameAffinePrefixRowsStream_eq_from] using
    unaryFrameAffinePrefixRowsRev_runFrom family

theorem encodeUnaryFrameAffinePrefixRows_length
    (family : UnaryFrameAffinePrefixRows) :
    (encodeUnaryFrameAffinePrefixRows family).length =
      family.base + family.count + 2 := by
  simp [encodeUnaryFrameAffinePrefixRows]
  omega

private theorem unaryFrameAffinePrefixRowsPayloadFrom_length_le
    (current : Nat) (payload : List UnaryFrameSym) (count : Nat) :
    (unaryFrameAffinePrefixRowsPayloadFrom current payload count).length ≤
      payload.length + count * (current + count + 1) := by
  induction count generalizing current payload with
  | zero => simp [unaryFrameAffinePrefixRowsPayloadFrom]
  | succ count ih =>
      simp only [unaryFrameAffinePrefixRowsPayloadFrom]
      have h := ih (current + 1)
        (payload ++ encodeUnaryFrameBlock current)
      simp [encodeUnaryFrameBlock] at h ⊢
      nlinarith

private theorem unaryFrameAffinePrefixRowsPhaseSteps_le
    (current : Nat) (payload : List UnaryFrameSym) (count : Nat) :
    unaryFrameAffinePrefixRowsPhaseSteps current payload count ≤
      count *
        (4 * (payload.length + count * (current + count + 1)) +
          5 * (current + count) + 8) := by
  induction count generalizing current payload with
  | zero => simp [unaryFrameAffinePrefixRowsPhaseSteps]
  | succ count ih =>
      simp only [unaryFrameAffinePrefixRowsPhaseSteps]
      let nextPayload := payload ++ encodeUnaryFrameBlock current
      have hrest := ih (current + 1) nextPayload
      have hnextLength : nextPayload.length = payload.length + current + 1 := by
        simp [nextPayload, encodeUnaryFrameBlock]
        omega
      have hbudget :
          nextPayload.length + count * (current + 1 + count + 1) ≤
            payload.length + (count + 1) * (current + (count + 1) + 1) := by
        rw [hnextLength]
        nlinarith
      have hfactor :
          4 * (nextPayload.length + count * (current + 1 + count + 1)) +
              5 * (current + 1 + count) + 8 ≤
            4 * (payload.length + (count + 1) *
              (current + (count + 1) + 1)) +
              5 * (current + (count + 1)) + 8 := by
        omega
      have hrest' :
          unaryFrameAffinePrefixRowsPhaseSteps (current + 1)
              nextPayload count ≤
            count *
              (4 * (payload.length + (count + 1) *
                (current + (count + 1) + 1)) +
                5 * (current + (count + 1)) + 8) :=
        hrest.trans (Nat.mul_le_mul_left count hfactor)
      have hfirst : unaryFrameAffinePrefixRowsPhaseCost
            current payload.length ≤
          4 * (payload.length + (count + 1) *
            (current + (count + 1) + 1)) +
            5 * (current + (count + 1)) + 8 := by
        simp [unaryFrameAffinePrefixRowsPhaseCost]
        omega
      calc
        unaryFrameAffinePrefixRowsPhaseCost current payload.length +
              unaryFrameAffinePrefixRowsPhaseSteps (current + 1)
                nextPayload count ≤
            (4 * (payload.length + (count + 1) *
              (current + (count + 1) + 1)) +
              5 * (current + (count + 1)) + 8) +
            count *
              (4 * (payload.length + (count + 1) *
                (current + (count + 1) + 1)) +
                5 * (current + (count + 1)) + 8) :=
          Nat.add_le_add hfirst hrest'
        _ = (count + 1) *
              (4 * (payload.length + (count + 1) *
                (current + (count + 1) + 1)) +
                5 * (current + (count + 1)) + 8) := by ring

/-- Coarse cubic envelope in the unary source length. -/
theorem unaryFrameAffinePrefixRowsRev_steps_le
    (family : UnaryFrameAffinePrefixRows) :
    unaryFrameAffinePrefixRowsRevSteps family ≤
      30 * (encodeUnaryFrameAffinePrefixRows family).length ^ 3 + 30 := by
  have hphase := unaryFrameAffinePrefixRowsPhaseSteps_le
    family.base [] family.count
  have hpayload := unaryFrameAffinePrefixRowsPayloadFrom_length_le
    family.base [] family.count
  let n := family.base + family.count + 2
  have hn : 1 ≤ n := by omega
  have hbase : family.base ≤ n := by omega
  have hcount : family.count ≤ n := by omega
  have hsum : family.base + family.count + 1 ≤ n := by omega
  have hpayload' :
      (unaryFrameAffinePrefixRowsPayloadFrom family.base []
        family.count).length ≤ n ^ 2 := by
    calc
      _ ≤ 0 + family.count *
          (family.base + family.count + 1) := by simpa using hpayload
      _ ≤ n * n := by
        simpa only [Nat.zero_add] using Nat.mul_le_mul hcount hsum
      _ = n ^ 2 := by ring
  have hfactor :
      4 * (0 + family.count *
          (family.base + family.count + 1)) +
          5 * (family.base + family.count) + 8 ≤ 17 * n ^ 2 := by
    have hproduct : family.count *
        (family.base + family.count + 1) ≤ n ^ 2 := by
      simpa [pow_two] using Nat.mul_le_mul hcount hsum
    nlinarith
  have hphase' :
      unaryFrameAffinePrefixRowsPhaseSteps family.base [] family.count ≤
        17 * n ^ 3 := by
    calc
      _ ≤ family.count *
          (4 * (0 + family.count *
            (family.base + family.count + 1)) +
            5 * (family.base + family.count) + 8) := hphase
      _ ≤ n * (17 * n ^ 2) := Nat.mul_le_mul hcount hfactor
      _ = 17 * n ^ 3 := by ring
  rw [encodeUnaryFrameAffinePrefixRows_length]
  change unaryFrameAffinePrefixRowsRevSteps family ≤ 30 * n ^ 3 + 30
  simp only [unaryFrameAffinePrefixRowsRevSteps]
  nlinarith

/-- Concrete polynomial-time TM2 for the reversed marked-row stream. -/
noncomputable def unaryFrameAffinePrefixRowsRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameAffinePrefixRows id
      (fun family => (unaryFrameAffinePrefixRowsStream family).reverse) where
  tm := compile unaryFrameAffinePrefixRowsRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 30 * Polynomial.X ^ 3 + 30
  outputsFun := fun family => by
    have builderRun := unaryFrameAffinePrefixRowsRev_run family
    have compiledRun := compile_evalsToInTime
      unaryFrameAffinePrefixRowsRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameAffinePrefixRowsRevProgram).step
        (_root_.Turing.initList (compile unaryFrameAffinePrefixRowsRevProgram)
          (encodeUnaryFrameAffinePrefixRows family))
        (some (_root_.Turing.haltList
          (compile unaryFrameAffinePrefixRowsRevProgram)
          (unaryFrameAffinePrefixRowsStream family).reverse))
        (unaryFrameAffinePrefixRowsRevSteps family) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : unaryFrameAffinePrefixRowsRevSteps family ≤
        (30 * Polynomial.X ^ 3 + 30).eval
          (encodeUnaryFrameAffinePrefixRows family).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFrameAffinePrefixRowsRev_steps_le family
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameAffinePrefixRowsRevProgram).step
        (_root_.Turing.initList (compile unaryFrameAffinePrefixRowsRevProgram)
          (encodeUnaryFrameAffinePrefixRows family))
        (some (_root_.Turing.haltList
          (compile unaryFrameAffinePrefixRowsRevProgram)
          (unaryFrameAffinePrefixRowsStream family).reverse))
        ((30 * Polynomial.X ^ 3 + 30).eval
          (encodeUnaryFrameAffinePrefixRows family).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward marked-row stream. -/
noncomputable def unaryFrameAffinePrefixRowsStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameAffinePrefixRows id unaryFrameAffinePrefixRowsStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameAffinePrefixRowsRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
