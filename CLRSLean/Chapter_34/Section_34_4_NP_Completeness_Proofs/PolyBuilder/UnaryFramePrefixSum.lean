import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFramePrefixSumSimulation
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition
import Mathlib.Tactic

/-!
# Unary-frame prefix sums: polynomial-time interface

This file isolates the size arithmetic and the public `TM2ComputableInPolyTime`
contract from the machine and its exact simulation.  The resulting fixed TM2
turns a unary base followed by unary increments into the delimiter-bearing
stream of all prefix values.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- The final accumulator is the base plus the sum of all increments. -/
theorem unaryFramePrefixSumFinal_eq_add_sum
    (current : Nat) (increments : List Nat) :
    unaryFramePrefixSumFinal current increments = current + increments.sum := by
  induction increments generalizing current with
  | nil => simp [unaryFramePrefixSumFinal]
  | cons increment rest ih =>
      simp only [unaryFramePrefixSumFinal, List.sum_cons]
      rw [ih]
      omega

/-- One symbol per unary unit and one delimiter per input field. -/
theorem encodeUnaryFramePrefixSum_length (frame : UnaryFramePrefixSum) :
    (encodeUnaryFramePrefixSum frame).length =
      frame.base + frame.increments.sum + frame.increments.length + 1 := by
  simp [encodeUnaryFramePrefixSum, encodeUnaryFrameBlock]
  omega

/-- The whole phase loop is quadratic in the unary input budget. -/
theorem unaryFramePrefixSumPhaseSteps_le
    (current : Nat) (increments : List Nat) :
    unaryFramePrefixSumPhaseSteps current increments ≤
      increments.length *
        (7 * (current + increments.sum) + 5) := by
  induction increments generalizing current with
  | nil => simp [unaryFramePrefixSumPhaseSteps]
  | cons increment rest ih =>
      simp only [unaryFramePrefixSumPhaseSteps, List.length_cons,
        List.sum_cons]
      have hrest := ih (current + increment)
      have hcost : unaryFramePrefixSumPhaseCost current increment ≤
          7 * (current + (increment + rest.sum)) + 5 := by
        simp [unaryFramePrefixSumPhaseCost]
        omega
      calc
        unaryFramePrefixSumPhaseCost current increment +
              unaryFramePrefixSumPhaseSteps (current + increment) rest ≤
            (7 * (current + (increment + rest.sum)) + 5) +
              rest.length *
                (7 * (current + (increment + rest.sum)) + 5) := by
                  apply Nat.add_le_add hcost
                  simpa [Nat.add_assoc] using hrest
        _ = (rest.length + 1) *
              (7 * (current + (increment + rest.sum)) + 5) := by ring

/-- A coarse quadratic envelope for the exact reverse-output execution. -/
theorem unaryFramePrefixSumRev_steps_le (frame : UnaryFramePrefixSum) :
    unaryFramePrefixSumRevSteps frame ≤
      20 * (encodeUnaryFramePrefixSum frame).length ^ 2 + 20 := by
  have hphase := unaryFramePrefixSumPhaseSteps_le
    frame.base frame.increments
  have hfinal := unaryFramePrefixSumFinal_eq_add_sum
    frame.base frame.increments
  let n := frame.base + frame.increments.sum + frame.increments.length + 1
  have hn : 1 ≤ n := by omega
  have hbase : frame.base ≤ n := by omega
  have hsum : frame.base + frame.increments.sum ≤ n := by omega
  have hlength : frame.increments.length ≤ n := by omega
  have hfactor :
      7 * (frame.base + frame.increments.sum) + 5 ≤ 12 * n := by
    omega
  have hphase' :
      unaryFramePrefixSumPhaseSteps frame.base frame.increments ≤
        12 * n ^ 2 := by
    calc
      _ ≤ frame.increments.length *
          (7 * (frame.base + frame.increments.sum) + 5) := hphase
      _ ≤ n * (12 * n) := Nat.mul_le_mul hlength hfactor
      _ = 12 * n ^ 2 := by ring
  rw [encodeUnaryFramePrefixSum_length]
  change unaryFramePrefixSumRevSteps frame ≤ 20 * n ^ 2 + 20
  simp only [unaryFramePrefixSumRevSteps]
  rw [hfinal]
  nlinarith

/-- Concrete polynomial-time machine for the reversed prefix-value stream. -/
noncomputable def unaryFramePrefixSumRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFramePrefixSum id
      (fun frame => (unaryFramePrefixSumStream frame).reverse) where
  tm := compile unaryFramePrefixSumRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 20 * Polynomial.X ^ 2 + 20
  outputsFun := fun frame => by
    have builderRun := unaryFramePrefixSumRev_run frame
    have compiledRun := compile_evalsToInTime
      unaryFramePrefixSumRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFramePrefixSumRevProgram).step
        (_root_.Turing.initList (compile unaryFramePrefixSumRevProgram)
          (encodeUnaryFramePrefixSum frame))
        (some (_root_.Turing.haltList
          (compile unaryFramePrefixSumRevProgram)
          (unaryFramePrefixSumStream frame).reverse))
        (unaryFramePrefixSumRevSteps frame) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg,
        List.append_nil] using compiledRun
    have htime : unaryFramePrefixSumRevSteps frame ≤
        (20 * Polynomial.X ^ 2 + 20).eval
          (encodeUnaryFramePrefixSum frame).length := by
      simpa only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] using
        unaryFramePrefixSumRev_steps_le frame
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFramePrefixSumRevProgram).step
        (_root_.Turing.initList (compile unaryFramePrefixSumRevProgram)
          (encodeUnaryFramePrefixSum frame))
        (some (_root_.Turing.haltList
          (compile unaryFramePrefixSumRevProgram)
          (unaryFramePrefixSumStream frame).reverse))
        ((20 * Polynomial.X ^ 2 + 20).eval
          (encodeUnaryFramePrefixSum frame).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Reversing the prepend-built result yields the forward prefix stream. -/
noncomputable def unaryFramePrefixSumStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFramePrefixSum id unaryFramePrefixSumStream := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFramePrefixSumRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
