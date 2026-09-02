import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveFinalize

/-!
# Polynomial-time same-input marked-row interleaving

This file connects input duplication, the two embedded transducer runs, and
the verified output finalizer into one fixed polynomial-time TM2.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

namespace UnaryFrameMarkedRowParallelInterleave

variable {α Γ : Type} [Fintype Γ]
variable {encode : α → List Γ}
variable {leftFamily rightFamily : α → UnaryFrameMarkedRowFamily}
variable
  (M₁ : _root_.Turing.TM2ComputableInPolyTime encode
    encodeUnaryFrameMarkedRowFamily leftFamily)
  (M₂ : _root_.Turing.TM2ComputableInPolyTime encode
    encodeUnaryFrameMarkedRowFamily rightFamily)

/-- Semantic target of the same-input interleaver. -/
def interleavedFamily
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length)
    (input : α) : UnaryFrameMarkedRowFamily :=
  UnaryFrameAlignedMarkedRowPair.interleaved
    { left := leftFamily input
      right := rightFamily input
      rowAligned := hAligned input }

/-- The first embedded halt configuration is definitionally the second
embedded start configuration once their frozen stack banks are identified. -/
lemma first_halt_eq_second_start (input : α) :
    mapCfg₁ M₁ M₂
        (_root_.Turing.haltList M₁.tm
          (List.map M₁.outputAlphabet.invFun
            (encodeUnaryFrameMarkedRowFamily (leftFamily input))))
        (_root_.Turing.initList M₂.tm
          (List.map M₂.inputAlphabet.invFun (encode input))).stk =
      mapCfg₂ M₁ M₂
        (_root_.Turing.initList M₂.tm
          (List.map M₂.inputAlphabet.invFun (encode input)))
        (_root_.Turing.haltList M₁.tm
          (List.map M₁.outputAlphabet.invFun
            (encodeUnaryFrameMarkedRowFamily (leftFamily input)))).stk := by
  rfl

/-- A uniform polynomial bound for duplication, both source transducers, and
the linear merge/restore suffix. -/
def time
    : Polynomial ℕ :=
  M₁.time + M₂.time +
    2 *
      (((_root_.Turing.TM2Comp.maxPushCount₁ M₁ : ℕ) : Polynomial ℕ) *
          M₁.time +
        ((_root_.Turing.TM2Comp.maxPushCount₁ M₂ : ℕ) : Polynomial ℕ) *
          M₂.time) +
    6 * Polynomial.X + 4

/-- End-to-end bounded run of the combined physical machine. -/
def outputsFun
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length)
    (input : α) :
    _root_.Turing.TM2OutputsInTime (machine M₁ M₂)
      (List.map (inputAlphabet M₁ M₂).invFun (encode input))
      (some (List.map (outputAlphabet M₁ M₂).invFun
        (encodeUnaryFrameMarkedRowFamily
          (interleavedFamily hAligned input))))
      ((time M₁ M₂).eval (encode input).length) := by
  let rawInput := encode input
  let n := rawInput.length
  let m₁ := M₁.time.eval n
  let m₂ := M₂.time.eval n
  let left := leftFamily input
  let right := rightFamily input
  let output := interleavedFamily hAligned input
  let leftStream := encodeUnaryFrameMarkedRowFamily left
  let rightStream := encodeUnaryFrameMarkedRowFamily right
  let initC := _root_.Turing.initList (machine M₁ M₂)
    (List.map M₁.inputAlphabet.invFun rawInput)
  let init₁ := _root_.Turing.initList M₁.tm
    (List.map M₁.inputAlphabet.invFun rawInput)
  let halt₁ := _root_.Turing.haltList M₁.tm
    (List.map M₁.outputAlphabet.invFun leftStream)
  let init₂ := _root_.Turing.initList M₂.tm
    (List.map M₂.inputAlphabet.invFun rawInput)
  let halt₂ := _root_.Turing.haltList M₂.tm
    (List.map M₂.outputAlphabet.invFun rightStream)
  let afterDuplicate := mapCfg₁ M₁ M₂ init₁ init₂.stk
  let afterFirst := mapCfg₁ M₁ M₂ halt₁ init₂.stk
  let secondStart := mapCfg₂ M₁ M₂ init₂ halt₁.stk
  let afterSecond := mapCfg₂ M₁ M₂ halt₂ halt₁.stk
  let haltC := _root_.Turing.haltList (machine M₁ M₂)
    (List.map M₂.outputAlphabet.invFun
      (encodeUnaryFrameMarkedRowFamily output))
  change EvalsToInTime (machine M₁ M₂).step initC (some haltC)
    ((time M₁ M₂).eval n)

  have hdup : EvalsToInTime (machine M₁ M₂).step initC
      (some afterDuplicate) (2 * rawInput.length + 2) :=
    ⟨⟨2 * rawInput.length + 2, by
      simpa [initC, afterDuplicate, init₁, init₂,
        duplicatedSecondInput] using duplicate_phase M₁ M₂ rawInput⟩,
      le_rfl⟩

  have h₁run : EvalsToInTime M₁.tm.step init₁ (some halt₁) m₁ := by
    simpa [n, m₁, init₁, halt₁, leftStream, left,
      _root_.Turing.TM2OutputsInTime, rawInput] using M₁.outputsFun input
  have hstop₁ : M₁.tm.step halt₁ = none := rfl
  have h₁lift : EvalsToInTime (machine M₁ M₂).step afterDuplicate
      (some afterFirst) m₁ := by
    simpa [afterDuplicate, afterFirst] using
      _root_.Turing.TM2Comp.evalsToInTime_lift
        (fun cfg => mapCfg₁ M₁ M₂ cfg init₂.stk)
        h₁run hstop₁ (stepC_sim₁ M₁ M₂ init₂.stk)
  have hbridge : afterFirst = secondStart := by
    simpa [afterFirst, secondStart, halt₁, init₂, leftStream, left] using
      first_halt_eq_second_start M₁ M₂ input
  rw [hbridge] at h₁lift

  have h₂run : EvalsToInTime M₂.tm.step init₂ (some halt₂) m₂ := by
    simpa [n, m₂, init₂, halt₂, rightStream, right,
      _root_.Turing.TM2OutputsInTime, rawInput] using M₂.outputsFun input
  have hstop₂ : M₂.tm.step halt₂ = none := rfl
  have h₂lift : EvalsToInTime (machine M₁ M₂).step secondStart
      (some afterSecond) m₂ := by
    simpa [secondStart, afterSecond] using
      _root_.Turing.TM2Comp.evalsToInTime_lift
        (fun cfg => mapCfg₂ M₁ M₂ cfg halt₁.stk)
        h₂run hstop₂ (stepC_sim₂ M₁ M₂ halt₁.stk)

  have hfinal : EvalsToInTime (machine M₁ M₂).step afterSecond
      (some haltC) (finalizeAlignedRowsSteps left.rows right.rows) := by
    simpa [afterSecond, haltC, halt₁, halt₂, leftStream, rightStream,
      output, interleavedFamily, left, right] using
      finalize_aligned_rows_run M₁ M₂ left right (hAligned input)

  let throughFirst := EvalsToInTime.trans (machine M₁ M₂).step
    (2 * rawInput.length + 2) m₁ initC afterDuplicate
    (some secondStart) hdup h₁lift
  let throughSecond := EvalsToInTime.trans (machine M₁ M₂).step
    (m₁ + (2 * rawInput.length + 2)) m₂ initC secondStart
    (some afterSecond) throughFirst h₂lift
  let full := EvalsToInTime.trans (machine M₁ M₂).step
    (m₂ + (m₁ + (2 * rawInput.length + 2)))
    (finalizeAlignedRowsSteps left.rows right.rows)
    initC afterSecond (some haltC) throughSecond hfinal

  let A := _root_.Turing.TM2Comp.maxPushCount₁ M₁
  let B := _root_.Turing.TM2Comp.maxPushCount₁ M₂
  have hsteps₁ : (M₁.outputsFun input).toEvalsTo.steps ≤ m₁ := by
    simpa [m₁, n] using (M₁.outputsFun input).steps_le_m
  have hsteps₂ : (M₂.outputsFun input).toEvalsTo.steps ≤ m₂ := by
    simpa [m₂, n] using (M₂.outputsFun input).steps_le_m
  have hleftRaw := _root_.Turing.TM2Comp.evalsTo_out_len_le M₁ input
  have hrightRaw := _root_.Turing.TM2Comp.evalsTo_out_len_le M₂ input
  have hleftLen : leftStream.length ≤ n + A * m₁ := by
    dsimp [leftStream, left, n, A]
    simpa using le_trans hleftRaw
      (Nat.add_le_add_left (Nat.mul_le_mul_left
        (_root_.Turing.TM2Comp.maxPushCount₁ M₁) hsteps₁) rawInput.length)
  have hrightLen : rightStream.length ≤ n + B * m₂ := by
    dsimp [rightStream, right, n, B]
    simpa using le_trans hrightRaw
      (Nat.add_le_add_left (Nat.mul_le_mul_left
        (_root_.Turing.TM2Comp.maxPushCount₁ M₂) hsteps₂) rawInput.length)
  have hinterleaveLen :
      (encodeUnaryFrameMarkedRows
        (interleaveUnaryFrameMarkedRows left.rows right.rows)).length =
        leftStream.length + rightStream.length := by
    have hlen := encodeUnaryFrameMarkedRows_interleave_length
      left.rows right.rows (hAligned input)
    have hleftStream : leftStream =
        encodeUnaryFrameMarkedRows left.rows := by
      rfl
    have hrightStream : rightStream =
        encodeUnaryFrameMarkedRows right.rows := by
      rfl
    rw [hleftStream, hrightStream]
    exact hlen
  have hfinalBound : finalizeAlignedRowsSteps left.rows right.rows ≤
      2 * (2 * n + A * m₁ + B * m₂) + 2 := by
    rw [finalizeAlignedRowsSteps, hinterleaveLen]
    omega
  have htime : (time M₁ M₂).eval n =
      m₁ + m₂ + 2 * (A * m₁ + B * m₂) + 6 * n + 4 := by
    simp [time, m₁, m₂, A, B, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_natCast,
      Polynomial.eval_ofNat]
  have hbound : finalizeAlignedRowsSteps left.rows right.rows +
        (m₂ + (m₁ + (2 * rawInput.length + 2))) ≤
      (time M₁ M₂).eval n := by
    rw [htime]
    dsimp [n]
    omega
  exact { full with steps_le_m := full.steps_le_m.trans hbound }

/-- Reusable concrete polynomial-time machine for same-input aligned row
families. -/
def computableInPolyTime
    (hAligned : ∀ input,
      (leftFamily input).rows.length = (rightFamily input).rows.length) :
    _root_.Turing.TM2ComputableInPolyTime encode
      encodeUnaryFrameMarkedRowFamily
      (interleavedFamily hAligned) where
  tm := machine M₁ M₂
  inputAlphabet := inputAlphabet M₁ M₂
  outputAlphabet := outputAlphabet M₁ M₂
  time := time M₁ M₂
  outputsFun := outputsFun M₁ M₂ hAligned

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
