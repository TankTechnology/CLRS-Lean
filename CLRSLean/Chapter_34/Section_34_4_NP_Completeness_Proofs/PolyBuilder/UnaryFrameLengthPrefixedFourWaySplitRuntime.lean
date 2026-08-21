import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitBounds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse
import CLRSLean.Chapter_34.Section_34_1_Polynomial_Time.Composition

/-!
# Polynomial-time TM2 for the dynamic four-way splitter

The verified builder is compiled to one concrete TM2.  Its reversed stack
output is then composed with the existing polynomial-time list reverser to
expose the forward four-row family stream.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Concrete linear-time TM2 producing the reversed four-row stream. -/
noncomputable def
    unaryFrameLengthPrefixedFourWayPacketFamilyOutputRev_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameLengthPrefixedFourWayPacketFamily id
      (fun packets =>
        (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse) where
  tm := compile unaryFrameLengthPrefixedFourWaySplitRevProgram
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := 6 * Polynomial.X + 2
  outputsFun := fun packets => by
    have builderRun :=
      unaryFrameLengthPrefixedFourWaySplitRev_haltRun packets
    have compiledRun := compile_evalsToInTime
      unaryFrameLengthPrefixedFourWaySplitRevProgram builderRun
    have machineRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameLengthPrefixedFourWaySplitRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets))
        (some (_root_.Turing.haltList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse))
        (unaryFrameLengthPrefixedFourWayPacketFamilySteps packets + 2) := by
      simpa only [encodeCfg_initialCfg, encodeCfg_haltCfg] using compiledRun
    have htime :
        unaryFrameLengthPrefixedFourWayPacketFamilySteps packets + 2 ≤
          (6 * Polynomial.X + 2).eval
            (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets).length := by
      have hbound :=
        unaryFrameLengthPrefixedFourWayPacketFamilySteps_le packets
      simp only [Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_ofNat]
      omega
    have boundedRun : _root_.StateTransition.EvalsToInTime
        (compile unaryFrameLengthPrefixedFourWaySplitRevProgram).step
        (_root_.Turing.initList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets))
        (some (_root_.Turing.haltList
          (compile unaryFrameLengthPrefixedFourWaySplitRevProgram)
          (unaryFrameLengthPrefixedFourWayPacketFamilyOutput packets).reverse))
        ((6 * Polynomial.X + 2).eval
          (encodeUnaryFrameLengthPrefixedFourWayPacketFamily packets).length) :=
      ⟨machineRun.toEvalsTo, machineRun.steps_le_m.trans htime⟩
    simpa [_root_.Turing.TM2OutputsInTime, compile] using boundedRun

/-- Forward four-row packet-family stream, exposed as a concrete
polynomial-time TM2 computation. -/
noncomputable def
    unaryFrameLengthPrefixedFourWayPacketFamilyOutput_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime
      encodeUnaryFrameLengthPrefixedFourWayPacketFamily id
      unaryFrameLengthPrefixedFourWayPacketFamilyOutput := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      unaryFrameLengthPrefixedFourWayPacketFamilyOutputRev_computableInPolyTime
      (reverse_computableInPolyTime (Γ := UnaryFrameSym))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.PolyBuilder
