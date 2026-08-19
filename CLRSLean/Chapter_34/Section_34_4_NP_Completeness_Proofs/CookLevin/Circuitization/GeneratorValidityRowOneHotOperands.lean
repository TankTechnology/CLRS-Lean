import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStructuredRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneMarkedRowInvocationSource

/-!
# Ordered one-hot operands for Cook--Levin validity rows

The concrete exactly-one controller consumes one frame per semantic one-hot
group.  This module gives those frames a positional specification: the frame
at group `i` uses the group's consecutive tableau interval, while its gate
start is the sum of the exact costs of all preceding groups.  It then lifts
that specification from one validity-row seed to the complete row-major
family.

This is the semantic contract for the following fixed source controller.  In
particular, it exposes the precise runtime loop invariant without replacing
the required concrete TM2 by an oracle computation.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.CookLevin

open PolyBuilder

/-! ## Positional form of an affine exactly-one family -/

/-- The exact cost of all affine exactly-one groups preceding `index`. -/
def affineExactlyOnePrefixCost {n : Nat} (counts : Fin n → Nat)
    (index : Fin n) : Nat :=
  ∑ previous : Fin index.val,
    (3 * counts ⟨previous.val,
      Nat.lt_trans previous.isLt index.isLt⟩ + 4)

/-- Closed frame at one position of an ordered affine exactly-one family. -/
def affineExactlyOneRuntimeFrameAt (start : Nat) {n : Nat}
    (bases counts : Fin n → Nat) (index : Fin n) :
    AffineExactlyOneFrame :=
  { start := start + affineExactlyOnePrefixCost counts index
    rowBase := bases index
    count := counts index }

/-- Advancing one family position adds exactly the previous group's gate
cost to the accumulated prefix. -/
theorem affineExactlyOnePrefixCost_succ {n : Nat}
    (counts : Fin n → Nat) (index : Nat) (hnext : index + 1 < n) :
    affineExactlyOnePrefixCost counts ⟨index + 1, hnext⟩ =
      affineExactlyOnePrefixCost counts ⟨index, by omega⟩ +
        (3 * counts ⟨index, by omega⟩ + 4) := by
  unfold affineExactlyOnePrefixCost
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Consequently, adjacent runtime frames advance their gate start by the
exact affine exactly-one cost of the previous group. -/
theorem affineExactlyOneRuntimeFrameAt_succ_start
    (start : Nat) {n : Nat} (bases counts : Fin n → Nat)
    (index : Nat) (hnext : index + 1 < n) :
    (affineExactlyOneRuntimeFrameAt start bases counts
      ⟨index + 1, hnext⟩).start =
      (affineExactlyOneRuntimeFrameAt start bases counts
        ⟨index, by omega⟩).start +
        (3 * counts ⟨index, by omega⟩ + 4) := by
  simp only [affineExactlyOneRuntimeFrameAt]
  rw [affineExactlyOnePrefixCost_succ]
  omega

/-- Over a contiguous block whose counts are constant, frame starts form the
exact affine progression used by the concrete triple-stream controller. -/
theorem affineExactlyOneRuntimeFrameAt_add_const_start
    (start : Nat) {n : Nat} (bases counts : Fin n → Nat)
    (offset steps count : Nat) (hbound : offset + steps < n)
    (hcounts : ∀ index : Fin steps,
      counts ⟨offset + index.val, by omega⟩ = count) :
    (affineExactlyOneRuntimeFrameAt start bases counts
      ⟨offset + steps, hbound⟩).start =
      (affineExactlyOneRuntimeFrameAt start bases counts
        ⟨offset, by omega⟩).start + steps * (3 * count + 4) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      have hprefix : offset + steps < n := by omega
      calc
        (affineExactlyOneRuntimeFrameAt start bases counts
            ⟨offset + (steps + 1), hbound⟩).start =
            (affineExactlyOneRuntimeFrameAt start bases counts
              ⟨(offset + steps) + 1, by omega⟩).start := by
          congr 2
        _ = (affineExactlyOneRuntimeFrameAt start bases counts
              ⟨offset + steps, hprefix⟩).start +
              (3 * counts ⟨offset + steps, by omega⟩ + 4) := by
          exact affineExactlyOneRuntimeFrameAt_succ_start
            start bases counts (offset + steps) (by omega)
        _ = (affineExactlyOneRuntimeFrameAt start bases counts
              ⟨offset, by omega⟩).start +
              (steps + 1) * (3 * count + 4) := by
          rw [ih hprefix (fun index => hcounts index.castSucc)]
          have hlast := hcounts (Fin.last steps)
          rw [show counts ⟨offset + steps, by omega⟩ = count by
            simpa using hlast]
          ring

/-- The established snoc-recursive runtime family is exactly its positional
`List.ofFn` specification. -/
theorem affineExactlyOneRuntimeFrames_eq_ofFn
    (start n : Nat) (bases counts : Fin n → Nat) :
    affineExactlyOneRuntimeFrames start n bases counts =
      List.ofFn fun index : Fin n =>
        affineExactlyOneRuntimeFrameAt start bases counts index := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [affineExactlyOneRuntimeFrames]
      rw [ih, List.ofFn_succ']
      simp only [List.concat_eq_append]
      congr 1

/-! ## Arithmetic Cook--Levin group frames -/

/-- Exact runtime frame associated with one semantic row one-hot group. -/
noncomputable def arithmeticOneHotGroupFrame
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (group : CfgOneHotGroup tm H) : AffineExactlyOneFrame :=
  let equiv := cfgOneHotGroupEquivFin tm H
  affineExactlyOneRuntimeFrameAt start
    (fun index => arithmeticCfgOneHotGroupWireBase tm H rowBase
      (equiv.symm index))
    (fun index => arithmeticCfgOneHotGroupWireCount tm H
      (equiv.symm index))
    (equiv group)

/-- The output wire recorded by the semantic raw-one-hot trace is exactly the
closed last-gate index carried by the corresponding arithmetic runtime frame.
This removes the last semantic lookup from later conjunction-source code. -/
theorem arithmeticRawOneHot_output_eq_frame
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (group : CfgOneHotGroup tm H) :
    (rawOneHotGateTrace start
      (arithmeticCfgWires tm H rowBase)).outputs group =
      affineExactlyOneFrameOutputWire
        (arithmeticOneHotGroupFrame tm H start rowBase group) := by
  unfold rawOneHotGateTrace arithmeticOneHotGroupFrame
  dsimp only
  rw [exactlyOneFamilyGateTrace_output_eq]
  unfold affineExactlyOneFrameOutputWire affineExactlyOneRuntimeFrameAt
    affineExactlyOnePrefixCost
  simp_rw [arithmeticCfgOneHotGroupWires_eq_affine]
  simp [affineSequentialExactlyOneWires]

/-- Runtime progression parameters for the `H` consecutive cell-symbol
groups of one fixed verifier stack.  Its first base follows the stack-height
group, and both gate and source bases then advance by fixed stack-dependent
strides. -/
noncomputable def arithmeticStackCellOneHotProgression
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    AffineUnaryTripleProgression :=
  let heightFrame := arithmeticOneHotGroupFrame tm H start rowBase
    (.inr (.inr ⟨k, .inl ()⟩))
  let cellCount := (reachableAlphabet tm k).card + 1
  { base₁ := heightFrame.start + (3 * (H + 1) + 4)
    base₂ := heightFrame.rowBase + (H + 1)
    base₃ := cellCount
    step₁ := 3 * cellCount + 4
    step₂ := cellCount
    step₃ := 0
    count := H }

/-! ## Fixed row prefix and structured stack blocks -/

/-- The label group is the first row group, so its gate start is unchanged
and its source interval begins immediately after the halted bit. -/
@[simp] theorem arithmeticOneHotGroupFrame_label
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticOneHotGroupFrame tm H start rowBase (.inl ()) =
      { start := start
        rowBase := rowBase + 1
        count := labelCount tm + 1 } := by
  simp [arithmeticOneHotGroupFrame, affineExactlyOneRuntimeFrameAt,
    affineExactlyOnePrefixCost, arithmeticCfgOneHotGroupWireBase,
    arithmeticCfgOneHotGroupWireCount]

/-- The state group follows the label group by exactly one label-group gate
cost and one label-width source interval. -/
@[simp] theorem arithmeticOneHotGroupFrame_state
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticOneHotGroupFrame tm H start rowBase (.inr (.inl ())) =
      { start := start + (3 * (labelCount tm + 1) + 4)
        rowBase := rowBase + 1 + (labelCount tm + 1)
        count := stateCount tm } := by
  have hfirst : (cfgOneHotGroupEquivFin tm H).symm
      (⟨0, by simp [cfgOneHotGroupCount]⟩ :
        Fin (cfgOneHotGroupCount tm H)) = (.inl () : CfgOneHotGroup tm H) := by
    apply (cfgOneHotGroupEquivFin tm H).injective
    apply Fin.ext
    simp
  simp [arithmeticOneHotGroupFrame, affineExactlyOneRuntimeFrameAt,
    affineExactlyOnePrefixCost, arithmeticCfgOneHotGroupWireBase,
    arithmeticCfgOneHotGroupWireCount, hfirst]

/-- The two fixed groups emitted before the runtime stack loop. -/
noncomputable def arithmeticOneHotPrefixFrames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List AffineExactlyOneFrame :=
  [ arithmeticOneHotGroupFrame tm H start rowBase (.inl ())
  , arithmeticOneHotGroupFrame tm H start rowBase (.inr (.inl ())) ]

/-- Closed form consumed by the fixed prefix source controller. -/
theorem arithmeticOneHotPrefixFrames_eq_explicit
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticOneHotPrefixFrames tm H start rowBase =
      [ { start := start
          rowBase := rowBase + 1
          count := labelCount tm + 1 }
      , { start := start + (3 * (labelCount tm + 1) + 4)
          rowBase := rowBase + 1 + (labelCount tm + 1)
          count := stateCount tm } ] := by
  simp [arithmeticOneHotPrefixFrames]

/-- Every fixed stack begins with its runtime-height one-hot group. -/
@[simp] theorem arithmeticOneHotGroupFrame_stackHeight_count
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inl ()⟩))).count = H + 1 := by
  simp [arithmeticOneHotGroupFrame, affineExactlyOneRuntimeFrameAt,
    arithmeticCfgOneHotGroupWireCount]

/-- Structured source block for one fixed stack: its height frame followed by
the concrete affine progression of its `H` cell-symbol frames. -/
noncomputable def arithmeticStackOneHotFrames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    List AffineExactlyOneFrame :=
  arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inl ()⟩)) ::
    affineExactlyOneFramesOfTripleProgression
      (arithmeticStackCellOneHotProgression tm H start rowBase k)

/-- Instantiating the continuous stack source at the semantic height frame
and the fixed reachable-alphabet width gives exactly the canonical arithmetic
stack block. -/
theorem affineExactlyOneStackFrames_eq_arithmeticStack
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineExactlyOneStackFrames ((reachableAlphabet tm k).card + 1) H
        (arithmeticOneHotGroupFrame tm H start rowBase
          (.inr (.inr ⟨k, .inl ()⟩))).start
        (arithmeticOneHotGroupFrame tm H start rowBase
          (.inr (.inr ⟨k, .inl ()⟩))).rowBase =
      arithmeticStackOneHotFrames tm H start rowBase k := by
  unfold affineExactlyOneStackFrames arithmeticStackOneHotFrames
  congr 1
  · cases hframe : arithmeticOneHotGroupFrame tm H start rowBase
        (.inr (.inr ⟨k, .inl ()⟩)) with
    | mk frameStart frameBase frameCount =>
        have hcount := arithmeticOneHotGroupFrame_stackHeight_count
          tm H start rowBase k
        rw [hframe] at hcount
        simp only at hcount
        simp [affineExactlyOneHeightFrame, hcount]

/-- Closed source base of a stack-height one-hot group. -/
@[simp] theorem arithmeticOneHotGroupFrame_stackHeight_rowBase
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inl ()⟩))).rowBase =
      rowBase + 1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k := by
  simp [arithmeticOneHotGroupFrame, affineExactlyOneRuntimeFrameAt,
    arithmeticCfgOneHotGroupWireBase]

/-- Closed source base of a cell-symbol one-hot group. -/
@[simp] theorem arithmeticOneHotGroupFrame_stackCell_rowBase
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (k : tm.K) (index : Fin H) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inr index⟩))).rowBase =
      rowBase + 1 + (labelCount tm + 1) + stateCount tm +
        cfgStackBitOffset tm H k + (H + 1) +
          ((reachableAlphabet tm k).card + 1) * index.val := by
  simp [arithmeticOneHotGroupFrame, affineExactlyOneRuntimeFrameAt,
    arithmeticCfgOneHotGroupWireBase]

/-- Every cell-symbol group on one fixed stack has the same width. -/
@[simp] theorem arithmeticOneHotGroupFrame_stackCell_count
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (k : tm.K) (index : Fin H) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inr index⟩))).count =
      (reachableAlphabet tm k).card + 1 := by
  simp [arithmeticOneHotGroupFrame, affineExactlyOneRuntimeFrameAt,
    arithmeticCfgOneHotGroupWireCount]

/-- Cell-symbol group starts form the exact affine gate progression following
the stack-height group. -/
theorem arithmeticOneHotGroupFrame_stackCell_start
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (k : tm.K) (index : Fin H) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inr index⟩))).start =
      (arithmeticOneHotGroupFrame tm H start rowBase
        (.inr (.inr ⟨k, .inl ()⟩))).start +
        (3 * (H + 1) + 4) + index.val *
          (3 * ((reachableAlphabet tm k).card + 1) + 4) := by
  let equiv := cfgOneHotGroupEquivFin tm H
  let bases : Fin (cfgOneHotGroupCount tm H) → Nat := fun position =>
    arithmeticCfgOneHotGroupWireBase tm H rowBase (equiv.symm position)
  let counts : Fin (cfgOneHotGroupCount tm H) → Nat := fun position =>
    arithmeticCfgOneHotGroupWireCount tm H (equiv.symm position)
  let heightGroup : CfgOneHotGroup tm H :=
    .inr (.inr ⟨k, .inl ()⟩)
  let cellGroup : CfgOneHotGroup tm H :=
    .inr (.inr ⟨k, .inr index⟩)
  have hheightVal : (equiv heightGroup).val =
      2 + cfgOneHotStackOffset tm H k := by
    simp [equiv, heightGroup]
  have hcellVal : (equiv cellGroup).val =
      2 + cfgOneHotStackOffset tm H k + 1 + index.val := by
    simp [equiv, cellGroup]
  have hfirstBound : (equiv heightGroup).val + 1 <
      cfgOneHotGroupCount tm H := by
    have hcellBound := (equiv cellGroup).isLt
    omega
  have hfirst := affineExactlyOneRuntimeFrameAt_succ_start
    start bases counts (equiv heightGroup).val hfirstBound
  have hheightCount : counts (equiv heightGroup) = H + 1 := by
    simp [counts, heightGroup, arithmeticCfgOneHotGroupWireCount]
  have hfirst' :
      (affineExactlyOneRuntimeFrameAt start bases counts
        ⟨(equiv heightGroup).val + 1, hfirstBound⟩).start =
        (affineExactlyOneRuntimeFrameAt start bases counts
          (equiv heightGroup)).start + (3 * (H + 1) + 4) := by
    simpa [hheightCount] using hfirst
  have htailBound : (equiv heightGroup).val + 1 + index.val <
      cfgOneHotGroupCount tm H := by
    have hcellBound := (equiv cellGroup).isLt
    omega
  have hcellCounts : ∀ offset : Fin index.val,
      counts ⟨(equiv heightGroup).val + 1 + offset.val, by omega⟩ =
        (reachableAlphabet tm k).card + 1 := by
    intro offset
    let priorIndex : Fin H := ⟨offset.val,
      Nat.lt_trans offset.isLt index.isLt⟩
    let priorGroup : CfgOneHotGroup tm H :=
      .inr (.inr ⟨k, .inr priorIndex⟩)
    have hposition :
        (⟨(equiv heightGroup).val + 1 + offset.val, by omega⟩ :
          Fin (cfgOneHotGroupCount tm H)) = equiv priorGroup := by
      apply Fin.ext
      simp [equiv, heightGroup, priorGroup, priorIndex]
    rw [hposition]
    simp [counts, priorGroup, arithmeticCfgOneHotGroupWireCount]
  have htail := affineExactlyOneRuntimeFrameAt_add_const_start
    start bases counts ((equiv heightGroup).val + 1) index.val
      ((reachableAlphabet tm k).card + 1) htailBound hcellCounts
  have hcellPosition : equiv cellGroup =
      ⟨(equiv heightGroup).val + 1 + index.val, htailBound⟩ := by
    apply Fin.ext
    change (equiv cellGroup).val =
      (equiv heightGroup).val + 1 + index.val
    omega
  change (affineExactlyOneRuntimeFrameAt start bases counts
      (equiv cellGroup)).start =
    (affineExactlyOneRuntimeFrameAt start bases counts
      (equiv heightGroup)).start +
      (3 * (H + 1) + 4) + index.val *
        (3 * ((reachableAlphabet tm k).card + 1) + 4)
  calc
    (affineExactlyOneRuntimeFrameAt start bases counts
        (equiv cellGroup)).start =
        (affineExactlyOneRuntimeFrameAt start bases counts
          ⟨(equiv heightGroup).val + 1 + index.val, htailBound⟩).start := by
      rw [hcellPosition]
    _ = (affineExactlyOneRuntimeFrameAt start bases counts
          ⟨(equiv heightGroup).val + 1, hfirstBound⟩).start +
          index.val *
            (3 * ((reachableAlphabet tm k).card + 1) + 4) := htail
    _ = (affineExactlyOneRuntimeFrameAt start bases counts
          (equiv heightGroup)).start + (3 * (H + 1) + 4) +
          index.val *
            (3 * ((reachableAlphabet tm k).card + 1) + 4) := by
      rw [hfirst']

/-- The fixed triple-progression machine's structured output is exactly the
ordered cell-symbol group block of one stack. -/
theorem arithmeticStackCellOneHotProgression_frames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    affineExactlyOneFramesOfTripleProgression
        (arithmeticStackCellOneHotProgression tm H start rowBase k) =
      List.ofFn fun index : Fin H =>
        arithmeticOneHotGroupFrame tm H start rowBase
          (.inr (.inr ⟨k, .inr index⟩)) := by
  unfold affineExactlyOneFramesOfTripleProgression
  simp only [arithmeticStackCellOneHotProgression]
  rw [affineUnaryTripleProgressionRows_eq_ofFn, List.map_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  have hstart := arithmeticOneHotGroupFrame_stackCell_start
    tm H start rowBase k index
  have hbase := arithmeticOneHotGroupFrame_stackCell_rowBase
    tm H start rowBase k index
  have hcount := arithmeticOneHotGroupFrame_stackCell_count
    tm H start rowBase k index
  cases hframe : arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr ⟨k, .inr index⟩)) with
  | mk frameStart frameBase frameCount =>
      rw [hframe] at hstart hbase hcount
      simp only at hstart hbase hcount
      change
        ({
          start :=
            (arithmeticOneHotGroupFrame tm H start rowBase
              (.inr (.inr ⟨k, .inl ()⟩))).start +
              (3 * (H + 1) + 4) + index.val *
                (3 * ((reachableAlphabet tm k).card + 1) + 4)
          rowBase :=
            (arithmeticOneHotGroupFrame tm H start rowBase
              (.inr (.inr ⟨k, .inl ()⟩))).rowBase +
              (H + 1) + index.val *
                ((reachableAlphabet tm k).card + 1)
          count := (reachableAlphabet tm k).card + 1 + index.val * 0
        } :
            AffineExactlyOneFrame) =
          ({
            start := frameStart
            rowBase := frameBase
            count := frameCount
          } : AffineExactlyOneFrame)
      rw [arithmeticOneHotGroupFrame_stackHeight_rowBase]
      simp only [AffineExactlyOneFrame.mk.injEq]
      constructor
      · omega
      constructor
      · rw [hbase]
        ring
      · omega

/-- The structured stack block is exactly the semantic height group followed
by all cell-symbol groups in increasing cell order. -/
theorem arithmeticStackOneHotFrames_eq_groups
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) (k : tm.K) :
    arithmeticStackOneHotFrames tm H start rowBase k =
      arithmeticOneHotGroupFrame tm H start rowBase
          (.inr (.inr ⟨k, .inl ()⟩)) ::
        List.ofFn fun index : Fin H =>
          arithmeticOneHotGroupFrame tm H start rowBase
            (.inr (.inr ⟨k, .inr index⟩)) := by
  simp [arithmeticStackOneHotFrames,
    arithmeticStackCellOneHotProgression_frames]

private theorem cfgOneHotGroupEquivFin_symm_stackHeight
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (stack : Fin (@Fintype.card tm.K tm.kFin)) :
    (cfgOneHotGroupEquivFin tm H).symm
        ⟨2 + (H + 1) * stack.val, by
          simp only [cfgOneHotGroupCount]
          calc
            2 + (H + 1) * stack.val <
                2 + (H + 1) * @Fintype.card tm.K tm.kFin :=
              Nat.add_lt_add_left
                (Nat.mul_lt_mul_of_pos_left stack.isLt
                  (Nat.zero_lt_succ H)) 2
            _ = 2 + @Fintype.card tm.K tm.kFin * (H + 1) := by
              rw [Nat.mul_comm]⟩ =
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm stack, .inl ()⟩) :
          CfgOneHotGroup tm H) := by
  apply (cfgOneHotGroupEquivFin tm H).injective
  apply Fin.ext
  simp [cfgOneHotStackOffset]

private theorem cfgOneHotGroupEquivFin_symm_stackCell
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (stack : Fin (@Fintype.card tm.K tm.kFin)) (index : Fin H) :
    (cfgOneHotGroupEquivFin tm H).symm
        ⟨2 + (H + 1) * stack.val + 1 + index.val, by
          simp only [cfgOneHotGroupCount]
          have hstack := stack.isLt
          have hindex := index.isLt
          nlinarith⟩ =
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm stack, .inr index⟩) :
          CfgOneHotGroup tm H) := by
  apply (cfgOneHotGroupEquivFin tm H).injective
  apply Fin.ext
  simp [cfgOneHotStackOffset]

private theorem cfgOneHotGroupEquivFin_symm_stackHeight_natAdd
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (stack : Fin (@Fintype.card tm.K tm.kFin)) :
    (cfgOneHotGroupEquivFin tm H).symm
        (Fin.natAdd 2
          (⟨stack.val * (H + 1), by
            exact Nat.mul_lt_mul_of_pos_right stack.isLt
              (Nat.zero_lt_succ H)⟩ :
            Fin (@Fintype.card tm.K tm.kFin * (H + 1)))) =
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm stack, .inl ()⟩) :
          CfgOneHotGroup tm H) := by
  rw [show Fin.natAdd 2
      (⟨stack.val * (H + 1), by
        exact Nat.mul_lt_mul_of_pos_right stack.isLt
          (Nat.zero_lt_succ H)⟩ :
        Fin (@Fintype.card tm.K tm.kFin * (H + 1))) =
      ⟨2 + (H + 1) * stack.val, by
        calc
          2 + (H + 1) * stack.val <
              2 + (H + 1) * @Fintype.card tm.K tm.kFin :=
            Nat.add_lt_add_left
              (Nat.mul_lt_mul_of_pos_left stack.isLt
                (Nat.zero_lt_succ H)) 2
          _ = 2 + @Fintype.card tm.K tm.kFin * (H + 1) := by
            rw [Nat.mul_comm]⟩ by
    apply Fin.ext
    change 2 + stack.val * (H + 1) = 2 + (H + 1) * stack.val
    rw [Nat.mul_comm stack.val]]
  exact cfgOneHotGroupEquivFin_symm_stackHeight tm H stack

private theorem stackCellProductIndex_lt
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (stack : Fin (@Fintype.card tm.K tm.kFin)) (index : Fin H) :
    stack.val * (H + 1) + index.succ.val <
      @Fintype.card tm.K tm.kFin * (H + 1) := by
  calc
    stack.val * (H + 1) + index.succ.val <
        stack.val * (H + 1) + (H + 1) :=
      Nat.add_lt_add_left index.succ.isLt _
    _ = (stack.val + 1) * (H + 1) := by ring
    _ ≤ @Fintype.card tm.K tm.kFin * (H + 1) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr stack.isLt)

private theorem cfgOneHotGroupEquivFin_symm_stackCell_natAdd
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (stack : Fin (@Fintype.card tm.K tm.kFin)) (index : Fin H) :
    (cfgOneHotGroupEquivFin tm H).symm
        (Fin.natAdd 2
          (⟨stack.val * (H + 1) + index.succ.val, by
            exact stackCellProductIndex_lt tm H stack index⟩ :
            Fin (@Fintype.card tm.K tm.kFin * (H + 1)))) =
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm stack, .inr index⟩) :
          CfgOneHotGroup tm H) := by
  rw [show Fin.natAdd 2
      (⟨stack.val * (H + 1) + index.succ.val, by
        exact stackCellProductIndex_lt tm H stack index⟩ :
        Fin (@Fintype.card tm.K tm.kFin * (H + 1))) =
      ⟨2 + (H + 1) * stack.val + 1 + index.val, by
        have hbound := stackCellProductIndex_lt tm H stack index
        calc
          2 + (H + 1) * stack.val + 1 + index.val =
              2 + (stack.val * (H + 1) + index.succ.val) := by
            simp only [Fin.val_succ]
            ring
          _ < 2 + @Fintype.card tm.K tm.kFin * (H + 1) :=
            Nat.add_lt_add_left hbound 2⟩ by
    apply Fin.ext
    change 2 + (stack.val * (H + 1) + index.succ.val) =
      2 + (H + 1) * stack.val + 1 + index.val
    rw [Nat.mul_comm stack.val]
    simp [Nat.add_assoc, Nat.add_comm]]
  exact cfgOneHotGroupEquivFin_symm_stackCell tm H stack index

/-- Controller-oriented decomposition of one row: the two fixed groups,
then one height-plus-cells block for every fixed stack. -/
noncomputable def arithmeticStructuredOneHotFrames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    List AffineExactlyOneFrame :=
  arithmeticOneHotPrefixFrames tm H start rowBase ++
    (List.ofFn fun stack : Fin (@Fintype.card tm.K tm.kFin) =>
      arithmeticStackOneHotFrames tm H start rowBase
        ((@Fintype.equivFin tm.K tm.kFin).symm stack)).flatten

/-- Fixed reachable-alphabet widths carried in the verifier's canonical stack
order.  These are compile-time constants of the verifier, not runtime data. -/
noncomputable def verifierOneHotCellCounts
    (tm : _root_.Turing.FinTM2) : List Nat :=
  List.ofFn fun stack : Fin (@Fintype.card tm.K tm.kFin) =>
    (reachableAlphabet tm
      ((@Fintype.equivFin tm.K tm.kFin).symm stack)).card + 1

/-- Consecutive canonical stack indices advance the tableau source offset by
the complete height-plus-cells width of the preceding stack. -/
private theorem cfgStackBitOffset_equivFin_succ
    (tm : _root_.Turing.FinTM2) (H index : Nat)
    (hnext : index + 1 < @Fintype.card tm.K tm.kFin) :
    cfgStackBitOffset tm H
        ((@Fintype.equivFin tm.K tm.kFin).symm ⟨index + 1, hnext⟩) =
      cfgStackBitOffset tm H
          ((@Fintype.equivFin tm.K tm.kFin).symm
            ⟨index, by omega⟩) +
        cfgStackBitWidth tm H
          ((@Fintype.equivFin tm.K tm.kFin).symm
            ⟨index, by omega⟩) := by
  let stackEquiv := @Fintype.equivFin tm.K tm.kFin
  let offsetAt : Fin (@Fintype.card tm.K tm.kFin) → Nat := fun position =>
    ∑ j : Fin position.val,
      cfgStackBitWidth tm H
        (stackEquiv.symm (Fin.castLE position.isLt.le j))
  let next : Fin (@Fintype.card tm.K tm.kFin) := ⟨index + 1, hnext⟩
  let current : Fin (@Fintype.card tm.K tm.kFin) := ⟨index, by omega⟩
  have hnextOffset : cfgStackBitOffset tm H (stackEquiv.symm next) =
      offsetAt next := by
    unfold cfgStackBitOffset
    change offsetAt (stackEquiv (stackEquiv.symm next)) = offsetAt next
    exact congrArg offsetAt (stackEquiv.apply_symm_apply next)
  have hcurrentOffset : cfgStackBitOffset tm H (stackEquiv.symm current) =
      offsetAt current := by
    unfold cfgStackBitOffset
    change offsetAt (stackEquiv (stackEquiv.symm current)) = offsetAt current
    exact congrArg offsetAt (stackEquiv.apply_symm_apply current)
  have hsum : offsetAt next = offsetAt current +
      cfgStackBitWidth tm H (stackEquiv.symm current) := by
    change
      (∑ j : Fin (index + 1), cfgStackBitWidth tm H
        (stackEquiv.symm (Fin.castLE hnext.le j))) =
        (∑ j : Fin index, cfgStackBitWidth tm H
          (stackEquiv.symm (Fin.castLE (by omega) j))) +
          cfgStackBitWidth tm H (stackEquiv.symm current)
    rw [Fin.sum_univ_castSucc]
    congr 1
  simpa [stackEquiv, next, current] using
    hnextOffset.trans (hsum.trans (congrArg
      (fun value => value + cfgStackBitWidth tm H (stackEquiv.symm current))
      hcurrentOffset.symm))

/-- The first canonical stack has no preceding stack bits. -/
private theorem cfgStackBitOffset_equivFin_zero
    (tm : _root_.Turing.FinTM2) (H : Nat)
    (hcard : 0 < @Fintype.card tm.K tm.kFin) :
    cfgStackBitOffset tm H
      ((@Fintype.equivFin tm.K tm.kFin).symm ⟨0, hcard⟩) = 0 := by
  let stackEquiv := @Fintype.equivFin tm.K tm.kFin
  let offsetAt : Fin (@Fintype.card tm.K tm.kFin) → Nat := fun position =>
    ∑ j : Fin position.val,
      cfgStackBitWidth tm H
        (stackEquiv.symm (Fin.castLE position.isLt.le j))
  let first : Fin (@Fintype.card tm.K tm.kFin) := ⟨0, hcard⟩
  have hfirstOffset : cfgStackBitOffset tm H (stackEquiv.symm first) =
      offsetAt first := by
    unfold cfgStackBitOffset
    change offsetAt (stackEquiv (stackEquiv.symm first)) = offsetAt first
    exact congrArg offsetAt (stackEquiv.apply_symm_apply first)
  simpa [stackEquiv, first, offsetAt] using hfirstOffset

/-- The source base of the next canonical stack is exactly the base left by
the fixed-width stack source. -/
private theorem arithmeticStackHeight_rowBase_succ
    (tm : _root_.Turing.FinTM2) (H start rowBase index : Nat)
    (hnext : index + 1 < @Fintype.card tm.K tm.kFin) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm ⟨index + 1, hnext⟩,
          .inl ()⟩))).rowBase =
      affineExactlyOneStackEndBase
        ((reachableAlphabet tm
          ((@Fintype.equivFin tm.K tm.kFin).symm
            ⟨index, by omega⟩)).card + 1) H
        (arithmeticOneHotGroupFrame tm H start rowBase
          (.inr (.inr
            ⟨(@Fintype.equivFin tm.K tm.kFin).symm
              ⟨index, by omega⟩, .inl ()⟩))).rowBase := by
  rw [arithmeticOneHotGroupFrame_stackHeight_rowBase,
    arithmeticOneHotGroupFrame_stackHeight_rowBase,
    cfgStackBitOffset_equivFin_succ]
  simp only [affineExactlyOneStackEndBase, cfgStackBitWidth]
  ring

/-- The gate start of the next canonical stack is exactly the start left by
the fixed-width stack source. -/
private theorem arithmeticStackHeight_start_succ
    (tm : _root_.Turing.FinTM2) (H start rowBase index : Nat)
    (hnext : index + 1 < @Fintype.card tm.K tm.kFin) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm ⟨index + 1, hnext⟩,
          .inl ()⟩))).start =
      affineExactlyOneStackEndStart
        ((reachableAlphabet tm
          ((@Fintype.equivFin tm.K tm.kFin).symm
            ⟨index, by omega⟩)).card + 1) H
        (arithmeticOneHotGroupFrame tm H start rowBase
          (.inr (.inr
            ⟨(@Fintype.equivFin tm.K tm.kFin).symm
              ⟨index, by omega⟩, .inl ()⟩))).start := by
  let stackEquiv := @Fintype.equivFin tm.K tm.kFin
  let groupEquiv := cfgOneHotGroupEquivFin tm H
  let bases : Fin (cfgOneHotGroupCount tm H) → Nat := fun position =>
    arithmeticCfgOneHotGroupWireBase tm H rowBase
      (groupEquiv.symm position)
  let counts : Fin (cfgOneHotGroupCount tm H) → Nat := fun position =>
    arithmeticCfgOneHotGroupWireCount tm H (groupEquiv.symm position)
  let current : Fin (@Fintype.card tm.K tm.kFin) := ⟨index, by omega⟩
  let next : Fin (@Fintype.card tm.K tm.kFin) := ⟨index + 1, hnext⟩
  let currentHeight : CfgOneHotGroup tm H :=
    .inr (.inr ⟨stackEquiv.symm current, .inl ()⟩)
  let nextHeight : CfgOneHotGroup tm H :=
    .inr (.inr ⟨stackEquiv.symm next, .inl ()⟩)
  have hcurrentVal : (groupEquiv currentHeight).val =
      2 + (H + 1) * index := by
    simp [groupEquiv, currentHeight, current, stackEquiv,
      cfgOneHotStackOffset]
  have hnextVal : (groupEquiv nextHeight).val =
      2 + (H + 1) * (index + 1) := by
    simp [groupEquiv, nextHeight, next, stackEquiv,
      cfgOneHotStackOffset]
  have hfirstBound : (groupEquiv currentHeight).val + 1 <
      cfgOneHotGroupCount tm H := by
    refine Nat.lt_of_le_of_lt ?_ (groupEquiv nextHeight).isLt
    rw [hcurrentVal, hnextVal]
    nlinarith
  have hfirst := affineExactlyOneRuntimeFrameAt_succ_start
    start bases counts (groupEquiv currentHeight).val hfirstBound
  have hheightCount : counts (groupEquiv currentHeight) = H + 1 := by
    simp [counts, currentHeight, arithmeticCfgOneHotGroupWireCount]
  have hfirst' :
      (affineExactlyOneRuntimeFrameAt start bases counts
        ⟨(groupEquiv currentHeight).val + 1, hfirstBound⟩).start =
        (affineExactlyOneRuntimeFrameAt start bases counts
          (groupEquiv currentHeight)).start + (3 * (H + 1) + 4) := by
    simpa [hheightCount] using hfirst
  have htailBound : (groupEquiv currentHeight).val + 1 + H <
      cfgOneHotGroupCount tm H := by
    rw [hcurrentVal, show 2 + (H + 1) * index + 1 + H =
      (groupEquiv nextHeight).val by rw [hnextVal]; ring]
    exact (groupEquiv nextHeight).isLt
  have hcellCounts : ∀ cell : Fin H,
      counts ⟨(groupEquiv currentHeight).val + 1 + cell.val,
        by omega⟩ =
        (reachableAlphabet tm (stackEquiv.symm current)).card + 1 := by
    intro cell
    let cellGroup : CfgOneHotGroup tm H :=
      .inr (.inr ⟨stackEquiv.symm current, .inr cell⟩)
    have hposition :
        (⟨(groupEquiv currentHeight).val + 1 + cell.val, by omega⟩ :
          Fin (cfgOneHotGroupCount tm H)) = groupEquiv cellGroup := by
      apply Fin.ext
      simp [groupEquiv, currentHeight, cellGroup, current, stackEquiv,
        cfgOneHotStackOffset]
    rw [hposition]
    simp [counts, cellGroup, arithmeticCfgOneHotGroupWireCount]
  have htail := affineExactlyOneRuntimeFrameAt_add_const_start
    start bases counts ((groupEquiv currentHeight).val + 1) H
      ((reachableAlphabet tm (stackEquiv.symm current)).card + 1)
      htailBound hcellCounts
  have hnextPosition : groupEquiv nextHeight =
      ⟨(groupEquiv currentHeight).val + 1 + H, htailBound⟩ := by
    apply Fin.ext
    change (groupEquiv nextHeight).val =
      (groupEquiv currentHeight).val + 1 + H
    calc
      (groupEquiv nextHeight).val =
          2 + (H + 1) * (index + 1) := hnextVal
      _ = 2 + (H + 1) * index + 1 + H := by ring
      _ = (groupEquiv currentHeight).val + 1 + H := by rw [hcurrentVal]
  change (affineExactlyOneRuntimeFrameAt start bases counts
      (groupEquiv nextHeight)).start =
    affineExactlyOneStackEndStart
      ((reachableAlphabet tm (stackEquiv.symm current)).card + 1) H
      (affineExactlyOneRuntimeFrameAt start bases counts
        (groupEquiv currentHeight)).start
  calc
    (affineExactlyOneRuntimeFrameAt start bases counts
        (groupEquiv nextHeight)).start =
        (affineExactlyOneRuntimeFrameAt start bases counts
          ⟨(groupEquiv currentHeight).val + 1 + H,
            htailBound⟩).start := by rw [hnextPosition]
    _ = (affineExactlyOneRuntimeFrameAt start bases counts
          ⟨(groupEquiv currentHeight).val + 1, hfirstBound⟩).start +
          H * (3 *
            ((reachableAlphabet tm (stackEquiv.symm current)).card + 1) +
              4) := htail
    _ = affineExactlyOneStackEndStart
          ((reachableAlphabet tm (stackEquiv.symm current)).card + 1) H
          (affineExactlyOneRuntimeFrameAt start bases counts
            (groupEquiv currentHeight)).start := by
      rw [hfirst']
      unfold affineExactlyOneStackEndStart
      ring

/-- The first stack begins exactly after the label/state compact prefix. -/
private theorem arithmeticFirstStackHeight_start
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (hcard : 0 < @Fintype.card tm.K tm.kFin) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm ⟨0, hcard⟩,
          .inl ()⟩))).start =
      affineExactlyOneStructuredRowStackStart
        (labelCount tm + 1) (stateCount tm) start := by
  let stackEquiv := @Fintype.equivFin tm.K tm.kFin
  let groupEquiv := cfgOneHotGroupEquivFin tm H
  let bases : Fin (cfgOneHotGroupCount tm H) → Nat := fun position =>
    arithmeticCfgOneHotGroupWireBase tm H rowBase
      (groupEquiv.symm position)
  let counts : Fin (cfgOneHotGroupCount tm H) → Nat := fun position =>
    arithmeticCfgOneHotGroupWireCount tm H (groupEquiv.symm position)
  let first : Fin (@Fintype.card tm.K tm.kFin) := ⟨0, hcard⟩
  let firstHeight : CfgOneHotGroup tm H :=
    .inr (.inr ⟨stackEquiv.symm first, .inl ()⟩)
  let stateGroup : CfgOneHotGroup tm H := .inr (.inl ())
  have hheightVal : (groupEquiv firstHeight).val = 2 := by
    simp [groupEquiv, firstHeight, first, stackEquiv,
      cfgOneHotStackOffset]
  have hbound : 1 + 1 < cfgOneHotGroupCount tm H := by
    rw [show 1 + 1 = (groupEquiv firstHeight).val by
      exact hheightVal.symm]
    exact (groupEquiv firstHeight).isLt
  have hheightPosition : groupEquiv firstHeight = ⟨1 + 1, hbound⟩ := by
    apply Fin.ext
    exact hheightVal
  have hstateVal : (groupEquiv stateGroup).val = 1 := by
    simp [groupEquiv, stateGroup]
  have hstatePosition : groupEquiv stateGroup =
      (⟨1, by omega⟩ : Fin (cfgOneHotGroupCount tm H)) := by
    apply Fin.ext
    exact hstateVal
  have hcount : counts (groupEquiv stateGroup) = stateCount tm := by
    simp [counts, stateGroup, arithmeticCfgOneHotGroupWireCount]
  have hsucc := affineExactlyOneRuntimeFrameAt_succ_start
    start bases counts 1 hbound
  change (affineExactlyOneRuntimeFrameAt start bases counts
      (groupEquiv firstHeight)).start =
    affineExactlyOneStructuredRowStackStart
      (labelCount tm + 1) (stateCount tm) start
  rw [hheightPosition, hsucc, ← hstatePosition, hcount]
  change (arithmeticOneHotGroupFrame tm H start rowBase stateGroup).start +
      (3 * stateCount tm + 4) =
    affineExactlyOneStructuredRowStackStart
      (labelCount tm + 1) (stateCount tm) start
  rw [show arithmeticOneHotGroupFrame tm H start rowBase stateGroup =
      { start := start + (3 * (labelCount tm + 1) + 4)
        rowBase := rowBase + 1 + (labelCount tm + 1)
        count := stateCount tm } by
    exact arithmeticOneHotGroupFrame_state tm H start rowBase]
  unfold affineExactlyOneStructuredRowStackStart
  simp only

/-- The first stack's source interval begins exactly after halted, label, and
state bits. -/
private theorem arithmeticFirstStackHeight_rowBase
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat)
    (hcard : 0 < @Fintype.card tm.K tm.kFin) :
    (arithmeticOneHotGroupFrame tm H start rowBase
      (.inr (.inr
        ⟨(@Fintype.equivFin tm.K tm.kFin).symm ⟨0, hcard⟩,
          .inl ()⟩))).rowBase =
      affineExactlyOneStructuredRowStackBase
        (labelCount tm + 1) (stateCount tm) rowBase := by
  rw [arithmeticOneHotGroupFrame_stackHeight_rowBase,
    cfgStackBitOffset_equivFin_zero]
  unfold affineExactlyOneStructuredRowStackBase
  ring

/-- Starting at any canonical stack index, the recursive fixed-width source
emits exactly that nonempty suffix of semantic stack blocks. -/
private theorem affineExactlyOneStackFamilyFrames_fromArithmetic :
    ∀ (tm : _root_.Turing.FinTM2) (H start rowBase n offset : Nat)
      (hbound : offset + n < @Fintype.card tm.K tm.kFin),
      affineExactlyOneStackFamilyFrames
          (List.ofFn fun position : Fin (n + 1) =>
            (reachableAlphabet tm
              ((@Fintype.equivFin tm.K tm.kFin).symm
                ⟨offset + position.val, by omega⟩)).card + 1)
          H
          (arithmeticOneHotGroupFrame tm H start rowBase
            (.inr (.inr
              ⟨(@Fintype.equivFin tm.K tm.kFin).symm
                ⟨offset, by omega⟩, .inl ()⟩))).start
          (arithmeticOneHotGroupFrame tm H start rowBase
            (.inr (.inr
              ⟨(@Fintype.equivFin tm.K tm.kFin).symm
                ⟨offset, by omega⟩, .inl ()⟩))).rowBase =
        (List.ofFn fun position : Fin (n + 1) =>
          arithmeticStackOneHotFrames tm H start rowBase
            ((@Fintype.equivFin tm.K tm.kFin).symm
              ⟨offset + position.val, by omega⟩)).flatten := by
  intro tm H start rowBase n
  induction n with
  | zero =>
      intro offset hbound
      simpa [affineExactlyOneStackFamilyFrames] using
        affineExactlyOneStackFrames_eq_arithmeticStack tm H start rowBase
          ((@Fintype.equivFin tm.K tm.kFin).symm
            ⟨offset, by omega⟩)
  | succ n ih =>
      intro offset hbound
      conv_lhs => rw [List.ofFn_succ]
      conv_rhs => rw [List.ofFn_succ]
      simp only [affineExactlyOneStackFamilyFrames, Fin.val_zero,
        Nat.add_zero, Fin.val_succ, List.flatten_cons]
      rw [affineExactlyOneStackFrames_eq_arithmeticStack]
      congr 1
      have hstart := arithmeticStackHeight_start_succ
        tm H start rowBase offset (by omega)
      have hbase := arithmeticStackHeight_rowBase_succ
        tm H start rowBase offset (by omega)
      rw [← hstart, ← hbase]
      convert ih (offset + 1) (by omega) using 1
      · congr 1
        apply List.ofFn_inj.mpr
        funext position
        have hposition :
            (⟨offset + (position.val + 1), by omega⟩ :
              Fin (@Fintype.card tm.K tm.kFin)) =
              ⟨offset + 1 + position.val, by omega⟩ := by
          apply Fin.ext
          change offset + (position.val + 1) = offset + 1 + position.val
          omega
        rw [hposition]
      · apply congrArg List.flatten
        apply List.ofFn_inj.mpr
        funext position
        have hposition :
            (⟨offset + (position.val + 1), by omega⟩ :
              Fin (@Fintype.card tm.K tm.kFin)) =
              ⟨offset + 1 + position.val, by omega⟩ := by
          apply Fin.ext
          change offset + (position.val + 1) = offset + 1 + position.val
          omega
        rw [hposition]

/-- The raw row frames are exactly the semantic groups in their explicit
`cfgOneHotGroupEquivFin` order. -/
theorem arithmeticRawOneHotFrames_eq_groupFrames
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticRawOneHotFrames tm H start rowBase =
      List.ofFn fun index : Fin (cfgOneHotGroupCount tm H) =>
        arithmeticOneHotGroupFrame tm H start rowBase
          ((cfgOneHotGroupEquivFin tm H).symm index) := by
  unfold arithmeticRawOneHotFrames arithmeticOneHotGroupFrame
  rw [affineExactlyOneRuntimeFrames_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext index
  simp

/-- The controller-oriented prefix/stack decomposition preserves the exact
canonical `cfgOneHotGroupEquivFin` order, including `H = 0`. -/
theorem arithmeticStructuredOneHotFrames_eq_raw
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    arithmeticStructuredOneHotFrames tm H start rowBase =
      arithmeticRawOneHotFrames tm H start rowBase := by
  rw [arithmeticRawOneHotFrames_eq_groupFrames]
  unfold arithmeticStructuredOneHotFrames arithmeticOneHotPrefixFrames
  simp only [cfgOneHotGroupCount]
  rw [List.ofFn_add]
  rw [List.ofFn_mul]
  simp only [List.ofFn_succ, List.ofFn_zero, List.cons_append,
    List.nil_append]
  congr 1
  congr 1
  apply congrArg List.flatten
  apply List.ofFn_inj.mpr
  funext stack
  rw [arithmeticStackOneHotFrames_eq_groups]
  simp only [List.cons.injEq]
  constructor
  · apply congrArg (arithmeticOneHotGroupFrame tm H start rowBase)
    symm
    exact cfgOneHotGroupEquivFin_symm_stackHeight_natAdd tm H stack
  apply List.ofFn_inj.mpr
  funext index
  apply congrArg (arithmeticOneHotGroupFrame tm H start rowBase)
  symm
  exact cfgOneHotGroupEquivFin_symm_stackCell_natAdd tm H stack index

/-- Instantiating the fixed structured-row source with the verifier's finite
widths produces the canonical arithmetic one-hot frames for one row. -/
theorem affineExactlyOneStructuredRowFrames_eq_arithmeticRaw
    (tm : _root_.Turing.FinTM2) (H start rowBase : Nat) :
    affineExactlyOneStructuredRowFrames (labelCount tm + 1) (stateCount tm)
        (verifierOneHotCellCounts tm) H start rowBase =
      arithmeticRawOneHotFrames tm H start rowBase := by
  rw [← arithmeticStructuredOneHotFrames_eq_raw]
  unfold affineExactlyOneStructuredRowFrames
    arithmeticStructuredOneHotFrames
  rw [arithmeticOneHotPrefixFrames_eq_explicit]
  simp only [affineExactlyOnePrefixFrames, verifierOneHotCellCounts]
  congr 1
  by_cases hzero : @Fintype.card tm.K tm.kFin = 0
  · simp [hzero, affineExactlyOneStackFamilyFrames]
  · obtain ⟨n, hcard⟩ : ∃ n,
        @Fintype.card tm.K tm.kFin = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero hzero
    have hpositive : 0 < @Fintype.card tm.K tm.kFin := by omega
    have hfamily := affineExactlyOneStackFamilyFrames_fromArithmetic
      tm H start rowBase n 0 (by omega)
    rw [arithmeticFirstStackHeight_start tm H start rowBase hpositive,
      arithmeticFirstStackHeight_rowBase tm H start rowBase hpositive]
      at hfamily
    convert hfamily using 1
    · congr 1
      rw [List.ofFn_congr hcard]
      apply List.ofFn_inj.mpr
      funext position
      have hposition : Fin.cast hcard.symm position =
          (⟨0 + position.val, by omega⟩ :
            Fin (@Fintype.card tm.K tm.kFin)) := by
        apply Fin.ext
        simp only [Fin.val_cast, Nat.zero_add]
      rw [hposition]
    · apply congrArg List.flatten
      rw [List.ofFn_congr hcard]
      apply List.ofFn_inj.mpr
      funext position
      have hposition : Fin.cast hcard.symm position =
          (⟨0 + position.val, by omega⟩ :
            Fin (@Fintype.card tm.K tm.kFin)) := by
        apply Fin.ext
        simp only [Fin.val_cast, Nat.zero_add]
      rw [hposition]

/-! ## Row-seed and row-family contracts -/

/-- One seed expanded only to its ordered one-hot runtime frames. -/
noncomputable def validityRowSeedOneHotFrames
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    List AffineExactlyOneFrame :=
  arithmeticRawOneHotFrames tm seed.height seed.start seed.rowBase

/-- The one-hot seed expansion is exactly the one-hot field of the complete
canonical validity-row expansion. -/
theorem validityRowSeedOneHotFrames_eq_expand
    (tm : _root_.Turing.FinTM2) (seed : ValidityRowSeed) :
    validityRowSeedOneHotFrames tm seed =
      (expandValidityRowSeed tm seed).oneHotFrames := by
  rfl

/-- Row-major one-hot frames generated from every compiled validity seed. -/
noncomputable def validityRowSeedOneHotFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineExactlyOneFrame :=
  (verifierValidityRowSeeds W input).flatMap
    (validityRowSeedOneHotFrames W.machine.tm)

/-- Seed expansion gives byte-for-byte the canonical row-major one-hot frame
family consumed by the validity-row controller. -/
theorem validityRowSeedOneHotFamily_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    validityRowSeedOneHotFamily W input =
      (verifierValidityRowFramesByLength W input.length).flatMap
        (fun frame => frame.oneHotFrames) := by
  unfold validityRowSeedOneHotFamily
  rw [← verifierValidityRowSeeds_expand_eq_frames]
  rw [List.flatMap_map]
  congr 1

/-! ## Concrete fixed source over the compiled row seeds -/

/-- Reinterpret the Cook--Levin seed stream as the verifier-independent
runtime interface of the fixed structured-row family controller. -/
def verifierValidityRowStructuredSeeds
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List AffineExactlyOneStructuredRowSeed :=
  (verifierValidityRowSeeds W input).map fun seed =>
    { height := seed.height
      start := seed.start
      rowBase := seed.rowBase }

/-- The generic row-family controller consumes exactly the byte stream emitted
by the established raw-input validity-seed generator. -/
theorem verifierValidityRowStructuredSeedEncoding_eq
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    encodeAffineExactlyOneStructuredRowSeedFamily
        (verifierValidityRowStructuredSeeds W input) =
      verifierValidityRowSeedFrames W input := by
  rw [verifierValidityRowSeedFrames_eq_seeds]
  unfold verifierValidityRowStructuredSeeds
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneStructuredRowSeedFamily,
        encodeAffineExactlyOneStructuredRowSeed, ih]

/-- At the verifier's fixed widths, the generic controller's complete output
frame list is exactly the semantic Cook--Levin one-hot family. -/
theorem verifierValidityRowStructuredFrames_eq_oneHotFamily
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    affineExactlyOneStructuredRowFamilyFrames
        (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
        (verifierOneHotCellCounts W.machine.tm)
        (verifierValidityRowStructuredSeeds W input) =
      validityRowSeedOneHotFamily W input := by
  unfold verifierValidityRowStructuredSeeds validityRowSeedOneHotFamily
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [affineExactlyOneStructuredRowFamilyFrames, ih,
        validityRowSeedOneHotFrames,
        affineExactlyOneStructuredRowFrames_eq_arithmeticRaw]

/-- Fixed controller specialized only by the verifier machine's finite label,
state, stack, and reachable-alphabet widths.  All row values remain tape data.
-/
noncomputable def verifierValidityRowOneHotSourceProgram
    (tm : _root_.Turing.FinTM2) : Program UnaryFrameSym UnaryFrameSym :=
  affineExactlyOneStructuredRowFamilyRevProgram
    (labelCount tm + 1) (stateCount tm) (verifierOneHotCellCounts tm)

/-- Exact runtime of the verifier-specialized fixed row-family source. -/
noncomputable def verifierValidityRowOneHotSourceSteps
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : Nat :=
  affineExactlyOneStructuredRowFamilyRevSteps
    (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
    (verifierOneHotCellCounts W.machine.tm)
    (verifierValidityRowStructuredSeeds W input)

/-- From the concrete compiled seed bytes, one fixed verifier-dependent
controller emits every row's canonical compact one-hot operands and halts with
all input, work stacks, and counters cleared. -/
noncomputable def verifierValidityRowOneHotSource_run
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    EvalsToInTime
      (step (verifierValidityRowOneHotSourceProgram W.machine.tm))
      (initialCfg (verifierValidityRowOneHotSourceProgram W.machine.tm)
        (verifierValidityRowSeedFrames W input))
      (some (haltCfg
        (verifierValidityRowOneHotSourceProgram W.machine.tm)
        ((encodeAffineExactlyOneCompactFamily
          (validityRowSeedOneHotFamily W input)).reverse)))
      (verifierValidityRowOneHotSourceSteps W input) := by
  have sourceRun := affineExactlyOneStructuredRowFamilyRev_run
    (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
    (verifierOneHotCellCounts W.machine.tm)
    (verifierValidityRowStructuredSeeds W input)
  rw [verifierValidityRowStructuredSeedEncoding_eq W input] at sourceRun
  rw [verifierValidityRowStructuredFrames_eq_oneHotFamily W input]
    at sourceRun
  simpa [verifierValidityRowOneHotSourceProgram,
    verifierValidityRowOneHotSourceSteps] using sourceRun

/-! ## Polynomial-time closure from the raw verifier input -/

/-- Repackage the established raw-input seed compiler with the semantic seed
list as its output.  The byte stream is unchanged; the preceding encoding
identity theorem supplies the interface needed by the structured-row source.
-/
noncomputable def
    verifierValidityRowStructuredSeeds_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineExactlyOneStructuredRowSeedFamily
      (verifierValidityRowStructuredSeeds W) := by
  let source := verifierValidityRowSeedFrames_computableInPolyTime W
  exact
    { tm := source.tm
      inputAlphabet := source.inputAlphabet
      outputAlphabet := source.outputAlphabet
      time := source.time
      outputsFun := fun input => by
        simpa only [id_eq,
          verifierValidityRowStructuredSeedEncoding_eq W input] using
          source.outputsFun input }

/-- One fixed verifier-dependent polynomial-time TM2 maps the raw word to
the complete compact one-hot frame family for every validity row. -/
noncomputable def
    verifierValidityRowOneHotCompactFamily_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id
      encodeAffineExactlyOneCompactFamily
      (validityRowSeedOneHotFamily W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierValidityRowStructuredSeeds_computableInPolyTime W)
      (affineExactlyOneStructuredRowFamilyFrames_computableInPolyTime
        (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
        (verifierOneHotCellCounts W.machine.tm))
  simpa [Function.comp_def,
    verifierValidityRowStructuredFrames_eq_oneHotFamily] using
    Classical.choice composed

/-- Raw-input polynomial-time construction of the canonical four-field
one-hot operands used by every Cook--Levin validity row.  The result is stated
directly against the canonical row-major verifier frame family, not merely
against an auxiliary seed representation. -/
noncomputable def verifierValidityRowOneHotOperands_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime (id : List Γ → List Γ) id
      (fun input : List Γ => encodeAffineExactlyOneFamily
        ((verifierValidityRowFramesByLength W input.length).flatMap
          (fun frame => frame.oneHotFrames))) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierValidityRowOneHotCompactFamily_computableInPolyTime W)
      affineExactlyOneFrameExpand_computableInPolyTime
  simpa [Function.comp_def, validityRowSeedOneHotFamily_eq_canonical] using
    Classical.choice composed

/-! ## Row-delimited final-conjunction invocations -/

/-- For every validity row, project the structured one-hot frames to the
compact `(start, count, 0)` invocations that compute the corresponding output
wires.  A `frameEnd` after each row preserves the boundary needed by the
validity-tail assembler. -/
noncomputable def verifierValidityRowOneHotOutputInvocationFrames
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) : List UnaryFrameSym :=
  encodeAffineExactlyOneStructuredRowOutputInvocationFamily
    (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
    (verifierOneHotCellCounts W.machine.tm)
    (verifierValidityRowStructuredSeeds W input)

/-- The projected stream is exactly the canonical reversed one-hot frame
family for each row, with row boundaries retained byte-for-byte. -/
theorem verifierValidityRowOneHotOutputInvocationFrames_eq_canonical
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L)
    (input : List Γ) :
    verifierValidityRowOneHotOutputInvocationFrames W input =
      (verifierValidityRowFramesByLength W input.length).flatMap fun frame =>
        encodeAffineExactlyOneOutputSourceInvocationFamily
            frame.oneHotFrames.reverse ++
          [.frameEnd] := by
  rw [← verifierValidityRowSeeds_expand_eq_frames W input]
  unfold verifierValidityRowOneHotOutputInvocationFrames
    verifierValidityRowStructuredSeeds
  generalize verifierValidityRowSeeds W input = seeds
  induction seeds with
  | nil => rfl
  | cons seed rest ih =>
      simp [encodeAffineExactlyOneStructuredRowOutputInvocationFamily,
        encodeAffineExactlyOneStructuredRowOutputInvocation, ih,
        expandValidityRowSeed,
        affineExactlyOneStructuredRowFrames_eq_arithmeticRaw]
      unfold arithmeticValidityRowFrame
      rfl

/-- A fixed verifier-dependent polynomial-time TM2 maps the raw verifier word
directly to the row-delimited one-hot output invocation stream. -/
noncomputable def
    verifierValidityRowOneHotOutputInvocationFrames_computableInPolyTime
    {Γ : Type} {L : Language Γ} (W : VerifierWitness L) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (verifierValidityRowOneHotOutputInvocationFrames W) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (verifierValidityRowStructuredSeeds_computableInPolyTime W)
      (affineExactlyOneStructuredRowOutputInvocationFamily_computableInPolyTime
        (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
        (verifierOneHotCellCounts W.machine.tm))
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      encodeAffineExactlyOneStructuredRowOutputInvocationFamily
        (labelCount W.machine.tm + 1) (stateCount W.machine.tm)
        (verifierOneHotCellCounts W.machine.tm)
        (verifierValidityRowStructuredSeeds W input))
  simpa [Function.comp_def] using Classical.choice composed

end CLRS.Chapter34.Turing.CookLevin
