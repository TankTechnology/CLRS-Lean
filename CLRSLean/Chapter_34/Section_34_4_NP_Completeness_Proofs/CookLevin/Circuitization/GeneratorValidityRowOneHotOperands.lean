import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.CookLevin.Circuitization.GeneratorValidityRowSeeds
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneRowFamilySource
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.AffineExactlyOneStackSource

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

end CLRS.Chapter34.Turing.CookLevin
