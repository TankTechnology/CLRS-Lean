import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameMarkedRowParallelInterleaveRows

/-!
# Family-level parallel marked-row interleaving

The two local row-transfer theorems are lifted here to aligned row families.
The result is an exact run which consumes both physical output stacks and
places the reverse of the semantic interleaving on the merger scratch stack.
-/

noncomputable section

open Computability StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

/-- Raw `frameEnd`-delimited stream represented by a list of rows. -/
def encodeUnaryFrameMarkedRows (rows : List (List UnaryFrameSym)) :
    List UnaryFrameSym :=
  rows.flatMap fun row => row ++ [.frameEnd]

@[simp] theorem encodeUnaryFrameMarkedRows_nil :
    encodeUnaryFrameMarkedRows [] = [] := rfl

@[simp] theorem encodeUnaryFrameMarkedRows_cons
    (row : List UnaryFrameSym) (rows : List (List UnaryFrameSym)) :
    encodeUnaryFrameMarkedRows (row :: rows) =
      row ++ .frameEnd :: encodeUnaryFrameMarkedRows rows := by
  simp [encodeUnaryFrameMarkedRows]

namespace UnaryFrameMarkedRowParallelInterleave

variable {Γ : Type} [Fintype Γ] [Inhabited Γ]
variable {leftFamily rightFamily : List Γ → UnaryFrameMarkedRowFamily}
variable
  (M₁ : _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily leftFamily)
  (M₂ : _root_.Turing.TM2ComputableInPolyTime id
    encodeUnaryFrameMarkedRowFamily rightFamily)

/-- The control state after processing all rows.  An empty family performs no
step; every nonempty aligned family ends immediately after a right boundary.
-/
def mergeRowsFinalState (startState : ExtraState Γ) :
    List (List UnaryFrameSym) → ExtraState Γ
  | [] => startState
  | _ :: _ => ExtraState.mergeSymbol UnaryFrameSym.frameEnd

/-- Exact number of symbol-transfer steps before the final empty-stack probe.
-/
def mergeAlignedRowsSteps
    (left right : List (List UnaryFrameSym)) : Nat :=
  (encodeUnaryFrameMarkedRows left).length +
    (encodeUnaryFrameMarkedRows right).length

/-- Aligned delimiter-free row families are physically consumed in alternating
order.  Both source stacks become empty and the scratch contains the reverse
of the semantic interleaving followed by its previous contents. -/
def merge_aligned_rows_run
    (left right : List (List UnaryFrameSym))
    (haligned : left.length = right.length)
    (hleftFree : ∀ row ∈ left, ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd)
    (hrightFree : ∀ row ∈ right, ∀ symbol ∈ row,
      symbol ≠ UnaryFrameSym.frameEnd)
    {values : ∀ k : K M₁ M₂, List (StackAlphabet M₁ M₂ k)}
    {temp : List UnaryFrameSym} (state : ExtraState Γ)
    (hleft : values (firstOutputK M₁ M₂) =
      List.map M₁.outputAlphabet.invFun
        (encodeUnaryFrameMarkedRows left))
    (hright : values (outputK M₁ M₂) =
      List.map M₂.outputAlphabet.invFun
        (encodeUnaryFrameMarkedRows right))
    (htemp : values (outputTempK M₁ M₂) = temp) :
    EvalsToInTime (machine M₁ M₂).step
      (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)
      (some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft
        (mergeRowsFinalState state left)
        (Function.update
          (Function.update
            (Function.update values (firstOutputK M₁ M₂) [])
            (outputK M₁ M₂) [])
          (outputTempK M₁ M₂)
            ((encodeUnaryFrameMarkedRows
              (interleaveUnaryFrameMarkedRows left right)).reverse ++ temp))))
      (mergeAlignedRowsSteps left right) := by
  induction left generalizing right values temp state with
  | nil =>
      have hrightNil : right = [] :=
        List.eq_nil_of_length_eq_zero haligned.symm
      subst right
      have hcollapse :
          Function.update
              (Function.update
                (Function.update values (firstOutputK M₁ M₂) [])
                (outputK M₁ M₂) [])
              (outputTempK M₁ M₂) temp = values := by
        funext key
        by_cases h₁ : key = firstOutputK M₁ M₂
        · subst key
          simp [Function.update, hleft]
        · by_cases h₂ : key = outputK M₁ M₂
          · subst key
            simp [Function.update, hright]
          · by_cases h₃ : key = outputTempK M₁ M₂
            · subst key
              simp [Function.update, htemp]
            · simp [Function.update, h₁, h₂, h₃]
      refine ⟨⟨0, ?_⟩, le_rfl⟩
      change some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values) =
        some (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state
          (Function.update
            (Function.update
              (Function.update values (firstOutputK M₁ M₂) [])
              (outputK M₁ M₂) [])
            (outputTempK M₁ M₂) temp))
      exact congrArg
        (fun stackValues => some
          (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state stackValues))
        hcollapse.symm
  | cons leftRow leftRows ih =>
      cases right with
      | nil => simp at haligned
      | cons rightRow rightRows =>
          have htailAligned : leftRows.length = rightRows.length := by
            simpa using Nat.succ.inj haligned
          have hleftRowFree : ∀ symbol ∈ leftRow,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro symbol hsymbol
            exact hleftFree leftRow (by simp) symbol hsymbol
          have hrightRowFree : ∀ symbol ∈ rightRow,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro symbol hsymbol
            exact hrightFree rightRow (by simp) symbol hsymbol
          have hleftRowsFree : ∀ row ∈ leftRows, ∀ symbol ∈ row,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro row hrow symbol hsymbol
            exact hleftFree row (by simp [hrow]) symbol hsymbol
          have hrightRowsFree : ∀ row ∈ rightRows, ∀ symbol ∈ row,
              symbol ≠ UnaryFrameSym.frameEnd := by
            intro row hrow symbol hsymbol
            exact hrightFree row (by simp [hrow]) symbol hsymbol
          let leftBlock := leftRow ++ [UnaryFrameSym.frameEnd]
          let rightBlock := rightRow ++ [UnaryFrameSym.frameEnd]
          let leftTail := encodeUnaryFrameMarkedRows leftRows
          let rightTail := encodeUnaryFrameMarkedRows rightRows
          let valuesLeft := Function.update
            (Function.update values (firstOutputK M₁ M₂)
              (List.map M₁.outputAlphabet.invFun leftTail))
            (outputTempK M₁ M₂) (leftBlock.reverse ++ temp)
          let valuesRight := Function.update
            (Function.update valuesLeft (outputK M₁ M₂)
              (List.map M₂.outputAlphabet.invFun rightTail))
            (outputTempK M₁ M₂)
              (rightBlock.reverse ++ leftBlock.reverse ++ temp)
          let afterLeft := mergeCfg M₁ M₂ ExtraΛ.mergeRight
            (ExtraState.mergeSymbol UnaryFrameSym.frameEnd) valuesLeft
          let afterRight := mergeCfg M₁ M₂ ExtraΛ.mergeLeft
            (ExtraState.mergeSymbol UnaryFrameSym.frameEnd) valuesRight
          have hleftSource : values (firstOutputK M₁ M₂) =
              List.map M₁.outputAlphabet.invFun
                (leftRow ++ UnaryFrameSym.frameEnd :: leftTail) := by
            simpa [leftTail] using hleft
          have hleftIt : EvalsToInTime (machine M₁ M₂).step
              (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)
              (some afterLeft) (leftRow.length + 1) :=
            ⟨⟨leftRow.length + 1, by
              simpa [afterLeft, valuesLeft, leftBlock] using
                merge_left_row_phase M₁ M₂ state hleftRowFree hleftSource
                  htemp⟩, le_rfl⟩
          have hrightSource : valuesLeft (outputK M₁ M₂) =
              List.map M₂.outputAlphabet.invFun
                (rightRow ++ UnaryFrameSym.frameEnd :: rightTail) := by
            simp [valuesLeft, rightTail, Function.update, hright]
          have hleftTemp : valuesLeft (outputTempK M₁ M₂) =
              leftBlock.reverse ++ temp := by
            simp [valuesLeft]
          have hrightIt : EvalsToInTime (machine M₁ M₂).step
              afterLeft (some afterRight) (rightRow.length + 1) :=
            ⟨⟨rightRow.length + 1, by
              simpa [afterLeft, afterRight, valuesRight,
                rightBlock] using
                merge_right_row_phase M₁ M₂
                  (ExtraState.mergeSymbol UnaryFrameSym.frameEnd)
                  hrightRowFree hrightSource hleftTemp⟩, le_rfl⟩
          have hleftTail : valuesRight (firstOutputK M₁ M₂) =
              List.map M₁.outputAlphabet.invFun leftTail := by
            simp [valuesRight, valuesLeft, Function.update]
          have hrightTail : valuesRight (outputK M₁ M₂) =
              List.map M₂.outputAlphabet.invFun rightTail := by
            simp [valuesRight, Function.update]
          have hrightTemp : valuesRight (outputTempK M₁ M₂) =
              rightBlock.reverse ++ leftBlock.reverse ++ temp := by
            simp [valuesRight]
          have hrest := ih rightRows htailAligned hleftRowsFree hrightRowsFree
            (state := ExtraState.mergeSymbol UnaryFrameSym.frameEnd)
            (values := valuesRight)
            (temp := rightBlock.reverse ++ leftBlock.reverse ++ temp)
            hleftTail hrightTail hrightTemp
          let firstTwo := EvalsToInTime.trans (machine M₁ M₂).step
            (leftRow.length + 1) (rightRow.length + 1)
            (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)
            afterLeft (some afterRight) hleftIt hrightIt
          let full := EvalsToInTime.trans (machine M₁ M₂).step
            ((rightRow.length + 1) + (leftRow.length + 1))
            (mergeAlignedRowsSteps leftRows rightRows)
            (mergeCfg M₁ M₂ ExtraΛ.mergeLeft state values)
            afterRight _ firstTwo hrest
          have hstate : mergeRowsFinalState (Γ := Γ)
              (ExtraState.mergeSymbol (Γ := Γ) UnaryFrameSym.frameEnd)
                leftRows =
              ExtraState.mergeSymbol (Γ := Γ)
                UnaryFrameSym.frameEnd := by
            cases leftRows <;> rfl
          have hcollapse :
              Function.update
                  (Function.update
                    (Function.update valuesRight (firstOutputK M₁ M₂) [])
                    (outputK M₁ M₂) [])
                  (outputTempK M₁ M₂)
                    ((encodeUnaryFrameMarkedRows
                      (interleaveUnaryFrameMarkedRows leftRows rightRows)).reverse ++
                        (rightBlock.reverse ++ leftBlock.reverse ++ temp)) =
                Function.update
                  (Function.update
                    (Function.update values (firstOutputK M₁ M₂) [])
                    (outputK M₁ M₂) [])
                  (outputTempK M₁ M₂)
                    ((encodeUnaryFrameMarkedRows
                      (interleaveUnaryFrameMarkedRows
                        (leftRow :: leftRows) (rightRow :: rightRows))).reverse ++
                      temp) := by
            funext key
            by_cases h₁ : key = firstOutputK M₁ M₂ <;>
              by_cases h₂ : key = outputK M₁ M₂ <;>
                by_cases h₃ : key = outputTempK M₁ M₂ <;>
                  simp [valuesRight, valuesLeft, Function.update, h₁, h₂, h₃,
                    leftBlock, rightBlock, encodeUnaryFrameMarkedRows,
                    interleaveUnaryFrameMarkedRows, List.reverse_append,
                    List.append_assoc]
          have hsteps : mergeAlignedRowsSteps leftRows rightRows +
                ((rightRow.length + 1) + (leftRow.length + 1)) =
              mergeAlignedRowsSteps (leftRow :: leftRows)
                (rightRow :: rightRows) := by
            simp [mergeAlignedRowsSteps, encodeUnaryFrameMarkedRows]
            omega
          rw [hstate, hcollapse] at full
          simpa only [mergeRowsFinalState, hsteps] using full

end UnaryFrameMarkedRowParallelInterleave

end CLRS.Chapter34.Turing.PolyBuilder
