import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.UnaryFrameLengthPrefixedFourWaySplitSectionBlockSimulation

/-!
# Counter-delimited payload channels of the four-way splitter

This file lifts the one-block scanner to a complete dynamically sized channel.
The same theorem covers coordinates, true-arm fields, and false-arm fields by
placing the active unary counter in the appropriate counter stack.
-/

noncomputable section

open StateTransition

namespace CLRS.Chapter34.Turing.PolyBuilder

private abbrev splitStep :=
  step unaryFrameLengthPrefixedFourWaySplitRevProgram

/-- Put the active field count in the counter selected by `channel`. -/
def unaryFrameLengthPrefixedFourWaySplitSectionCfg
    (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
    (label : UnaryFrameLengthPrefixedFourWaySplitLabel)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (input output : List UnaryFrameSym)
    (active other₁ other₂ : Nat) :
    BuilderCfg unaryFrameLengthPrefixedFourWaySplitRevProgram :=
  match channel with
  | .coordinates => unaryFrameLengthPrefixedFourWaySplitCfg label buffer₁ buffer₂
      test input output active other₁ other₂
  | .trueArm => unaryFrameLengthPrefixedFourWaySplitCfg label buffer₁ buffer₂
      test input output other₁ active other₂
  | .falseArm => unaryFrameLengthPrefixedFourWaySplitCfg label buffer₁ buffer₂
      test input output other₁ other₂ active

/-- The scanner's final buffer is unchanged for an empty channel and contains
the last separator otherwise. -/
def unaryFrameLengthPrefixedFourWaySplitFinalBuffer
    (initial : Option UnaryFrameSym) : List Nat → Option UnaryFrameSym
  | [] => initial
  | _ :: _ => some .separator

@[simp] theorem unaryFrameLengthPrefixedFourWaySplitFinalBuffer_separator
    (values : List Nat) :
    unaryFrameLengthPrefixedFourWaySplitFinalBuffer
      (some UnaryFrameSym.separator) values = some UnaryFrameSym.separator := by
  cases values <;> rfl

/-- Exact builder-step count for one complete payload channel. -/
def unaryFrameLengthPrefixedFourWaySplitSectionSteps
    (values : List Nat) : Nat :=
  values.length + 2 * (encodeUnaryFrame values).length + 2

/-- A counter-delimited channel copies exactly its declared number of fields,
emits one row boundary, and transfers control to the next channel. -/
def unaryFrameLengthPrefixedFourWaySplit_section
    (channel : UnaryFrameLengthPrefixedFourWaySplitSection)
    (values : List Nat) (other₁ other₂ : Nat)
    (buffer₁ buffer₂ : Option UnaryFrameSym) (test : Bool)
    (tail output : List UnaryFrameSym) :
    EvalsToInTime splitStep
      (unaryFrameLengthPrefixedFourWaySplitSectionCfg channel
        (.sectionCheck channel) buffer₁ buffer₂ test
        (encodeUnaryFrame values ++ tail) output values.length other₁ other₂)
      (some (unaryFrameLengthPrefixedFourWaySplitSectionCfg channel
        (unaryFrameLengthPrefixedFourWaySplitNext channel)
        (unaryFrameLengthPrefixedFourWaySplitFinalBuffer buffer₁ values)
        buffer₂ false tail
        ((encodeUnaryFrame values ++ [UnaryFrameSym.frameEnd]).reverse ++ output)
        0 other₁ other₂))
      (unaryFrameLengthPrefixedFourWaySplitSectionSteps values) := by
  induction values generalizing buffer₁ test output with
  | nil =>
      cases channel <;> exact ⟨⟨2, rfl⟩, le_rfl⟩
  | cons value values ih =>
      let afterCheck := unaryFrameLengthPrefixedFourWaySplitSectionCfg channel
        (.sectionScan channel) buffer₁ buffer₂ true
        (encodeUnaryFrameBlock value ++ encodeUnaryFrame values ++ tail) output
        values.length other₁ other₂
      have hcheck : EvalsToInTime splitStep
          (unaryFrameLengthPrefixedFourWaySplitSectionCfg channel
            (.sectionCheck channel) buffer₁ buffer₂ test
            (encodeUnaryFrame (value :: values) ++ tail) output
            (value :: values).length other₁ other₂)
          (some afterCheck) 1 := by
        cases channel <;> exact ⟨⟨1, rfl⟩, le_rfl⟩
      have hblock : EvalsToInTime splitStep afterCheck
          (some (unaryFrameLengthPrefixedFourWaySplitSectionCfg channel
            (.sectionCheck channel) (some .separator) buffer₂ true
            (encodeUnaryFrame values ++ tail)
            ((encodeUnaryFrameBlock value).reverse ++ output)
            values.length other₁ other₂))
          (2 * (value + 1)) := by
        cases channel <;>
          simpa [afterCheck, unaryFrameLengthPrefixedFourWaySplitSectionCfg,
            List.append_assoc] using
            (unaryFrameLengthPrefixedFourWaySplit_sectionBlock
              _ value _ _ _ buffer₁ buffer₂ true
              (encodeUnaryFrame values ++ tail) output)
      have hfirst := EvalsToInTime.trans splitStep 1 (2 * (value + 1))
        _ afterCheck _ hcheck hblock
      have hrest := ih (buffer₁ := some UnaryFrameSym.separator)
        (test := true)
        (output := (encodeUnaryFrameBlock value).reverse ++ output)
      let full := EvalsToInTime.trans splitStep (2 * (value + 1) + 1)
        (unaryFrameLengthPrefixedFourWaySplitSectionSteps values)
        _ _ _ hfirst hrest
      convert full using 1
      · cases values <;>
          simp [unaryFrameLengthPrefixedFourWaySplitFinalBuffer,
          encodeUnaryFrame, List.reverse_append, List.append_assoc]
      · simp [unaryFrameLengthPrefixedFourWaySplitSectionSteps,
          encodeUnaryFrame, encodeUnaryFrameBlock]
        omega

end CLRS.Chapter34.Turing.PolyBuilder
