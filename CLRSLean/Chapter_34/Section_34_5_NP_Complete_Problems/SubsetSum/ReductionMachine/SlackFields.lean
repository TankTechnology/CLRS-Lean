import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.SlackSemantics
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.DropHead
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.Reverse

/-!
# Fixed-machine generation of all SUBSET-SUM slack fields

The runtime affine progression supplies the number of trailing zeroes in each
slack value.  A fixed local formatter turns every unary value into one compact
binary field, and a fixed two-symbol suffix trim removes the formatter's
terminal continuation marker.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder
open _root_.CLRS.Chapter34.SubsetSumReduction

/-- Delete exactly the last two symbols, or the whole word if it is shorter. -/
def trimTrailingTwo {α : Type} (input : List α) : List α :=
  (DropHead.stream (DropHead.stream input.reverse)).reverse

theorem trimTrailingTwo_append {α : Type}
    (leading : List α) (first second : α) :
    trimTrailingTwo (leading ++ [first, second]) = leading := by
  simp [trimTrailingTwo, DropHead.stream, List.reverse_append]

noncomputable def trimTrailingTwo_computableInPolyTime
    (α : Type) [Fintype α] :
    _root_.Turing.TM2ComputableInPolyTime id id
      (@trimTrailingTwo α) := by
  let reversed := reverse_computableInPolyTime (Γ := α)
  let dropOnce := DropHead.computableInPolyTime α
  let first := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    reversed dropOnce
  let second := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice first) dropOnce
  let restored := _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
    (Classical.choice second) reversed
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input : List α =>
      (DropHead.stream (DropHead.stream input.reverse)).reverse)
  simpa [Function.comp_def] using Classical.choice restored

/-- Translate one affine unary frame family into consecutive fields.  An
ordinary separator closes the current field and opens the next one. -/
def slackFieldBody : LoopBody UnaryFrameSym SubsetSumSym where
  emit
    | .tick => [.bit false]
    | .separator => [.fieldEnd, .numberMark, .bit true]
    | .frameEnd => []
  cost _ := 3
  emit_length_le_cost symbol := by
    cases symbol <;> decide

private theorem flatMap_replicate_false (count : Nat) :
    (List.replicate count UnaryFrameSym.tick).flatMap slackFieldBody.emit =
      List.replicate count (TSPSym.bit false) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.flatMap_cons]
      change [TSPSym.bit false] ++
        (List.replicate count UnaryFrameSym.tick).flatMap
          slackFieldBody.emit = _
      rw [ih]
      rfl

private theorem flatMap_encodeBlock (value : Nat) :
    (encodeUnaryFrameBlock value).flatMap slackFieldBody.emit =
      List.replicate value (TSPSym.bit false) ++
        [.fieldEnd, .numberMark, .bit true] := by
  rw [encodeUnaryFrameBlock, List.flatMap_append,
    flatMap_replicate_false]
  rfl

/-- The continuation-style formatter equals the direct compact-field list,
followed by one unused next-field prefix. -/
theorem rawSlackFields_eq (values : List Nat) :
    [.numberMark, .bit true] ++
        (encodeUnaryFrame values).flatMap slackFieldBody.emit =
      values.flatMap (fun value =>
        encodeCanonicalBitField (true :: List.replicate value false)) ++
        [.numberMark, .bit true] := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      rw [encodeUnaryFrame]
      simp only [List.flatMap_cons, List.flatMap_append]
      rw [flatMap_encodeBlock]
      have ih' : [.numberMark, .bit true] ++
          (List.flatMap encodeUnaryFrameBlock values).flatMap
            slackFieldBody.emit =
          values.flatMap (fun value =>
            encodeCanonicalBitField (true :: List.replicate value false)) ++
            [.numberMark, .bit true] := by
        simpa [encodeUnaryFrame] using ih
      calc
        [.numberMark, .bit true] ++
              (List.replicate value (.bit false) ++
                [.fieldEnd, .numberMark, .bit true] ++
                  (List.flatMap encodeUnaryFrameBlock values).flatMap
                    slackFieldBody.emit) =
            encodeCanonicalBitField
                (true :: List.replicate value false) ++
              ([.numberMark, .bit true] ++
                (List.flatMap encodeUnaryFrameBlock values).flatMap
                  slackFieldBody.emit) := by
            simp [encodeCanonicalBitField, List.append_assoc]
        _ = encodeCanonicalBitField
                (true :: List.replicate value false) ++
              (values.flatMap (fun value =>
                encodeCanonicalBitField
                  (true :: List.replicate value false)) ++
                [.numberMark, .bit true]) := by rw [ih']
        _ = _ := by simp [List.append_assoc]

def slackZeroCountFrames (input : List CNFSym) : List UnaryFrameSym :=
  affineUnaryProgressionFrameStream (slackProgression input)

theorem slackProgressionValues_eq (input : List CNFSym) :
    affineUnaryProgressionValues (slackProgression input) =
      (List.range (decodeCNF input).length).map fun clause =>
        reductionBlockWidth (decodeCNF input) *
          (reductionVariableCount (decodeCNF input) + clause) := by
  rw [affineUnaryProgressionValues,
    affineUnaryProgressionValuesFrom_eq_ofFn]
  apply List.ext_get
  · simp [slackProgression]
  · intro index hleft hright
    simp only [List.length_ofFn, List.length_map,
      List.length_range] at hleft hright
    simp [slackProgression]
    ring

noncomputable def slackZeroCountFrames_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackZeroCountFrames := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      slackProgressionSource_computableInPolyTime
      affineUnaryProgressionFrameStream_computableInPolyTime
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => affineUnaryProgressionFrameStream (slackProgression input))
  simpa [Function.comp_def] using Classical.choice composed

def rawSlackFieldStream (input : List CNFSym) : List SubsetSumSym :=
  [.numberMark, .bit true] ++
    (slackZeroCountFrames input).flatMap slackFieldBody.emit

/-- One complete clause-indexed family of slack fields. -/
def slackOneSlotFields (input : List CNFSym) : List SubsetSumSym :=
  trimTrailingTwo (rawSlackFieldStream input)

theorem slackOneSlotFields_eq_counts (input : List CNFSym) :
    slackOneSlotFields input =
      (affineUnaryProgressionValues (slackProgression input)).flatMap
        (fun value => encodeCanonicalBitField
          (true :: List.replicate value false)) := by
  rw [slackOneSlotFields, rawSlackFieldStream, slackZeroCountFrames,
    affineUnaryProgressionFrameStream, rawSlackFields_eq,
    trimTrailingTwo_append]

/-- On a three-CNF source, the generated family is exactly any one of the
three equal-valued slack-slot families in the public item order. -/
theorem slackOneSlotFields_eq_items (input : List CNFSym)
    (hthree : IsThreeCNF (decodeCNF input)) (slot : Nat) :
    slackOneSlotFields input =
      (List.range (decodeCNF input).length).flatMap fun clause =>
        encodeCanonicalBitField
          (reductionItemBits (decodeCNF input) (.slack clause slot)) := by
  rw [slackOneSlotFields_eq_counts, slackProgressionValues_eq,
    List.flatMap_map]
  apply List.flatMap_congr
  intro clause hclause
  rw [reductionItemBits_slack_eq hthree (List.mem_range.mp hclause)]

private noncomputable def formattedSlackFrames_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym =>
        (slackZeroCountFrames input).flatMap slackFieldBody.emit) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      slackZeroCountFrames_computableInPolyTime
      (boundedLoop_computableInPolyTime slackFieldBody)
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def rawSlackFieldStream_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id rawSlackFieldStream := by
  let joined := fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    (constantSubsetSumWord_computableInPolyTime [.numberMark, .bit true])
    formattedSlackFrames_computableInPolyTime
  exact
    { tm := joined.tm
      inputAlphabet := joined.inputAlphabet
      outputAlphabet := joined.outputAlphabet
      time := joined.time
      outputsFun := fun input => by
        have output := joined.outputsFun input
        rw [constantSubsetSumWord_eq] at output
        simpa [rawSlackFieldStream] using output }

/-- A fixed polynomial-time TM2 generates one complete slack-slot family. -/
noncomputable def slackOneSlotFields_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackOneSlotFields := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      rawSlackFieldStream_computableInPolyTime
      (trimTrailingTwo_computableInPolyTime SubsetSumSym)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input => trimTrailingTwo (rawSlackFieldStream input))
  simpa [Function.comp_def] using Classical.choice composed

/-- All three slack-slot families, in the public reduction order. -/
def slackFields (input : List CNFSym) : List SubsetSumSym :=
  slackOneSlotFields input ++ slackOneSlotFields input ++
    slackOneSlotFields input

theorem slackFields_eq_items (input : List CNFSym)
    (hthree : IsThreeCNF (decodeCNF input)) :
    slackFields input =
      (List.range (decodeCNF input).length).flatMap (fun clause =>
        encodeCanonicalBitField
          (reductionItemBits (decodeCNF input) (.slack clause 0))) ++
      (List.range (decodeCNF input).length).flatMap (fun clause =>
        encodeCanonicalBitField
          (reductionItemBits (decodeCNF input) (.slack clause 1))) ++
      (List.range (decodeCNF input).length).flatMap (fun clause =>
        encodeCanonicalBitField
          (reductionItemBits (decodeCNF input) (.slack clause 2))) := by
  unfold slackFields
  exact congrArg₂ (· ++ ·)
    (congrArg₂ (· ++ ·)
      (slackOneSlotFields_eq_items input hthree 0)
      (slackOneSlotFields_eq_items input hthree 1))
    (slackOneSlotFields_eq_items input hthree 2)

private noncomputable def slackFieldsPrefix_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id
      (fun input : List CNFSym =>
        slackOneSlotFields input ++ slackOneSlotFields input) :=
  fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    slackOneSlotFields_computableInPolyTime
    slackOneSlotFields_computableInPolyTime

/-- A fixed polynomial-time TM2 emits all three ordered slack families. -/
noncomputable def slackFields_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id slackFields :=
  fixedPairSameInputConcat_computableInPolyTime
    TSPReduction.encodeTSPSymPair TSPReduction.decodeTSPSymPair
    TSPReduction.decode_encodeTSPSymPair
    slackFieldsPrefix_computableInPolyTime
    slackOneSlotFields_computableInPolyTime

end CLRS.Chapter34.Turing.SubsetSumReduction
