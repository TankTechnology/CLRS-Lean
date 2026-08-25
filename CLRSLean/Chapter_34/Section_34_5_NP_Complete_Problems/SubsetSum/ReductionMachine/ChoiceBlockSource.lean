import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.ReductionMachine.ChoiceDigitMergeCompiled
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.ListMap

/-!
# Choice blocks: canonical nested-loop source

The source places every verified choice digit before one shared block-position
stream.  The unique low-bit column also serves as the item-boundary trigger,
so a fixed nested loop expands equal-width blocks and preserves boundaries.
-/

noncomputable section

namespace CLRS.Chapter34.Turing.SubsetSumReduction

open PolyBuilder

inductive ChoiceBlockDigit
  | zero | one | two | three
deriving DecidableEq, Fintype, Repr

def ChoiceBlockDigit.toSmallDigit : ChoiceBlockDigit → SmallDigit
  | .zero => .zero
  | .one => .one
  | .two => .two
  | .three => .three

def choiceBlockDigitTag : SmallDigit → ChoiceBlockDigit
  | .zero | .four => .zero
  | .one => .one
  | .two => .two
  | .three => .three

inductive ChoiceBlockSourceSym
  | rowDigit (digit : ChoiceBlockDigit)
  | rowEnd
  | column (position : SmallDigitPosition)
deriving DecidableEq, Fintype, Repr

def choiceBlockRowTag : ChoiceCountSym → ChoiceBlockSourceSym
  | .digit digit => .rowDigit (choiceBlockDigitTag digit)
  | .itemEnd => .rowEnd

def choiceBlockRows (truth : Bool) (input : List CNFSym) :
    List ChoiceBlockSourceSym :=
  (choiceDigitStream (decodeCNF input) truth).map choiceBlockRowTag

def choiceBlockColumns (input : List CNFSym) : List ChoiceBlockSourceSym :=
  (smallDigitPositions (reductionBlockWidthTicks input)).map .column

def choiceBlockSource (truth : Bool) (input : List CNFSym) :
    List ChoiceBlockSourceSym :=
  choiceBlockRows truth input ++ choiceBlockColumns input

private def encodeChoiceBlockSourceSymPair :
    ChoiceBlockSourceSym → UnaryFrameSym × UnaryFrameSym
  | .rowDigit .zero => (.tick, .tick)
  | .rowDigit .one => (.tick, .separator)
  | .rowDigit .two => (.tick, .frameEnd)
  | .rowDigit .three => (.separator, .tick)
  | .rowEnd => (.separator, .separator)
  | .column .bit0 => (.separator, .frameEnd)
  | .column .bit1 => (.frameEnd, .tick)
  | .column .bit2 => (.frameEnd, .separator)
  | .column .padding => (.frameEnd, .frameEnd)

private def decodeChoiceBlockSourceSymPair
    : UnaryFrameSym → UnaryFrameSym → ChoiceBlockSourceSym
  | .tick, .tick => .rowDigit .zero
  | .tick, .separator => .rowDigit .one
  | .tick, .frameEnd => .rowDigit .two
  | .separator, .tick => .rowDigit .three
  | .separator, .separator => .rowEnd
  | .separator, .frameEnd => .column .bit0
  | .frameEnd, .tick => .column .bit1
  | .frameEnd, .separator => .column .bit2
  | .frameEnd, .frameEnd => .column .padding

@[simp] private theorem decode_encodeChoiceBlockSourceSymPair
    (symbol : ChoiceBlockSourceSym) :
    decodeChoiceBlockSourceSymPair
      (encodeChoiceBlockSourceSymPair symbol).1
      (encodeChoiceBlockSourceSymPair symbol).2 = symbol := by
  cases symbol with
  | rowDigit digit => cases digit <;> rfl
  | rowEnd => rfl
  | column position => cases position <;> rfl

private noncomputable def choiceBlockRows_computableInPolyTime
    (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id (choiceBlockRows truth) := by
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      (choiceDigitStream_computableInPolyTime truth)
      (listMap_computableInPolyTime choiceBlockRowTag)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (choiceDigitStream (decodeCNF input) truth).map choiceBlockRowTag)
  simpa [Function.comp_def] using Classical.choice composed

private noncomputable def choiceBlockColumns_computableInPolyTime :
    _root_.Turing.TM2ComputableInPolyTime id id choiceBlockColumns := by
  let positionsExists :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch
      reductionBlockWidthTicks_computableInPolyTime
      smallDigitPositions_computableInPolyTime
  let positions := Classical.choice positionsExists
  let composed :=
    _root_.Turing.TM2Comp.TM2ComputableInPolyTime.comp_scratch positions
      (listMap_computableInPolyTime ChoiceBlockSourceSym.column)
  change _root_.Turing.TM2ComputableInPolyTime id id
    (fun input =>
      (smallDigitPositions (reductionBlockWidthTicks input)).map
        ChoiceBlockSourceSym.column)
  simpa [Function.comp_def] using Classical.choice composed

/-- A fixed polynomial-time TM2 produces the shared nested-loop source from
the same raw CNF word. -/
noncomputable def choiceBlockSource_computableInPolyTime (truth : Bool) :
    _root_.Turing.TM2ComputableInPolyTime id id
      (choiceBlockSource truth) :=
  fixedPairSameInputConcat_computableInPolyTime
    encodeChoiceBlockSourceSymPair decodeChoiceBlockSourceSymPair
    decode_encodeChoiceBlockSourceSymPair
    (choiceBlockRows_computableInPolyTime truth)
    choiceBlockColumns_computableInPolyTime

end CLRS.Chapter34.Turing.SubsetSumReduction
