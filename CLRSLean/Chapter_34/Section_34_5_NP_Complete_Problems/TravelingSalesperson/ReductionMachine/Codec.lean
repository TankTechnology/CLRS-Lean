import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.FixedPairSameInputConcat

/-! # Fixed pair code for the TSP alphabet -/

namespace CLRS.Chapter34.Turing.TSPReduction

open PolyBuilder

def encodeTSPSymPair : TSPSym → UnaryFrameSym × UnaryFrameSym
  | .instanceMark => (.tick, .tick)
  | .certificateMark => (.tick, .separator)
  | .numberMark => (.tick, .frameEnd)
  | .bit false => (.separator, .tick)
  | .bit true => (.separator, .separator)
  | .fieldEnd => (.separator, .frameEnd)
  | .recordEnd => (.frameEnd, .tick)

def decodeTSPSymPair : UnaryFrameSym → UnaryFrameSym → TSPSym
  | .tick, .tick => .instanceMark
  | .tick, .separator => .certificateMark
  | .tick, .frameEnd => .numberMark
  | .separator, .tick => .bit false
  | .separator, .separator => .bit true
  | .separator, .frameEnd => .fieldEnd
  | .frameEnd, .tick => .recordEnd
  | .frameEnd, .separator => .recordEnd
  | .frameEnd, .frameEnd => .recordEnd

@[simp] theorem decode_encodeTSPSymPair (symbol : TSPSym) :
    decodeTSPSymPair (encodeTSPSymPair symbol).1
      (encodeTSPSymPair symbol).2 = symbol := by
  cases symbol with
  | bit value => cases value <;> rfl
  | _ => rfl

/-- Extend the fixed code to option-separated TSP streams.  The eighth code
word is used for the physical pair separator. -/
def encodeOptionTSPSymPair : Option TSPSym → UnaryFrameSym × UnaryFrameSym
  | some symbol => encodeTSPSymPair symbol
  | none => (.frameEnd, .separator)

def decodeOptionTSPSymPair :
    UnaryFrameSym → UnaryFrameSym → Option TSPSym
  | .tick, .tick => some .instanceMark
  | .tick, .separator => some .certificateMark
  | .tick, .frameEnd => some .numberMark
  | .separator, .tick => some (.bit false)
  | .separator, .separator => some (.bit true)
  | .separator, .frameEnd => some .fieldEnd
  | .frameEnd, .tick => some .recordEnd
  | .frameEnd, .separator => none
  | .frameEnd, .frameEnd => none

@[simp] theorem decode_encodeOptionTSPSymPair (symbol : Option TSPSym) :
    decodeOptionTSPSymPair (encodeOptionTSPSymPair symbol).1
      (encodeOptionTSPSymPair symbol).2 = symbol := by
  cases symbol with
  | none => rfl
  | some symbol =>
      cases symbol with
      | bit value => cases value <;> rfl
      | _ => rfl

end CLRS.Chapter34.Turing.TSPReduction
