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

end CLRS.Chapter34.Turing.TSPReduction
