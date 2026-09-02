import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding
import CLRSLean.Chapter_34.Section_34_4_NP_Completeness_Proofs.PolyBuilder.StatefulFlatMap

/-! # Fixed formatting of the two TSP header fields -/

namespace CLRS.Chapter34.Turing.TSPReduction.HeaderFields

open PolyBuilder

inductive Mode
  | initial | rest
deriving DecidableEq, Fintype

def firstSpec : StatefulFlatMapSpec Mode Bool TSPSym where
  initial := .initial
  action
    | .initial, bit => ([.instanceMark, .numberMark, .bit bit], .rest)
    | .rest, bit => ([.bit bit], .rest)
  finish
    | .initial => [.instanceMark, .numberMark, .fieldEnd]
    | .rest => [.fieldEnd]

def secondSpec : StatefulFlatMapSpec Mode Bool TSPSym where
  initial := .initial
  action
    | .initial, bit => ([.numberMark, .bit bit], .rest)
    | .rest, bit => ([.bit bit], .rest)
  finish
    | .initial => [.numberMark, .fieldEnd]
    | .rest => [.fieldEnd]

def first (bits : List Bool) : List TSPSym :=
  rewriteStatefulFlatMap firstSpec bits

def second (bits : List Bool) : List TSPSym :=
  rewriteStatefulFlatMap secondSpec bits

private theorem first_from_rest (bits : List Bool) :
    rewriteStatefulFlatMapFrom firstSpec .rest bits =
      bits.map TSPSym.bit ++ [.fieldEnd] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [.bit bit] ++
        rewriteStatefulFlatMapFrom firstSpec .rest bits = _
      rw [ih]
      rfl

private theorem second_from_rest (bits : List Bool) :
    rewriteStatefulFlatMapFrom secondSpec .rest bits =
      bits.map TSPSym.bit ++ [.fieldEnd] := by
  induction bits with
  | nil => rfl
  | cons bit bits ih =>
      rw [rewriteStatefulFlatMapFrom]
      change [.bit bit] ++
        rewriteStatefulFlatMapFrom secondSpec .rest bits = _
      rw [ih]
      rfl

theorem first_eq (bits : List Bool) :
    first bits = .instanceMark :: .numberMark ::
      bits.map TSPSym.bit ++ [.fieldEnd] := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
      unfold first rewriteStatefulFlatMap
      rw [rewriteStatefulFlatMapFrom]
      change [.instanceMark, .numberMark, .bit bit] ++
        rewriteStatefulFlatMapFrom firstSpec .rest bits = _
      rw [first_from_rest]
      rfl

theorem second_eq (bits : List Bool) :
    second bits = .numberMark :: bits.map TSPSym.bit ++ [.fieldEnd] := by
  cases bits with
  | nil => rfl
  | cons bit bits =>
      unfold second rewriteStatefulFlatMap
      rw [rewriteStatefulFlatMapFrom]
      change [.numberMark, .bit bit] ++
        rewriteStatefulFlatMapFrom secondSpec .rest bits = _
      rw [second_from_rest]
      rfl

end CLRS.Chapter34.Turing.TSPReduction.HeaderFields
