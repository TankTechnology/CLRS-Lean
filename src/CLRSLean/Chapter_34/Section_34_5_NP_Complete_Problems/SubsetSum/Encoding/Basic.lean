import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Instance
import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.TravelingSalesperson.Encoding

/-!
# Raw finite syntax for SUBSET-SUM

SUBSET-SUM and decision-TSP share the same finite compact-number record
alphabet.  Reusing that already verified codec keeps the binary grammar and
its canonicality theorem single-sourced; the record interpretations remain
separate.
-/

namespace CLRS.Chapter34

/-- Shared finite compact-record alphabet, re-exported under the problem's
public name. -/
abbrev SubsetSumSym := TSPSym

/-- Proof-free indexed SUBSET-SUM data.  List positions distinguish equal
numerical values. -/
structure SubsetSumData where
  target : Nat
  values : List Nat
deriving DecidableEq, Repr

namespace SubsetSumData

/-- Sum the values at a list of selected indices.  Out-of-range indices use
zero, but accepted certificates separately prove the range condition. -/
def selectedSum (data : SubsetSumData) (indices : List Nat) : Nat :=
  (indices.map fun index => data.values.getD index 0).sum

/-- Honest indexed subset semantics. -/
def HasSubsetSum (data : SubsetSumData) : Prop :=
  ∃ indices : List Nat,
    indices.Nodup ∧
      (∀ index ∈ indices, index < data.values.length) ∧
      data.selectedSum indices = data.target

end SubsetSumData
end CLRS.Chapter34
