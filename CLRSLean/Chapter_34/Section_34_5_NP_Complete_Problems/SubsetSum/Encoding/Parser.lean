import CLRSLean.Chapter_34.Section_34_5_NP_Complete_Problems.SubsetSum.Encoding.Basic

/-! # Complete SUBSET-SUM instance and certificate parsers -/

namespace CLRS.Chapter34

/-- Canonical finite encoding of a target followed by indexed item values. -/
def encodeSubsetSumData (data : SubsetSumData) : List SubsetSumSym :=
  .instanceMark ::
    (encodeTSPFields (data.target :: data.values) ++ [.recordEnd])

/-- Decode one complete SUBSET-SUM instance word. -/
def decodeSubsetSumData : List SubsetSumSym → Option SubsetSumData
  | .instanceMark :: input =>
      match decodeTSPFields input with
      | some (target :: values) => some { target, values }
      | _ => none
  | _ => none

/-- Canonical certificate: a duplicate-free list of compact item indices. -/
def encodeSubsetSumCertificate (indices : List Nat) : List SubsetSumSym :=
  encodeTSPCertificate indices

/-- Decode one complete selected-index certificate. -/
def decodeSubsetSumCertificate : List SubsetSumSym → Option (List Nat) :=
  decodeTSPCertificate

end CLRS.Chapter34
